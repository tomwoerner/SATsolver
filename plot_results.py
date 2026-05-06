#!/usr/bin/env python3
"""
Plot SAT/UNSAT results from the latest batch for one experiment mode.

Modes are never mixed in a plot. Old summary rows without a mode are treated
as full-mode rows.
"""

import argparse
import csv
import os
import statistics
import subprocess
import sys
from pathlib import Path


BASE_DIR = Path(__file__).resolve().parent
SAT_MODES = ("full", "baseline", "no_dlis", "no_backjump")
PLOT_MODES = SAT_MODES + ("all",)
SUMMARY_HEADER = ["timestamp", "index", "file", "vars", "clauses", "result", "time_ms", "mode"]


def project_python():
    if sys.platform.startswith("win"):
        candidate = BASE_DIR / "venv" / "Scripts" / "python.exe"
    else:
        candidate = BASE_DIR / "venv" / "bin" / "python"

    if candidate.exists():
        return candidate

    return None


venv_python = project_python()
if venv_python is not None:
    current_python = Path(sys.executable).resolve()
    target_python = venv_python.resolve()
    if str(current_python).lower() != str(target_python).lower():
        raise SystemExit(
            subprocess.call([str(target_python), str(Path(__file__).resolve())] + sys.argv[1:])
        )

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


csv_file = BASE_DIR / "results" / "summary.csv"
out_dir = BASE_DIR / "results"
generated = []


def parse_args(argv):
    parser = argparse.ArgumentParser(description="Plot SAT benchmark results by mode")
    parser.add_argument("--mode", choices=PLOT_MODES, default="full")
    return parser.parse_args(argv)


def normalize_mode(row):
    mode = row.get("mode", "")
    mode = mode.strip() if mode is not None else ""
    return mode or "full"


def parse_summary_rows():
    rows = []
    with open(csv_file, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for file_order, r in enumerate(reader):
            try:
                idx = r["index"].strip()
                num_s, denom_s = idx.split("/", 1)
                num = int(num_s)
                denom = int(denom_s)
                rows.append({
                    "file": r["file"],
                    "timestamp": r["timestamp"],
                    "result": r["result"].strip().upper(),
                    "time": float(r["time_ms"]),
                    "num": num,
                    "denom": denom,
                    "mode": normalize_mode(r),
                    "file_order": file_order,
                })
            except Exception:
                continue
    return rows


def latest_batch_for_mode(rows, mode):
    mode_rows = [r for r in rows if r["mode"] == mode]
    if not mode_rows:
        return [], None, None

    actual_batch_size = mode_rows[0]["num"]
    planned_batch_size = mode_rows[0]["denom"]

    latest_by_num = {}
    for r in mode_rows:
        if 1 <= r["num"] <= actual_batch_size and r["num"] not in latest_by_num:
            latest_by_num[r["num"]] = r

    batch = [latest_by_num[n] for n in range(1, actual_batch_size + 1) if n in latest_by_num]
    batch = sorted(batch, key=lambda x: x["num"])
    return batch, actual_batch_size, planned_batch_size


def infer_timeout_ms(timeout_rows):
    if not timeout_rows:
        return None, None
    seconds = [r["time"] / 1000.0 for r in timeout_rows if r["time"] > 0]
    if not seconds:
        return None, None
    timeout_s = max(1, round(statistics.median(seconds)))
    return timeout_s * 1000, timeout_s


def build_log_ticks(times):
    ticks = [100, 1000, 10000]
    labels = ["100 ms", "1 s", "10 s"]

    max_time = max(times) if times else 0
    if max_time > max(ticks):
        top_s = max(1, round(max_time / 1000))
        top_ms = top_s * 1000
        if top_ms not in ticks:
            ticks.append(top_ms)
            labels.append(f"{top_s} s")

    combined = sorted(zip(ticks, labels), key=lambda x: x[0])
    return [x[0] for x in combined], [x[1] for x in combined]


def make_plot(data, title, mode, name, actual_batch_size, planned_batch_size):
    if not data:
        return

    data = sorted(data, key=lambda x: x["time"], reverse=True)

    names = [x["file"] for x in data]
    times = [x["time"] for x in data]
    timestamps = [x["timestamp"] for x in data]

    fig, ax = plt.subplots(figsize=(10, max(6, len(names) * 0.3)))
    y = list(range(len(names)))

    ax.barh(y, times)
    ax.set_yticks(y)
    ax.set_yticklabels(names)
    ax.set_ylim(len(y) - 0.5, -0.5)

    ax.set_title(
        f"{title} - {mode}\nLatest batch: {actual_batch_size}/{planned_batch_size} completed",
        fontsize=16,
        fontweight="bold",
        pad=2,
        linespacing=0.85,
    )
    ax.set_xlabel("Runtime")
    ax.set_xscale("log")

    ticks, labels = build_log_ticks(times)
    ax.set_xticks(ticks)
    ax.set_xticklabels(labels)
    ax.grid(True, axis="x", which="both")

    ax2 = ax.twinx()
    ax2.set_ylim(ax.get_ylim())
    ax2.set_yticks(y)
    ax2.set_yticklabels(timestamps)
    ax2.set_ylabel("Timestamp")

    plt.tight_layout(pad=0.4)

    out = out_dir / name
    plt.savefig(out, dpi=150)
    plt.close(fig)
    generated.append(out)


def write_timeout(data, mode, actual_batch_size, planned_batch_size, timeout_s):
    if not data:
        return

    out = out_dir / f"timeout_table_{mode}.txt"
    with open(out, "w", encoding="utf-8") as f:
        f.write(f"Mode: {mode}\n")
        f.write(f"Latest batch: {actual_batch_size}/{planned_batch_size} completed\n")
        if timeout_s is not None:
            f.write(f"Inferred timeout: {timeout_s} s\n")
        f.write("\n")
        for r in sorted(data, key=lambda x: x["num"]):
            index = f"{r['num']}/{r['denom']}"
            f.write(f"{index} {r['file']} {r['result']} {r['time']:.2f} ms {r['timestamp']}\n")

    generated.append(out)


def plot_mode(rows, mode):
    batch, actual_batch_size, planned_batch_size = latest_batch_for_mode(rows, mode)
    if not batch:
        print(f"No valid rows found for mode: {mode}")
        return None

    sat = [r for r in batch if r["result"] == "SAT"]
    unsat = [r for r in batch if r["result"] == "UNSAT"]
    timeout = [r for r in batch if r["result"] not in ("SAT", "UNSAT")]
    timeout_ms, timeout_s = infer_timeout_ms(timeout)

    make_plot(sat, "Boolean Satisfied", mode, f"sat_plot_{mode}.png", actual_batch_size, planned_batch_size)
    make_plot(unsat, "Boolean Unsatisfied", mode, f"unsat_plot_{mode}.png", actual_batch_size, planned_batch_size)
    write_timeout(timeout, mode, actual_batch_size, planned_batch_size, timeout_s)

    total_time = sum(r["time"] for r in batch)
    return {
        "mode": mode,
        "total_rows": len(batch),
        "sat_count": len(sat),
        "unsat_count": len(unsat),
        "timeout_count": len([r for r in batch if r["result"] == "TIMEOUT"]),
        "unknown_count": len([r for r in batch if r["result"] not in ("SAT", "UNSAT", "TIMEOUT")]),
        "total_time_ms": total_time,
        "avg_time_ms": total_time / len(batch) if batch else 0,
    }


def write_mode_summary(summaries):
    summaries = [s for s in summaries if s is not None]
    if not summaries:
        return

    out = out_dir / "mode_summary.csv"
    with open(out, "w", newline="", encoding="utf-8") as f:
        fieldnames = [
            "mode",
            "total_rows",
            "sat_count",
            "unsat_count",
            "timeout_count",
            "unknown_count",
            "total_time_ms",
            "avg_time_ms",
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for summary in summaries:
            row = dict(summary)
            row["total_time_ms"] = f"{row['total_time_ms']:.2f}"
            row["avg_time_ms"] = f"{row['avg_time_ms']:.2f}"
            writer.writerow(row)

    generated.append(out)


def main():
    args = parse_args(sys.argv[1:])
    rows = parse_summary_rows()
    if not rows:
        raise SystemExit(f"No valid rows found in {csv_file}")

    if args.mode == "all":
        modes_to_plot = SAT_MODES
    else:
        modes_to_plot = (args.mode,)

    summaries = [plot_mode(rows, mode) for mode in modes_to_plot]
    write_mode_summary(summaries)

    for f in generated:
        try:
            os.startfile(f)
        except Exception:
            pass

    print(f"DONE - plotted mode: {args.mode}")
    for f in generated:
        print(f)


if __name__ == "__main__":
    main()
