#!/usr/bin/env python3
"""
Plot SAT/UNSAT results from the most recent in-progress or completed batch.

Important behavior:
- The denominator in index (e.g. 241 in 110/241) is only the planned batch size.
- The ACTUAL current batch size is the numerator on the newest/first valid row.
  Example: if the newest row is 110/241, only numerators 1..110 are plotted.
- For each numerator, only the newest result is kept. This prevents older appended
  results from a previous run from being plotted with the current run.
"""

import csv
import os
import statistics
import subprocess
import sys
from pathlib import Path


BASE_DIR = Path(__file__).resolve().parent.parent


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


rows = []
with open(csv_file, newline="", encoding="utf-8") as f:
    reader = csv.DictReader(f)
    for file_order, r in enumerate(reader):
        try:
            idx = r["index"].strip()       # e.g. 110/241
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
                "file_order": file_order,
            })
        except Exception:
            continue

if not rows:
    raise SystemExit(f"No valid rows found in {csv_file}")

# The file is written newest-first in your current workflow. The first valid row
# tells us how far the current/latest run got before plot_results.py was called.
actual_batch_size = rows[0]["num"]
planned_batch_size = rows[0]["denom"]

# Keep only nums that belong to the latest partial batch, then keep the newest
# row per numerator. Because the CSV is newest-first, the first time a numerator
# is seen is the newest result for that numerator.
latest_by_num = {}
for r in rows:
    if 1 <= r["num"] <= actual_batch_size and r["num"] not in latest_by_num:
        latest_by_num[r["num"]] = r

batch = [latest_by_num[n] for n in range(1, actual_batch_size + 1) if n in latest_by_num]
batch = sorted(batch, key=lambda x: x["num"])

sat = [r for r in batch if r["result"] == "SAT"]
unsat = [r for r in batch if r["result"] == "UNSAT"]
timeout = [r for r in batch if r["result"] not in ("SAT", "UNSAT")]

generated = []


def infer_timeout_ms(timeout_rows):
    """Infer timeout from TIMEOUT/UNKNOWN rows and round to nearest second."""
    if not timeout_rows:
        return None, None
    seconds = [r["time"] / 1000.0 for r in timeout_rows if r["time"] > 0]
    if not seconds:
        return None, None
    timeout_s = max(1, round(statistics.median(seconds)))
    return timeout_s * 1000, timeout_s


timeout_ms, timeout_s = infer_timeout_ms(timeout)


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


def make_plot(data, title, name):
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
        f"{title}\nLatest batch: {actual_batch_size}/{planned_batch_size} completed",
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

    #if timeout_ms is not None:
    #    ax.axvline(timeout_ms, linestyle="--", linewidth=1)

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


def write_timeout(data):
    if not data:
        return
    out = out_dir / "timeout_table.txt"
    with open(out, "w", encoding="utf-8") as f:
        f.write(f"Latest batch: {actual_batch_size}/{planned_batch_size} completed\n")
        if timeout_s is not None:
            f.write(f"Inferred timeout: {timeout_s} s\n")
        f.write("\n")
        for r in sorted(data, key=lambda x: x["num"]):
            f.write(f"{r['index'] if 'index' in r else str(r['num']) + '/' + str(r['denom'])} {r['file']} {r['result']} {r['time']:.2f} ms {r['timestamp']}\n")
    generated.append(out)


make_plot(sat, "Boolean Satisfied", "sat_plot.png")
make_plot(unsat, "Boolean Unsatisfied", "unsat_plot.png")
write_timeout(timeout)

for f in generated:
    try:
        os.startfile(f)  # Windows convenience; ignored elsewhere
    except Exception:
        pass

print(f"DONE - plotted latest batch: {actual_batch_size}/{planned_batch_size}")
for f in generated:
    print(f)
