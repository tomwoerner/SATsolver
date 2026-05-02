#!/usr/bin/env python3
"""
FINAL run_all.py (fixed)

- Handles timeouts properly
- Logs to ONE summary.csv (newest rows after header)
- Adds timestamp, index, vars, clauses
- Supports --resume / --continue
- Cross-platform
"""

import sys
import time
import csv
import subprocess
from pathlib import Path
from datetime import datetime
import gzip

try:
    from unlzw3 import unlzw
    HAS_UNLZW = True
except:
    HAS_UNLZW = False


BASE = Path(__file__).resolve().parent.parent


def project_python():
    if sys.platform.startswith("win"):
        candidate = BASE / "venv" / "Scripts" / "python.exe"
    else:
        candidate = BASE / "venv" / "bin" / "python"

    if candidate.exists():
        return str(candidate)

    return sys.executable


def get_sat_timeout(sat1_path, default=10):
    with open(sat1_path, "r", encoding="utf-8") as f:
        for line in f:
            stripped = line.strip()
            if stripped.startswith("TIME_LIMIT"):
                try:
                    return int(stripped.split("=", 1)[1].strip())
                except ValueError:
                    break

    print(f"WARNING: TIME_LIMIT not found in {sat1_path}; using default {default}s")
    return default

def open_stream(path: Path):
    if path.suffix == ".cnf":
        return path.open("rt", encoding="utf-8", errors="replace")
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8", errors="replace")
    if path.suffix.lower() == ".z":
        if HAS_UNLZW:
            data = unlzw(path.read_bytes())
        else:
            proc = subprocess.run(
                [
                    project_python(),
                    "-c",
                    "import sys; from unlzw3 import unlzw; sys.stdout.buffer.write(unlzw(open(sys.argv[1], 'rb').read()))",
                    str(path),
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            if proc.returncode != 0:
                raise RuntimeError("pip install unlzw3")
            data = proc.stdout
        return data.decode("utf-8", errors="replace").splitlines()
    raise ValueError("Unsupported format")


def read_header(path):
    try:
        for line in open_stream(path):
            line = line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                parts = line.split()
                return int(parts[2]), int(parts[3])
    except:
        pass
    return "", ""


SUMMARY_HEADER = ["timestamp","index","file","vars","clauses","result","time_ms"]


def trim_trailing_empty_columns(row):
    row = list(row)
    while row and row[-1] == "":
        row.pop()
    return row


def normalize_summary_row(row):
    row = trim_trailing_empty_columns(row)

    if len(row) == 6:
        row = [row[0], "", row[1], row[2], row[3], row[4], row[5]]

    if len(row) < len(SUMMARY_HEADER):
        row = row + [""] * (len(SUMMARY_HEADER) - len(row))

    return row[:len(SUMMARY_HEADER)]


def read_summary_rows(csv_path):
    if not csv_path.exists():
        return []

    with open(csv_path, "r", newline="", encoding="utf-8") as f:
        rows = list(csv.reader(f))

    if not rows:
        return []

    header = trim_trailing_empty_columns(rows[0])
    data_rows = rows[1:] if header and header[0] == "timestamp" else rows

    return [normalize_summary_row(row) for row in data_rows if trim_trailing_empty_columns(row)]


def parse_index_value(index_value):
    if "/" not in index_value:
        return None

    current, total = index_value.split("/", 1)
    try:
        return int(current), int(total)
    except ValueError:
        return None


def get_resume_state(csv_path, total_files):
    rows = read_summary_rows(csv_path)
    completed_files = set()

    if not rows:
        return 1, completed_files

    top_index = parse_index_value(rows[0][1])
    if top_index is None:
        return 1, completed_files

    top_current, top_total = top_index
    if top_total != total_files:
        return 1, completed_files

    expected_index = top_current

    for row in rows:
        index_value = row[1]
        parsed_index = parse_index_value(index_value)

        if parsed_index is None:
            break

        current, total = parsed_index
        if total != total_files or current != expected_index:
            break

        completed_files.add(row[2])
        expected_index -= 1

    return min(top_current + 1, total_files + 1), completed_files


def write_summary_row(csv_path, row, retries=5, retry_delay=1.0):
    existing_rows = read_summary_rows(csv_path)
    temp_path = csv_path.with_name(csv_path.name + ".tmp")

    for attempt in range(retries + 1):
        try:
            with open(temp_path, "w", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                writer.writerow(SUMMARY_HEADER)
                writer.writerow(row)
                writer.writerows(existing_rows)
            temp_path.replace(csv_path)
            return True
        except PermissionError:
            try:
                if temp_path.exists():
                    temp_path.unlink()
            except OSError:
                pass

            if attempt == retries:
                print(
                    f"ERROR: Could not update {csv_path}. "
                    "Close the file if it is open in Excel or another program."
                )
                return False

            time.sleep(retry_delay)

    return False


def main():
    resume = False

    if len(sys.argv) not in (2, 3):
        print("Usage: python3 src/run_all.py benchmarks/ [--resume|--continue]")
        return

    bench_dir = Path(sys.argv[1])

    if len(sys.argv) == 3:
        if sys.argv[2] not in ("--resume", "--continue"):
            print("Usage: python3 src/run_all.py benchmarks/ [--resume|--continue]")
            return
        resume = True

    results_dir = BASE / "results"
    results_dir.mkdir(exist_ok=True)

    csv_path = results_dir / "summary.csv"

    files = sorted(
        list(bench_dir.glob("*.cnf")) +
        list(bench_dir.glob("*.cnf.gz")) +
        list(bench_dir.glob("*.cnf.Z"))
    )

    print(f"Found {len(files)} files")

    start_index = 1
    completed_files = set()
    if resume:
        start_index, completed_files = get_resume_state(csv_path, len(files))
        if start_index > len(files):
            print("Resume requested: all benchmarks already completed")
            print("DONE")
            return
        print(f"Resume requested: starting at {start_index}/{len(files)}")
        print(f"Resume requested: skipping {len(completed_files)} completed file(s)")

    for i, file in enumerate(files[start_index - 1:], start_index):
        if file.name in completed_files:
            print(f"[{i}/{len(files)}] {file.name} already completed, skipping", flush=True)
            continue

        print(f"[{i}/{len(files)}] {file.name}...", flush=True)

        vars_, clauses_ = read_header(file)

        start = time.time()

        sat1_path = BASE / "src" / "SAT1.py"
        sat_time_limit = get_sat_timeout(sat1_path)
        SAFETY_MARGIN = 5

        try:
            proc = subprocess.run(
                [project_python(), str(sat1_path), str(file)],
                stdout=subprocess.PIPE,
                stderr=None,
                universal_newlines=True,
                timeout=sat_time_limit + SAFETY_MARGIN
            )

            out = proc.stdout

            if "RESULT:SAT" in out:
                result = "SAT"
            elif "RESULT:UNSAT" in out:
                result = "UNSAT"
            elif "RESULT:TIMEOUT" in out:
                result = "TIMEOUT"
            else:
                result = "UNKNOWN"

        except subprocess.TimeoutExpired:
            result = "TIMEOUT"
            out = ""

        elapsed = (time.time() - start) * 1000

        wrote_summary = write_summary_row(csv_path, [
            datetime.now().isoformat(timespec="seconds"),
            f"{i}/{len(files)}",
            file.name,
            vars_,
            clauses_,
            result,
            f"{elapsed:.2f}"
        ])

        if not wrote_summary:
            print("Stopping so completed benchmark rows are not lost.")
            return

        print(f"   -> {result} ({elapsed:.1f} ms)")

    print("DONE")


if __name__ == "__main__":
    main()
