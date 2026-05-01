#!/usr/bin/env python3
"""
FINAL run_all.py (fixed)

- Handles timeouts properly
- Logs to ONE summary.csv (append)
- Adds timestamp, vars, clauses
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


def open_stream(path: Path):
    if path.suffix == ".cnf":
        return path.open("rt", encoding="utf-8", errors="replace")
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8", errors="replace")
    if path.suffix.lower() == ".z":
        if not HAS_UNLZW:
            raise RuntimeError("pip install unlzw3")
        data = unlzw(path.read_bytes())
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


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 src/run_all.py benchmarks/")
        return

    bench_dir = Path(sys.argv[1])
    BASE = Path(__file__).resolve().parent.parent
    results_dir = BASE / "results"
    results_dir.mkdir(exist_ok=True)

    csv_path = results_dir / "summary.csv"

    files = sorted(
        list(bench_dir.glob("*.cnf")) +
        list(bench_dir.glob("*.cnf.gz")) +
        list(bench_dir.glob("*.cnf.Z"))
    )

    print(f"Found {len(files)} files")

    write_header = not csv_path.exists()

    with open(csv_path, "a", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)

        if write_header:
            writer.writerow(["timestamp","file","vars","clauses","result","time_ms"])

        for i, file in enumerate(files, 1):
            print(f"[{i}/{len(files)}] {file.name}...", flush=True)

            vars_, clauses_ = read_header(file)

            start = time.time()

            try:
                proc = subprocess.run(
                    [sys.executable, str(BASE / "src" / "SAT1.py"), str(file)],
                    capture_output=True,
                    text=True,
                    timeout=15
                )
                out = proc.stdout
                if "RESULT:SAT" in out:
                    result = "SAT"
                elif "RESULT:UNSAT" in out:
                    result = "UNSAT"
                else:
                    result = "UNKNOWN"

            except subprocess.TimeoutExpired:
                result = "TIMEOUT"
                out = ""

            elapsed = (time.time() - start) * 1000

            writer.writerow([
                datetime.now().isoformat(timespec="seconds"),
                file.name,
                vars_,
                clauses_,
                result,
                f"{elapsed:.2f}"
            ])

            f.flush()

            print(f"   -> {result} ({elapsed:.1f} ms)")

    print("DONE")


if __name__ == "__main__":
    main()
