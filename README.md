# SAT Solver (DPLL-Based with Heuristics)

This project implements a DIMACS CNF SAT solver using DPLL with Boolean Constraint Propagation (BCP), watched literals, a DLIS-style decision heuristic, and simple non-chronological backtracking/backjumping.

---

## Setup (One Command)

### Linux / Mac

```bash
unzip SATsolver-main.zip
cd SATsolver-main
chmod -R 777 .
./setup.sh
source venv/bin/activate
python3 src/run_all.py benchmarks/
python3 src/plot_results.py
```

### Windows (PowerShell)

```powershell
./setup.ps1
```

---

## Manual Setup

Create the virtual environment:

```bash
python3 -m venv venv
```

Activate it:

```bash
# Linux/Mac
source venv/bin/activate

# Windows PowerShell
venv\Scripts\activate
```

Install dependencies:

```bash
pip install -r requirements.txt
```

---

## Run Solver

Single benchmark file:

```bash
python3 src/SAT1.py benchmarks/file.cnf.Z
```

Run all benchmarks:

```bash
python3 src/run_all.py benchmarks/
```

Resume/continue an interrupted run:

```bash
python3 src/run_all.py benchmarks/ --resume
python3 src/run_all.py benchmarks/ --continue
```

---

## Experimental Mode / Heuristic Toggle Plumbing

`SAT1.py` and `run_all.py` now support an optional `--mode` argument for experiment tracking.

Supported modes:

- `full`
- `baseline`
- `no_dlis`
- `no_backjump`

Default mode is `full`, so the required clean solver command still works:

```bash
python3 src/SAT1.py benchmarks/file.cnf.Z
```

Explicit full-mode run:

```bash
python3 src/SAT1.py benchmarks/file.cnf.Z --mode full
```

Wrapper run with mode:

```bash
python3 src/run_all.py benchmarks/ --mode full
python3 src/run_all.py benchmarks/ --mode baseline
python3 src/run_all.py benchmarks/ --mode no_dlis
python3 src/run_all.py benchmarks/ --mode no_backjump
```

Resume a mode-specific benchmark run:

```bash
python3 src/run_all.py benchmarks/ --resume --mode full
python3 src/run_all.py benchmarks/ --resume --mode baseline
python3 src/run_all.py benchmarks/ --resume --mode no_dlis
python3 src/run_all.py benchmarks/ --resume --mode no_backjump
```

Run every supported mode sequentially:

```bash
python3 src/run_all.py benchmarks/ --mode all
python3 src/run_all.py benchmarks/ --resume --mode all
```

`--mode all` is only supported by `run_all.py`. It expands to `full`, `baseline`, `no_dlis`, and `no_backjump` sequentially. `SAT1.py` does not accept `--mode all` directly.

Important: the mode feature is currently infrastructure plumbing only. `SAT1.py` accepts the mode, builds an experiment config, and `run_all.py` records the mode in `results/summary.csv`. The solver behavior is currently unchanged across modes until manual control points are added inside the solver for disabling DLIS or backjumping.

---

## Testing the Mode Capability

Run a syntax check first:

```bash
python -m py_compile src/SAT1.py src/run_all.py src/plot_results.py
```

Test the default solver interface:

```bash
python3 src/SAT1.py benchmarks/file.cnf.Z
```

Expected output should be only solver output, for example:

```text
RESULT:SAT
ASSIGNMENT:1=1 2=0 3=1 ...
```

or:

```text
RESULT:UNSAT
```

Test explicit mode support:

```bash
python3 src/SAT1.py benchmarks/file.cnf.Z --mode full
python3 src/SAT1.py benchmarks/file.cnf.Z --mode baseline
python3 src/SAT1.py benchmarks/file.cnf.Z --mode no_dlis
python3 src/SAT1.py benchmarks/file.cnf.Z --mode no_backjump
```

Test wrapper mode support:

```bash
python3 src/run_all.py benchmarks/ --mode full
python3 src/run_all.py benchmarks/ --mode all
```

Expected wrapper output should include:

```text
Found <N> files
Mode: full
[1/<N>] ...
```

Test mode-aware resume:

```bash
python3 src/run_all.py benchmarks/ --resume --mode full
```

Expected wrapper output should include:

```text
Found <N> files
Mode: full
Resume requested: starting at <K>/<N>
Resume requested: skipping <K-1> completed file(s)
```

To verify that mode logging works, open:

```text
results/summary.csv
```

The header should be:

```csv
timestamp,index,file,vars,clauses,result,time_ms,mode
```

Old rows without a mode are treated as `full`. New rows include the selected mode in the final column.

---

## Plot Results

After running benchmarks, generate runtime plots:

```bash
python3 src/plot_results.py --mode full
python3 src/plot_results.py --mode all
```

Generated outputs are written under:

```text
results/
```

Typical outputs:

- `results/summary.csv`
- `results/sat_plot_full.png`
- `results/unsat_plot_full.png`
- `results/timeout_table_full.txt`
- `results/mode_summary.csv`

`plot_results.py` defaults to `--mode full`. Plots are generated per mode, so results from different modes are not mixed in the same SAT/UNSAT chart. Use `--mode all` to generate one SAT plot and one UNSAT plot per mode.

---

## Output Format

The solver prints one of the following formats to standard output.

For satisfiable formulas:

```text
RESULT:SAT
ASSIGNMENT:1=1 2=0 3=1 ...
```

For unsatisfiable formulas:

```text
RESULT:UNSAT
```

For internal timeout handling during benchmark runs:

```text
RESULT:TIMEOUT
```

---

## Summary CSV

Benchmark results go to:

```text
results/summary.csv
```

Columns:

- `timestamp`
- `index`
- `file`
- `vars`
- `clauses`
- `result`
- `time_ms`
- `mode`

Rows are inserted newest-first after the header.

---

## Supported Formats

- `.cnf`
- `.cnf.gz`
- `.cnf.Z`

No external decompression tools are required when the Python dependency is available.

---

## Notes

- Results folder is always relative to the project root.
- Works on Windows and Linux.
- `--mode` is for benchmark/report experiments and tracking. The default final solver command remains `python3 src/SAT1.py benchmark.cnf`.
