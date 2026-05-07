# SAT Solver

This project contains a DIMACS CNF SAT solver and optional benchmark/report tooling.

## Final Layout

```text
mySAT.py
run_all.py
plot_results.py
requirements.txt
benchmarks/
results/
README.md
```

## Dependencies

Install Python dependencies from the project root:

```bash
python3 -m pip install -r requirements.txt
```

`.cnf` and `.cnf.gz` files work with the Python standard library. `.cnf.Z` files work with either the Python package `unlzw3` or a system decompression tool such as `uncompress` or `gunzip`.

On Windows, the simplest `.cnf.Z` option is:

```powershell
python -m pip install unlzw3
```

On Linux/Purdue systems, `uncompress` or `gunzip` may already be available.

Optional virtual environment:

```bash
python3 -m venv venv
source venv/bin/activate
python3 -m pip install -r requirements.txt
```

On Windows PowerShell:

```powershell
python -m venv venv
venv\Scripts\activate
python -m pip install -r requirements.txt
```

Optional setup scripts are also included:

```bash
./setup.sh
source venv/bin/activate
```

```powershell
.\setup.ps1
venv\Scripts\activate
```

The setup scripts create `venv` and install `requirements.txt`. Activate the virtual environment before running commands that need installed packages.

## Final Grading Command

Run the solver from the project root:

```bash
python3 mySAT.py benchmark.cnf
```

Examples:

```bash
python3 mySAT.py benchmarks/example.cnf
python3 mySAT.py benchmarks/example.cnf.gz
python3 mySAT.py benchmarks/example.cnf.Z
```

`mySAT.py` prints only required solver output to stdout:

```text
RESULT:SAT
ASSIGNMENT:1=1 2=0 3=1 ...
```

or:

```text
RESULT:UNSAT
```

For internal benchmark timeout handling, it may print:

```text
RESULT:TIMEOUT
```

Usage messages, errors, and optional spinner output go to stderr.

## Experiment Modes

`mySAT.py` accepts optional experiment modes:

```bash
python3 mySAT.py benchmark.cnf --mode full
python3 mySAT.py benchmark.cnf --mode baseline
python3 mySAT.py benchmark.cnf --mode no_dlis
python3 mySAT.py benchmark.cnf --mode no_backjump
```


## Experiment Modes

Default mode is `full`. 
`mySAT.py` accepts optional experiment modes for internal testing:

```bash
python3 mySAT.py benchmark.cnf --mode full
python3 mySAT.py benchmark.cnf --mode baseline
python3 mySAT.py benchmark.cnf --mode no_dlis
python3 mySAT.py benchmark.cnf --mode no_backjump

## Benchmark Wrapper

Run all benchmarks:

```bash
python3 run_all.py benchmarks/
```

Resume a benchmark run:

```bash
python3 run_all.py benchmarks/ --resume
```

Run one mode:

```bash
python3 run_all.py benchmarks/ --mode full
python3 run_all.py benchmarks/ --mode baseline
python3 run_all.py benchmarks/ --mode no_dlis
python3 run_all.py benchmarks/ --mode no_backjump
```

Run or resume all modes sequentially:

```bash
python3 run_all.py benchmarks/ --mode all
python3 run_all.py benchmarks/ --resume --mode all
```

Benchmark results are written newest-first to:

```text
results/summary.csv
```

The summary includes a `mode` column. Resume is mode-aware.

## Plot Results

Plot one mode:

```bash
python3 plot_results.py --mode full
```

Plot all modes separately:

```bash
python3 plot_results.py --mode all
```

Plots and tables are written to `results/`, using mode-specific filenames such as:

```text
sat_plot_full.png
unsat_plot_full.png
timeout_table_full.txt
mode_summary.csv
```

## Supported Input Formats

- `.cnf`
- `.cnf.gz`
- `.cnf.Z`

## Validation

Syntax check:

```bash
python -m py_compile mySAT.py run_all.py plot_results.py
```
