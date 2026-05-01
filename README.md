# SAT Solver (DPLL-Based with Heuristics)

## Setup (One Command)

### Linux / Mac
bash setup.sh

### Windows (PowerShell)
./setup.ps1

---

## Manual Setup

python3 -m venv venv

Activate:
Linux/Mac: source venv/bin/activate
Windows: venv\Scripts\activate

Install:
pip install -r requirements.txt

---

## Run Solver

Single file:
python3 src/SAT1.py benchmarks/file.cnf.Z

Run ALL benchmarks:
python3 src/run_all.py benchmarks/

---

## Plot Results

After running benchmarks, you can generate a runtime plot:

```bash
python3 src/plot_results.py
```
---

## Output

All results go to:
results/summary.csv

Includes:
- timestamp
- filename
- number of variables
- number of clauses
- SAT/UNSAT
- runtime (ms)
- solver output

---

## Supported Formats

- .cnf
- .cnf.gz
- .cnf.Z

No external tools required.

---

## Notes

- Results folder is always relative to project root
- Works on Windows and Linux
