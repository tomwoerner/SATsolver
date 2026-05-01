import csv
import matplotlib.pyplot as plt
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent.parent
csv_file = BASE_DIR / "results" / "summary.csv"

files = []
times = []

with open(csv_file) as f:
    reader = csv.DictReader(f)
    for row in reader:
        files.append(row["file"])
        times.append(float(row["time_ms"]))

plt.figure()
plt.plot(times)
plt.xlabel("Benchmark Index")
plt.ylabel("Time (ms)")
plt.title("SAT Solver Runtime per Benchmark")
plt.grid()

plt.savefig("../results/runtime_plot.png")
plt.show()
