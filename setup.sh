#!/bin/bash
set -e

echo "Setting up virtual environment..."
python3 -m venv venv

echo "Installing dependencies..."
venv/bin/python -m pip install -r requirements.txt

echo "Setup complete!"
echo "You can now run:"
echo "  python3 src/run_all.py benchmarks/"
echo "  python3 src/plot_results.py"
