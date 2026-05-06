#!/bin/bash
set -e

echo "Setting up virtual environment..."
python3 -m venv venv

echo "Installing dependencies..."
venv/bin/python -m pip install -r requirements.txt

echo "Setup complete!"
echo "Activate the virtual environment before running commands:"
echo "  source venv/bin/activate"
echo ""
echo "Then run:"
echo "  python3 mySAT.py benchmarks/example.cnf"
echo "  python3 run_all.py benchmarks/"
echo "  python3 plot_results.py --mode full"
