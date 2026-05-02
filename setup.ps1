Write-Host "Setting up virtual environment..."
python -m venv venv

Write-Host "Installing dependencies..."
.\venv\Scripts\python.exe -m pip install -r requirements.txt

Write-Host "Setup complete!"
Write-Host "You can now run:"
Write-Host "  python src/run_all.py benchmarks/"
Write-Host "  python src/plot_results.py"
