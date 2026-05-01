Write-Host "Setting up virtual environment..."
python -m venv venv

Write-Host "Activating environment..."
.\venv\Scripts\Activate

Write-Host "Installing dependencies..."
pip install -r requirements.txt

Write-Host "Setup complete!"
