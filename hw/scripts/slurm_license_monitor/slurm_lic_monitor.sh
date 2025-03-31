#!/bin/bash

# create a virtual environment
python3 -m venv slurm_lic_env

# Activate the virtual environment
source slurm_lic_env/bin/activate

# install packages
pip install -r requirements.txt

# call python script to scrape data from SLURM
python3 slurm_lic_monitor.py

# Deactivate and remove the virtual environment
deactivate
rm -rf slurm_lic_env
