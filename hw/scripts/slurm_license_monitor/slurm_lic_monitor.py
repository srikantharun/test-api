#!/usr/bin/env python3

# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

"""
For documentation of SLURM license monitor script, refer to the following document:
docs/flow_docs/flows/slurm_lic_monitor.md
"""

from flask import Flask, Response
from prometheus_client import generate_latest, Gauge, CollectorRegistry
import subprocess
import re

app      = Flask(__name__)
registry = CollectorRegistry()

# Define metrics
licenses_total    = Gauge('slurm_licenses_total'   , 'Total number of SLURM licenses'   , ['license_name'], registry=registry)
licenses_used     = Gauge('slurm_licenses_used'    , 'Number of SLURM licenses used'    , ['license_name'], registry=registry)
licenses_free     = Gauge('slurm_licenses_free'    , 'Number of SLURM licenses free'    , ['license_name'], registry=registry)
licenses_reserved = Gauge('slurm_licenses_reserved', 'Number of SLURM licenses reserved', ['license_name'], registry=registry)

def set_license_metrics(metric, license_name, value):
    """Helper function to set metric values for a given license."""
    metric.labels(license_name=license_name).set(value)

def fetch_slurm_licenses():
    """
    Fetch SLURM license information using scontrol and update Prometheus metrics.
    """
    try:
        # fetch SLURM licenses
        output = subprocess.check_output(['scontrol', 'show', 'lic'], universal_newlines=True)
        license_info = re.findall(r'LicenseName=(\S+)\s+Total=(\d+)\s+Used=(\d+)\s+Free=(\d+)\s+Reserved=(\d+)', output)

        for license_name, total, used, free, reserved in license_info:
            set_license_metrics(licenses_total,    license_name, total)
            set_license_metrics(licenses_used,     license_name, used)
            set_license_metrics(licenses_free,     license_name, free)
            set_license_metrics(licenses_reserved, license_name, reserved)
    
    except Exception as e:
        print(f"Failed to fetch SLURM licenses: {e}")

@app.route('/metrics')
def metrics():
    """
    Endpoint for Prometheus to scrape.
    """
    fetch_slurm_licenses()  # Update metrics with the latest license info
    return Response(generate_latest(registry), mimetype="text/plain")

if __name__ == '__main__':
    flask_host = os.getenv('SLM_FLASK_HOST', '0.0.0.0')
    flask_port = int(os.getenv('SLM_FLASK_PORT', '8000'))
    app.run(host=flask_host, port=flask_port)
