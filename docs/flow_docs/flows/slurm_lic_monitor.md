# SLURM License Token Monitoring

## Overview
This project includes scripts to monitor SLURM license usage and expose these metrics to Prometheus for visualization in Grafana. The implementation uses a Flask application with Prometheus client integration to periodically scrape SLURM license data and provide it for Prometheus scraping.

## Prerequisites
- Python 3.x
- SLURM
- Prometheus
- Grafana
- Access to a server with SLURM client installed

## Files
- `hw/scripts/slurm_license_monitor/slurm_lic_monitor.sh`: Shell script for setting up the environment, running the Flask application, and cleaning up afterward.
- `hw/scripts/slurm_license_monitor/slurm_lic_monitor.py`: Python script that defines the Flask application, collecting and exposing SLURM license metrics.

## Setup and Deployment

### Step 1: Clone the Repository
Download the scripts onto the server designated for running the monitoring. Validate that SLURM client tools are installed and functioning:

```bash
scontrol --version
```

### Step 2: Run the Shell Script
Execute the `slurm_lic_monitor.sh` script which automates the following tasks:
1. Environment Setup: Creates a Python virtual environment to avoid dependency conflicts.
2. Dependency Installation: Installs Flask and prometheus_client within the virtual environment.
3. Application Execution: Starts the Flask server to serve the metrics endpoint.
4. Cleanup: Deactivates and removes the virtual environment upon stopping the server.

```bash
./slurm_lic_monitor.sh
```

### Step 3: Configure Prometheus
Configure Prometheus to scrape metrics from the Flask application by adding the job configuration to the `prometheus.yml`:

```yaml
scrape_configs:
  - job_name: 'slurm_license_monitoring'
    static_configs:
      - targets: ['<flask_server_ip>:8000']
```
Replace `<flask_server_ip>` with the actual IP address where the Flask application is hosted.

### Step 4: Grafana Dashboard
Follow these steps to visualize SLURM license data:
1. Log into your Grafana dashboard.
2. Ensure Prometheus is set up as the data source.
3. Create a new dashboard with panels for each SLURM license metric.
4. Use Prometheus queries to display metrics, such as:
   - `slurm_licenses_total{license_name="desired_license"}`
   - `slurm_licenses_used{license_name="desired_license"}`
   - `slurm_licenses_free{license_name="desired_license"}`
   - `slurm_licenses_reserved{license_name="desired_license"}`

## Deployment Details
Deploy the monitoring service in a Linux Container (LXC) with a systemd service to manage its lifecycle:

```bash
[Unit]
Description=SLURM License Monitor
After=network.target

[Service]
User=root
Group=root
WorkingDirectory=/opt/slurm_lic_mon
ExecStart=/opt/slurm_lic_mon/slurm_lic_env/bin/python3 /opt/slurm_lic_mon/slurm_lic_monitor.py
Restart=always

[Install]
WantedBy=multi-user.target
```

Container ID: `htz1-slurm-lic-mon01`

## Implementation Details

### Python Flask Application
The `slurm_lic_monitor.py` script uses a Flask server to provide an endpoint for Prometheus scraping:
- The script defines SLURM license metrics using Prometheus Gauge type. Executes the `scontrol show lic` command to fetch current license data, parses it, and updates Prometheus gauges.
- The metric endpoint provides a `/metrics` route where Prometheus can scrape the latest data whenever it hits this endpoint.

### Troubleshooting
Ensure the SLURM commands are accessible to the user running the Flask application and that Prometheus is configured to scrape the correct endpoint.

## Monitoring
- The Grafana dashboard for monitoring can be accessed at: https://10.1.2.113:3000/d/c78e4919-68c8-4b8c-9ba3-582429d4622c/slurm-token-usage?orgId=1&from=now-2d&to=now

![SLURM Token Monitoring Dashboard](images/SLURM_token_monitor.jpg "SLURM Token Monitoring Dashboard")

This dashboard would be useful for administrators to monitor license usage and availability for each tool, compare usage between SLURM tokens and FlexLM licenses, and ensure that there are enough licenses for batch and interactive jobs. It also helps identify any discrepancies between the SLURM and FlexLM systems, which could be critical for maintaining and optimizing resource allocation. The following widgets help monitor usage metrics:

1. Gap - FlexLM vs SLURM(&lt;tool-name&gt;) \[Top Left Panel\]:
   - This widget shows the current difference or gap between licenses managed by FlexLM and SLURM. Ideally this should always be 0.

2. FlexLM vs. SLURM Gap(&lt;tool-name&gt;) \[Top Middle Panel\]:
   - This line graph compares the gap over time between FlexLM and SLURM. Peaks indicate times when the difference was greatest. Ideally the graph should be flat at 0.

3. FlexLM vs. SLURM License Usage Comparison(&lt;tool-name&gt;) \[Top Right Panel\]:
   - This line graph compares the license usage for FlexLM and SLURM over time. Ideally both the lines should overlap.

4. SLURM Token Utilisation (&lt;tool-name&gt; Batch) \[Middle Left Panel\]:
   - This bar graph shows the current batch token usage (total, free, used, or reserved) for SLURM.

5. SLURM Token Utilisation (&lt;tool-name&gt; Batch) \[Middle Middle Panel\]:
   - This stacked bar graph represents the percentage utilization of SLURM tokens over time for batch processes.

6. SLURM Token Utilisation (&lt;tool-name&gt; Batch) \[Middle Right Panel\]:
   - This line graph displays the utilization of tokens for batch sessions over time.

7. SLURM Token Utilisation (&lt;tool-name&gt; Interactive) \[Bottom Left Panel\]:
   - Similar to the middle left panel, this bar graph shows the total number of tokens dedicated to interactive sessions and their status.

8. SLURM Token Utilisation (&lt;tool-name&gt; Interactive) \[Bottom Middle Panel\]:
   - This is a stacked bar graph showing the percentage of SLURM tokens used over time for interactive sessions.

9. SLURM Token Utilisation (&lt;tool-name&gt; Interactive) \[Bottom Right Panel\]:
   - This line graph mirrors the middle right panel and shows the number of SLURM tokens available for interactive sessions.
