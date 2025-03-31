#!/usr/bin/env python3

import sys
import subprocess as sp
import argparse
import re
import glob
import logging
from pathlib import Path
import pandas as pd
import time
import csv
from dataclasses import dataclass
from typing import Tuple, Optional

# Define a dataclass to hold configuration values
@dataclass
class Config:
    block: str = "aic_did"
    netlist: Optional[str] = None
    spef_condition: str = "rcworst_125c"
    threshold: int = 2
    dft: bool = False
    dry_run: bool = False
    verbose: bool = False
    corner_condition: str = "tt_nominal_0p8500v_0p8500v_125c"

# Define a dataclass to hold paths
@dataclass
class Paths:
    script_dir: Path = Path(__file__).resolve().parent
    blocks_dir: Path = script_dir.parents[1] / "impl" / "europa" / "blocks"
    log_file: Path = script_dir / "ungated_flops.log"
    csv_file: Path = script_dir.parents[2] / "tests_results.csv"

# Initialize configuration and paths
config = Config()
paths = Paths()


def get_netlist(directory: str, block: str, netlist_arg: Optional[str] = None) -> Tuple[Optional[str], Optional[str]]:
    """Find the latest netlist file or use the specified one."""
    if netlist_arg and Path(netlist_arg).is_file():
        file_date = time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(Path(netlist_arg).stat().st_mtime))
        return netlist_arg, file_date

    pattern = f"{block}_p.mapped.v.gz"
    directory_path = Path(directory)

    latest_file = max(
        (file for file in directory_path.rglob(pattern)),
        key=lambda f: f.stat().st_mtime,
        default=None,
    )

    if latest_file:
        latest_mtime = latest_file.stat().st_mtime
        return str(latest_file), time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(latest_mtime))

    return None, None

def parse_report(report_file: str) -> Tuple[int, int, dict]:
    """Parse the report file for ungated flip-flops."""
    with open(report_file, 'r') as file:
#        report_lines = file.readlines()

        in_ungated_section = False
        all_flops = []
        gated_flops = 0
        ungated_flops = 0

        main_register_pattern = re.compile(r'^\s*clock_gate_.*')
        flop_pattern = r">\s+([^\s]+)\s+[\d\.]+\s+[\d\.]+%"

        for line in file:
            if main_register_pattern.match(line):
                gated_flops += 1
                in_ungated_section = True
                continue

            if "**Ungated**" in line:
                in_ungated_section = True
                continue

            if in_ungated_section:
                match = re.search(flop_pattern, line)
                if match:
                    flop_path = match.groups()[0]
                    ungated_flops += 1
                    subregister_pattern = r"([^\s]+)\[\d+\]$|([^\s]+)_\d+_$"
                    sub_match = re.search(subregister_pattern, flop_path)
                    flop_name = sub_match.group(1) if sub_match else flop_path
                    all_flops.append(flop_name)

    unique_flops = {flop: all_flops.count(flop) for flop in all_flops}
    filtered_flops = {flop: count for flop, count in unique_flops.items() if count >= config.threshold}

    return gated_flops, ungated_flops, filtered_flops

def main() -> int:
    # Parse command-line arguments
    parser = argparse.ArgumentParser(description='Report ungated flip-flops after synthesis.')
    parser.add_argument('-v', '--verbose', action='store_true', default=False, help="Enable verbose output")
    parser.add_argument('-b', '--block', type=str, default=config.block, help="Specify the block name to be analyzed or synthesized.")
    parser.add_argument('-n', '--netlist', type=str, help="Specify the location of the netlist")
    parser.add_argument('-d', '--dry_run', action='store_true', default=False, help="Dry run mode: commands will not be executed")
    parser.add_argument('-t', '--threshold', type=int, default=config.threshold, help="Threshold for reporting vectors wider than this value")
    parser.add_argument('--dft', action='store_true', default=False, help="Run with Design for Test (DFT) enabled")

    args = parser.parse_args()

    # Update config with command-line arguments
    config.block = args.block
    config.netlist = args.netlist
    config.threshold = args.threshold
    config.dft = args.dft
    config.dry_run = args.dry_run
    config.verbose = args.verbose

    # Set up logging
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
        handlers=[
            logging.FileHandler(paths.log_file),
            logging.StreamHandler()
        ]
    )
    logger = logging.getLogger()

    # Get netlist
    directory = f"/data/europa/pd/{config.block}_p/block_build"
    latest_file, file_date = get_netlist(directory, config.block, config.netlist)
    if latest_file:
        logger.info(f"Final netlist being used: {latest_file}")
        logger.info(f"Netlist date: {file_date}")
        config.netlist = latest_file
    else:
        logger.error("No suitable netlist found.")
        return 1

    # Construct and execute the shell command for generating reports
    pt_args = f"-x \"set BLOCK \\\"{config.block}\\\"; set NETLIST \\\"{config.netlist}\\\"; set DFT {int(config.dft)}; source \\\"{paths.script_dir}/pt_clock_savings_rep.tcl\\\"\""
    command = f"pt_shell {pt_args}"
    logger.info(f"Running command: {command}")
    sp.run(command, shell=True)

    # Locate the report files generated by PrimeTime
    report_files = glob.glob(f"{paths.blocks_dir}/{config.block}/pt_reports/clock_gate_savings.all.*.rpt")
    if not report_files:
        logger.error("No report files found in %s", f"{paths.blocks_dir}/{config.block}/pt_reports/")
        return 1

    for report_file in report_files:
        try:
            gated_flops, ungated_flops, filtered_flops = parse_report(report_file)
        except Exception as e:
            logger.error(f"Unable to open {report_file}, skipping. Error: {e}")
            continue

        # Extract BLOCK identifier from the filename
        block_identifier = report_file.split('savings.all.')[1].split('.rpt')[0]

        # Prepare the report content
        report_content = [f"Ungated flip-flops (threshold: {config.threshold}):\n"]
        report_content.extend([f" - {flop}: {count} bits\n" for flop, count in filtered_flops.items()])

        # Log the report content
        logger.info(''.join(report_content))

        # Write the report to a file
        result_filename = f"{paths.blocks_dir}/{config.block}/pt_reports/ungated_flops.{block_identifier}.rpt"
        logger.info(f"Writing report to {result_filename}")
        with open(result_filename, 'w') as result_file:
            result_file.writelines(report_content)

        # Summary calculations
        total_flops = gated_flops + ungated_flops
        percentage_ungated = (ungated_flops / total_flops * 100) if total_flops else 0

        # Log summary data
        table_data = [
            ["Block", block_identifier],
            ["Total Flops", total_flops],
            ["Ungated Flops", ungated_flops],
            ["Percentage Ungated", f"{percentage_ungated:.2f}%"],
        ]
        df = pd.DataFrame(table_data, columns=["Parameter", "Value"])

        # Print formatted table
        table_str = "\n"
        table_str += "+--------------------+-----------+\n"
        table_str += "| {:<18} | {:<9} |\n".format("Parameter", "Value")
        table_str += "+--------------------+-----------+\n"

        for row in table_data:
            table_str += "| {:<18} | {:<9} |\n".format(row[0], row[1])
            table_str += "+--------------------+-----------+\n"

        logger.info(f"\n{table_str}")  # Log the table


        # Write summary to CSV
        with open(paths.csv_file, mode='w', newline='') as file:
            writer = csv.writer(file)
            writer.writerow(["Block", "Total Flops", "Ungated Flops", "Percentage Ungated"])
            writer.writerow([block_identifier, total_flops, ungated_flops, f"{percentage_ungated:.2f}%"])
        logger.info(f"Summary written to {paths.csv_file}")

    return 0

if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
