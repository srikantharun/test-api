import re
import csv
import argparse
import sys

"""
Author: Abhilash Chadhar

This script takes a log file from imperas ISS as input and
processes it to generate an output CSV file compatible with the coverage collection setup

Usage:
    python cva6v_imperas_log_to_csv.py --log input_log_file.log --csv output_file.csv

Arguments:
    --log : The input log file.
    --csv : The output CSV file.
"""

def parse_log_line(line):
    match = re.match(r"Info 'iss/cpu0', (?P<pc>0x[0-9a-fA-F]+)\((?P<label>[^\)]+)\): Machine (?P<binary>[0-9a-fA-F]+) (?P<instr_str>.+)", line)
    if match:
        return match.groupdict()
    return None

def parse_gpr_line(line):
    match = re.match(r"Info\s+(?P<gpr>\w+)\s+[0-9a-fA-F]+\s+->\s+(?P<gpr_value>0x[0-9a-fA-F]+)", line)
    if match:
        return match.groupdict()
    return None

def process_log(input_file, output_file):
    output_columns = ["pc", "instr", "gpr", "csr", "binary", "mode", "instr_str", "operand", "pad"]
    output_data = []

    with open(input_file, "r") as file:
        lines = file.readlines()
        current_gpr = ""
        for line in lines:
            log_data = parse_log_line(line)
            if log_data:
                pc = log_data['pc'].replace('0x', '').zfill(16)  # Strip leading '0x' and zero-pad
                binary = log_data['binary']
                instr_str = log_data['instr_str'].strip()
                mode = '3'  # Assuming mode is 3 (machine mode in RISC-V)
                gpr = current_gpr
                csr = ""
                instr = ""
                operand = ""
                pad = ""

                output_data.append([pc, instr, gpr, csr, binary, mode, instr_str, operand, pad])
                current_gpr = ""  # Reset current_gpr after each instruction line
            else:
                gpr_data = parse_gpr_line(line)
                if gpr_data:
                    gpr_value = gpr_data['gpr_value'].replace('0x', '').zfill(16)
                    current_gpr = f'{gpr_data["gpr"]}:{gpr_value}'
                    if output_data:
                        output_data[-1][2] = current_gpr

    # Ensure correct CSV formatting and quoting
    with open(output_file, "w", newline='') as csvfile:
        writer = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL)
        writer.writerow(output_columns)
        writer.writerows(output_data)

def main():
    parser = argparse.ArgumentParser(description='Process a log file and output a CSV file. Author: Abhilash Chadhar')
    parser.add_argument('--log', type=str, required=True, help='The input log file.')
    parser.add_argument('--csv', type=str, required=True, help='The output CSV file.')
    args = parser.parse_args()

    process_log(args.log, args.csv)

if __name__ == "__main__":
    main()
