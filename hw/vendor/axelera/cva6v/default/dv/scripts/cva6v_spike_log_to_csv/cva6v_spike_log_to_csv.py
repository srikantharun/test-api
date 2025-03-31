import csv
import re
import argparse

# Mapping of register numbers to names
register_map = {
    'x0': 'zero', 'x1': 'ra', 'x2': 'sp', 'x3': 'gp', 'x4': 'tp',
    'x5': 't0', 'x6': 't1', 'x7': 't2', 'x8': 's0', 'x9': 's1',
    'x10': 'a0', 'x11': 'a1', 'x12': 'a2', 'x13': 'a3', 'x14': 'a4',
    'x15': 'a5', 'x16': 'a6', 'x17': 'a7', 'x18': 's2', 'x19': 's3',
    'x20': 's4', 'x21': 's5', 'x22': 's6', 'x23': 's7', 'x24': 's8',
    'x25': 's9', 'x26': 's10', 'x27': 's11', 'x28': 't3', 'x29': 't4',
    'x30': 't5', 'x31': 't6',
    'f0': 'ft0', 'f1': 'ft1', 'f2': 'ft2', 'f3': 'ft3', 'f4': 'ft4',
    'f5': 'ft5', 'f6': 'ft6', 'f7': 'ft7', 'f8': 'fs0', 'f9': 'fs1',
    'f10': 'fa0', 'f11': 'fa1', 'f12': 'fa2', 'f13': 'fa3', 'f14': 'fa4',
    'f15': 'fa5', 'f16': 'fa6', 'f17': 'fa7', 'f18': 'fs2', 'f19': 'fs3',
    'f20': 'fs4', 'f21': 'fs5', 'f22': 'fs6', 'f23': 'fs7', 'f24': 'fs8',
    'f25': 'fs9', 'f26': 'fs10', 'f27': 'fs11', 'f28': 'ft8', 'f29': 'ft9',
    'f30': 'ft10', 'f31': 'ft11'
}

def parse_spike_log(log_file):
    instructions = []

    with open(log_file, 'r') as file:
        lines = file.readlines()

    for i, line in enumerate(lines):
        match = re.match(r'core\s+\d+:\s+0x([0-9a-f]+)\s+\((0x[0-9a-f]+)\)\s+(\S+)\s+(.*)', line)
        if match:
            pc = match.group(1)
            binary = match.group(2)
            instr = match.group(3)
            instr_str = match.group(4)

            # Combine instruction name with the rest of the instruction string
            full_instr_str = f"{instr} {instr_str}"

            # Split operands
            operands = instr_str.split(',')
            operand = operands[0] if operands else ""

            # Match additional details for CSR, mem_addr, and mem_value
            csr_match = re.search(r'csr\s+([a-zA-Z0-9_]+)\s+(0x[0-9a-f]+)', line)
            csr = f"{csr_match.group(1)}:{csr_match.group(2)}" if csr_match else ""
            mem_match = re.search(r'mem\s+(0x[0-9a-f]+)\s+(0x[0-9a-f]+)', line)
            mem_addr = mem_match.group(1) if mem_match else ""
            mem_value = mem_match.group(2) if mem_match else ""

            # Check for GPR and FPR values in the next few lines
            gpr = ""
            for j in range(i+1, i+5):
                if j < len(lines):
                    gpr_match = re.match(r'core\s+\d+:\s+\d+\s+0x([0-9a-f]+)\s+\(0x[0-9a-f]+\)\s+(x|f)(\d+)\s+(0x[0-9a-f]+)', lines[j])
                    if gpr_match and gpr_match.group(1) == pc:
                        reg_num = f"{gpr_match.group(2)}{gpr_match.group(3)}"
                        reg_val = gpr_match.group(4)
                        reg_name = register_map.get(reg_num, reg_num)
                        gpr = f"{reg_name}:{reg_val}"
                        break

            print(f"Debug: PC={pc}, Instr={instr}, GPR={gpr}")

            # TODO: Detect the mode from log. Mode can be extracted from binary instruction 
            mode = "3"  # As per the provided CSV example

            # Append instruction details
            instructions.append([pc, instr, gpr, csr, binary, mode, full_instr_str, operand, mem_addr, mem_value, ""])

    return instructions

def write_to_csv(instructions, csv_file):
    with open(csv_file, 'w', newline='') as file:
        writer = csv.writer(file)
        writer.writerow(["pc", "instr", "gpr", "csr", "binary", "mode", "instr_str", "operand", "mem_addr", "mem_value", "pad"])
        writer.writerows(instructions)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert Spike log to CSV trace.")
    parser.add_argument('--log', type=str, required=True, help='Path to the Spike log file.')
    parser.add_argument('--csv', type=str, required=True, help='Path to the output CSV file.')
    args = parser.parse_args()

    instructions = parse_spike_log(args.log)
    write_to_csv(instructions, args.csv)
