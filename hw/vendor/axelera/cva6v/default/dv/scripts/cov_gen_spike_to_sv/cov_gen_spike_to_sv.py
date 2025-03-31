import csv
import sys
import os

# Maps register names to their indices
def get_register_index(register_name):
    register_map = {
        "zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, 
        "s0": 8, "s1": 9, "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15,
        "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21, "s6": 22, "s7": 23,
        "s8": 24, "s9": 25, "s10": 26, "s11": 27, "t3": 28, "t4": 29, "t5": 30, "t6": 31
    }
    return register_map.get(register_name, None)

def sanitize_instruction_string(instr_str):
    return ' '.join(instr_str.split()).strip()

def parse_instruction_name(instr_str):
    return instr_str.split()[0]

def generate_sv_code(csv_filename, sv_filename):
    if os.path.exists(sv_filename):
        print(f"Output file {sv_filename} already exists. Overwriting.")
    else:
        print(f"Creating a new output file: {sv_filename}.")

    with open(csv_filename, mode='r') as csvfile, open(sv_filename, 'w') as svfile:
        csvreader = csv.DictReader(csvfile)
        
        for row in csvreader:
            pc = row['pc']
            instr_binary = row['binary']
            mode = row['mode']
            instr_str = sanitize_instruction_string(row['instr_str'].strip('"'))
            inst_name = parse_instruction_name(instr_str)
            gpr = row['gpr'].split(':')
            register_name = gpr[0] if len(gpr) > 1 else None
            register_index = get_register_index(register_name)
            register_value = gpr[1] if len(gpr) > 1 else None
            
            disass_with_binary = f"{instr_binary}, {instr_str}"
            
            svfile.write(f"// Instruction at PC: 0x{pc}, Binary: 0x{instr_binary}, Mode: {mode}, Instruction String: {instr_str}, Instruction: {inst_name}\n")
            svfile.write("rvviData = new();\n")
            svfile.write("rvviData.valid = 1'b1;\n")
            svfile.write(f"rvviData.insn = 32'h{instr_binary};\n")
            svfile.write(f"rvviData.mode = 2'b{int(mode):02b};\n")
            svfile.write(f"rvviData.pc_rdata = 32'h{pc};\n")
            svfile.write(f"rvviData.inst_name = \"{inst_name}\";\n")
            svfile.write(f"rvviData.disass = \"{disass_with_binary}\";\n")
            if register_index is not None and register_value is not None:
                svfile.write(f"rvviData.x_wdata[{register_index}] = 'h{register_value};\n")
                svfile.write(f"rvviData.x_wb[{register_index}] = 1'b1;\n")
            svfile.write("rvviData.trap = 1'b0;\n")
            svfile.write("rvviData.halt = 1'b0;\n")
            svfile.write("rvviData.intr = 1'b0;\n")
            svfile.write("traceDataQ[hart][issue].push_front(rvviData);\n")
            svfile.write("rvviData.display();\n")
            svfile.write("rv32i_sample(hart, issue, traceDataQ);\n")
            svfile.write("traceDataQ[hart][issue].pop_back();\n\n")

if __name__ == "__main__":
    sim_spike = os.getenv("SIM_SPIKE")
    if sim_spike is None:
        print("Error: SIM_SPIKE environment variable not set.")
        print("Please run 'setup_spike_env.sh' from the sim-spike directory.")
        sys.exit(1)

    csv_filename = sys.argv[1] if len(sys.argv) > 1 else None
    sv_filename = f"{sim_spike}/generated_rvvi_data.svh"  # Default SV file path using SIM_SPIKE

    if csv_filename is None:
        print("Usage: python script.py <CSV file>")
        sys.exit(1)

    os.makedirs(os.path.dirname(sv_filename), exist_ok=True)
    generate_sv_code(csv_filename, sv_filename)
