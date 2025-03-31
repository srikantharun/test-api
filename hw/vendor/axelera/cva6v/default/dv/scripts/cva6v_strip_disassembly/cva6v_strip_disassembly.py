import csv

def get_register_index(reg_name):
    reg_map = {
        'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4,
        't0': 5, 't1': 6, 't2': 7,
        's0': 8, 'fp': 8, 's1': 9,
        'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13,
        'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
        's2': 18, 's3': 19, 's4': 20, 's5': 21,
        's6': 22, 's7': 23, 's8': 24, 's9': 25,
        's10': 26, 's11': 27,
        't3': 28, 't4': 29, 't5': 30, 't6': 31
    }
    return reg_map.get(reg_name.lower(), -1)

def get_fpr_index(reg_name):
    reg_map = {
        'ft0': 0, 'ft1': 1, 'ft2': 2, 'ft3': 3, 'ft4': 4,
        'ft5': 5, 'ft6': 6, 'ft7': 7,
        'fs0': 8, 'fs1': 9,
        'fa0': 10, 'fa1': 11,
        'fa2': 12, 'fa3': 13, 'fa4': 14, 'fa5': 15,
        'fa6': 16, 'fa7': 17,
        'fs2': 18, 'fs3': 19, 'fs4': 20, 'fs5': 21,
        'fs6': 22, 'fs7': 23, 'fs8': 24, 'fs9': 25,
        'fs10': 26, 'fs11': 27,
        'ft8': 28, 'ft9': 29, 'ft10': 30, 'ft11': 31
    }
    return reg_map.get(reg_name.lower(), -1)

def expand_vector_data(reg_value):
    # Check if reg_value contains shorthand notation
    if '^' in reg_value:
        # Expected format: '0x0^<total_bits>-<data>'
        # Example: '0x0^960-<data>'
        try:
            prefix, rest = reg_value.split('^', 1)
            if prefix != '0x0':
                # Not in expected format
                return reg_value
            total_bits_str, data = rest.split('-', 1)
            total_bits = int(total_bits_str)
            data = data.strip()
            # Remove '0x' from data if present
            if data.startswith('0x'):
                data = data[2:]
            data_bits = len(data) * 4  # Each hex digit is 4 bits
            zeros_bits = total_bits - data_bits
            if zeros_bits < 0:
                # Data is longer than total_bits
                return reg_value
            zeros_hex_digits = zeros_bits // 4
            zeros = '0' * zeros_hex_digits
            full_data = '0x' + zeros + data
            return full_data
        except Exception as e:
            # Error in parsing, return reg_value unchanged
            return reg_value
    else:
        return reg_value

def get_aqrl_suffix(insn_hex):
    try:
        insn_int = int(insn_hex, 16)
        opcode = insn_int & 0x7F  # Bits [6:0]
        # AMO opcode is 0x2F (binary 0101111)
        if opcode != 0x2F:
            return ''  # Not an AMO instruction, no suffix needed
        aq_bit = (insn_int >> 26) & 1
        rl_bit = (insn_int >> 25) & 1
        suffix = ''
        if aq_bit and rl_bit:
            suffix = '.aqrl'
        elif aq_bit:
            suffix = '.aq'
        elif rl_bit:
            suffix = '.rl'
        return suffix
    except:
        return ''

def process_csv(input_file, output_file):
    line_count = 0
    order = 0
    with open(input_file, 'r') as csvfile, open(output_file, 'w') as outfile:
        reader = csv.DictReader(csvfile)

        # Write header line to the output file
        header_fields = [
            'valid', 'order', 'insn', 'trap', 'halt', 'intr', 'mode', 'ixl',
            'pc_rdata', 'pc_wdata', 'x_wb', 'x_wdata', 'f_wb', 'f_wdata',
            'v_wb', 'v_wdata', 'csr_wb', 'csr', 'lrsc_cancel', 'disass', 'inst_name'
        ]
        outfile.write(';'.join(header_fields) + '\n')

        for row in reader:
            # Initialize fields
            valid = '1'
            trap = '0'
            halt = '0'
            intr = '0'
            ixl = '0'
            lrsc_cancel = '0'

            # Extract fields from CSV
            binary = row.get('binary', '').strip()
            instr_str = row.get('instr_str', '').strip().strip('"')
            pc_rdata = row.get('pc', '').strip()
            mode = row.get('mode', '').strip()
            gpr = row.get('gpr', '').strip()
            csr_field = row.get('csr', '').strip()

            if not binary or not instr_str or not pc_rdata:
                continue

            # Process instr_str to get instruction and operands
            instr_parts = instr_str.split()
            if not instr_parts:
                continue
            instruction = instr_parts[0]
            operands = ' '.join(instr_parts[1:]).replace(' ,', ',').replace(', ', ',')  # Removing any extra spaces around commas

            # insn is binary
            insn = binary

            # Get aqrl suffix based on the binary instruction, only if it's an AMO instruction
            suffix = get_aqrl_suffix(insn)
            instruction_full = instruction
            if suffix:
                instruction_full += suffix

            # Construct disass including the binary at the beginning
            disass = f"{insn} {instruction_full} {operands}".strip()

            # Extract inst_name
            inst_name = instruction_full

            # Calculate pc_wdata
            # Instruction length: if binary is 8 hex digits, it's 32 bits (4 bytes), else 2 bytes
            if len(binary) == 8:
                instr_length = 4
            else:
                instr_length = 2
            pc_wdata_int = int(pc_rdata, 16) + instr_length
            pc_wdata = format(pc_wdata_int, '016x')

            # Initialize writeback variables
            x_wb = ''
            x_wdata = ''
            f_wb = ''
            f_wdata = ''
            v_wb = ''
            v_wdata = ''
            csr_wb = ''
            csr = '0'

            # x_wb, x_wdata, f_wb, f_wdata, v_wb, v_wdata from gpr
            if gpr:
                reg_name_value = gpr.strip().split(':')
                if len(reg_name_value) == 2:
                    reg_name = reg_name_value[0]
                    reg_value = reg_name_value[1]
                    if reg_name.startswith('v'):
                        # Vector register
                        reg_index = int(reg_name[1:])
                        if 0 <= reg_index <= 31:
                            v_wb = str(reg_index)
                            v_wdata = expand_vector_data(reg_value)
                    elif reg_name.startswith('f'):
                        # Floating point register
                        reg_index = get_fpr_index(reg_name)
                        if reg_index != -1:
                            f_wb = str(reg_index)
                            f_wdata = reg_value
                    else:
                        # GPR
                        reg_index = get_register_index(reg_name)
                        if reg_index != -1:
                            x_wb = str(reg_index)
                            x_wdata = reg_value

            # csr_wb and csr from csr_field
            if csr_field:
                csr_name_value = csr_field.strip().split(':')
                if len(csr_name_value) == 2:
                    csr_wb = csr_name_value[0]
                    csr = csr_name_value[1]

            # Write to output file in the specified format

            output_line = f"{valid};{order};{insn};{trap};{halt};{intr};{mode};{ixl};{pc_rdata};{pc_wdata};{x_wb};{x_wdata};{f_wb};{f_wdata};{v_wb};{v_wdata};{csr_wb};{csr};{lrsc_cancel};\"{disass}\";{inst_name}\n"
            outfile.write(output_line)

            # Increment order and line count
            order += 1
            line_count += 1
            if line_count % 1000000 == 0:
                print(f"Processed {line_count} lines")

    print(f"Finished processing {line_count} lines")

if __name__ == "__main__":
    input_csv = 'spike_rvvi.csv'   # Replace with your input CSV file
    output_log = 'inst_cov_dis.log'  # Replace with your desired output file
    process_csv(input_csv, output_log)
