"""
Copyright 2019 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Convert spike sim log to standard riscv instruction trace format
"""

import argparse
import os
import re
import sys
import logging

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

#from dv.scripts.lib import *
from dv.instr_trace_compare import *
from riscv_trace_csv import *
from lib import *

RD_RE = re.compile(r"(core\s+\d+:\s+)?(?P<pri>\d) 0x(?P<addr>[a-f0-9]+?) " \
                   "\((?P<bin>.*?)\)(( c\S* 0x[a-f0-9]+)*) (?P<reg>[xf]\s*\d*?)\s*0x(?P<val>[a-f0-9]+)")

CORE_RE = re.compile(
    r"core\s+\d+:\s+0x(?P<addr>[a-f0-9]+?) \(0x(?P<bin>.*?)\) (?P<instr>.*?)$")
ADDR_RE = re.compile(
    r"(?P<rd>[a-z0-9]+?),(?P<imm>[\-0-9]+?)\((?P<rs1>[a-z0-9]+)\)")
ILLE_RE = re.compile(r"trap_illegal_instruction")

LOGGER = logging.getLogger()

VL_MAX = 4096
VD_MAX = 32

# Initialize the vector registers
vector_registers = {f"v{i}": "invalid_value" for i in range(32)}

# Declare and initialize all RISC-V GPRs with default value 0
gpr_registers = {
  "zero": 0, "x0": 0, "ra": 0, "sp": 0, "gp": 0, "tp": 0,
  "t0": 0, "t1": 0, "t2": 0, "s0": 0, "s1": 0,
  "a0": 0, "a1": 0, "a2": 0, "a3": 0, "a4": 0, "a5": 0, "a6": 0, "a7": 0,
  "s2": 0, "s3": 0, "s4": 0, "s5": 0, "s6": 0, "s7": 0, "s8": 0, "s9": 0, "s10": 0, "s11": 0,
  "t3": 0, "t4": 0, "t5": 0, "t6": 0
}

next_gpr_registers = {
  "zero": 0, "x0": 0, "ra": 0, "sp": 0, "gp": 0, "tp": 0,
  "t0": 0, "t1": 0, "t2": 0, "s0": 0, "s1": 0,
  "a0": 0, "a1": 0, "a2": 0, "a3": 0, "a4": 0, "a5": 0, "a6": 0, "a7": 0,
  "s2": 0, "s3": 0, "s4": 0, "s5": 0, "s6": 0, "s7": 0, "s8": 0, "s9": 0, "s10": 0, "s11": 0,
  "t3": 0, "t4": 0, "t5": 0, "t6": 0
}

def process_instr(trace):
    if trace.instr == "jal":
        # Spike jal format jal rd, -0xf -> jal rd, -15
        idx = trace.operand.rfind(",")
        imm = trace.operand[idx + 1:]
        if imm[0] == "-":
            imm = "-" + str(int(imm[1:], 16))
        else:
            imm = str(int(imm, 16))
        trace.operand = trace.operand[0:idx + 1] + imm
    # Properly format operands of all instructions of the form:
    # <instr> <reg1> <imm>(<reg2>)
    # The operands should be converted into CSV as:
    # "<reg1>,<reg2>,<imm>"
    m = ADDR_RE.search(trace.operand)
    if m:
        trace.operand = "{},{},{}".format(
            m.group("rd"), m.group("rs1"), m.group("imm"))


def read_spike_instr(match, full_trace):
    """Unpack a regex match for CORE_RE to a RiscvInstructionTraceEntry

    If full_trace is true, extract operand data from the disassembled
    instruction.

    """
    # Extract the disassembled instruction.
    disasm = match.group('instr')

    # Spike's disassembler shows a relative jump as something like "j pc +
    # 0x123" or "j pc - 0x123". We just want the relative offset.
    disasm = disasm.replace('pc + ', '').replace('pc - ', '-')

    instr = RiscvInstructionTraceEntry()
    instr.pc = match.group('addr')
    instr.instr_str = disasm
    instr.binary = match.group('bin')
    if full_trace:
        opcode = disasm.split(' ')[0]
        operand = disasm[len(opcode):].replace(' ', '')
        instr.instr, instr.operand = \
            convert_pseudo_instr(opcode, operand, instr.binary)

        process_instr(instr)

    return instr


def read_spike_trace(path, full_trace, full_hex):
    """Read a Spike simulation log at <path>, yielding executed instructions.

    This assumes that the log was generated with the -l and --log-commits options
    to Spike.

    If full_trace is true, extract operands from the disassembled instructions.

    Since Spike has a strange trampoline that always runs at the start, we skip
    instructions up to and including the one at PC 0x10010 (the end of the
    trampoline). At the end of a DV program, there's an ECALL instruction, which
    we take as a signal to stop checking, so we ditch everything that follows
    that instruction.

    This function yields instructions as it parses them as tuples of the form
    (entry, illegal). entry is a RiscvInstructionTraceEntry. illegal is a
    boolean, which is true if the instruction caused an illegal instruction trap.

    """

    # This loop is a simple FSM with states TRAMPOLINE, INSTR, EFFECT. The idea
    # is that we're in state TRAMPOLINE until we get to the end of Spike's
    # trampoline, then we switch between INSTR (where we expect to read an
    # instruction) and EFFECT (where we expect to read commit information).
    #
    # We yield a RiscvInstructionTraceEntry object each time we leave EFFECT
    # (going back to INSTR), we loop back from INSTR to itself, or we get to the
    # end of the file and have an instruction in hand.
    #
    # On entry to the loop body, we are in state TRAMPOLINE if in_trampoline is
    # true. Otherwise, we are in state EFFECT if instr is not None, otherwise we
    # are in state INSTR.

    #end_trampoline_re = re.compile(r'core.*: 0x0*10010 ')
    #end_trampoline_re = re.compile(r'core.*: >>>>  reset_vector') # TODO: RG: workaround
    #end_trampoline_re = re.compile(r'core.*: >>>>  _start') # TODO: RG: workaround
    # PW: added rvtest_entry_point & rvtest_code_begin for spike patched for riscv-arch-tests


    # Define regular expression patterns as separate strings
    end_trampoline_patterns = [
        r'core.*: >>>>  reset_vector',
        r'core.*: >>>>  _start',
        r'core.*: >>>>  _init',
        r'core.*: >>>>  rvtest_entry_point',
        r'core.*: >>>>  rvtest_code_begin',
        r'core.*: >>>>  \$xrv64i2p1_m2p0_a2p1_f2p2_zicsr2p0_zifencei2p0_zmmul1p0_zfh1p0_zfhmin1p0_zve32f1p0_zve32x1p0_zvl32b1p0',
        r'core.*: >>>>  \$xrv64i2p1_m2p0_a2p1_f2p2_c2p0_zicsr2p0_zifencei2p0_zmmul1p0_zfh1p0_zfhmin1p0_zve32f1p0_zve32x1p0_zvl32b1p0',
        # Add more patterns here if needed
    ]

    # Compile each pattern and store them in a list
    end_trampoline_re = [re.compile(pattern) for pattern in end_trampoline_patterns]

    # Now, end_trampoline_re is a list of compiled regular expression objects

    in_trampoline = True
    instr = None
    counter = 0

    with open(path, 'r') as handle:
        for line in handle:
            counter = counter + 1
            if in_trampoline:
                # The TRAMPOLINE state


                # Iterate over each compiled regular expression object in end_trampoline_re
                for regex in end_trampoline_re:
                    if regex.match(line):
                        in_trampoline = False

                continue

            if instr is None:
                # The INSTR state. We expect to see a line matching CORE_RE.
                # We'll discard any other lines.
                instr_match = CORE_RE.match(line)
                if not instr_match:
                    continue

                instr = read_spike_instr(instr_match, full_trace)

                continue

            # The EFFECT state. If the line matches CORE_RE, we should have been in
            # state INSTR, so we yield the instruction we had, read the new
            # instruction and continue.
            instr_match = CORE_RE.match(line)
            if instr_match:
                yield instr, False
                instr = read_spike_instr(instr_match, full_trace)
                continue

            # The line doesn't match CORE_RE, so we are definitely on a follow-on
            # line in the log. First, check for illegal instructions
            if (
                'exception trap_load_page_fault' in line or
                'exception trap_load_access_fault' in line or
                'exception trap_store_page_fault' in line or
                'exception trap_illegal_instruction' in line or
                'exception trap_load_address_misaligned' in line or
                'exception trap_store_address_misaligned' in line or
                'exception trap #4' in line # vector load trap
            ):
                yield (instr, True)
                logging.debug("[%d] Dbg Skipped Instruction: %s pc: %s binary: %s",   counter, instr.instr_str, instr.pc, line)
                instr = None
                continue

            # The instruction seems to have been fine. Do we have commit data (from
            # the --log-commits Spike option)?
            commit_match = RD_RE.match(line)
            if commit_match:
                instr.gpr.append(gpr_to_abi(commit_match.group('reg')
                                            .replace(' ', '')) +
                                 ':' + commit_match.group('val'))
                instr.mode = commit_match.group('pri')

                for gpr_entry in instr.gpr:
                    gpr_name, gpr_value = gpr_entry.split(':')
                    if not gpr_name.startswith(('v', 'f')):
                        gpr_registers[gpr_name] = next_gpr_registers[gpr_name]
                        # Only update on the next step, like in:
                        # vsetvl a5, zero a5
                        # we should use previous a5 value and not the Vd!
                        next_gpr_registers[gpr_name] = int(gpr_value, 16)


            vector_match = instr.instr_str[0] == 'v'
            if vector_match:
                vresult = parse_line(line)
                vresult['v_values'].sort(key=lambda x: int(x[0][1:]))

                if instr.instr_str[:4] == 'vset':

                    ## The following code extracts the VSETVL/VSETVLI/VSETIVLI instruction to get the vector length
                    ## and determine how many destination registers are needed by the vector instruction.
                    ## This is used when Spike does not print everything on the instruction log because of masking.
                    ## We do not want to implement the masks, so we just print every Vd as well.
                    vsetvl_elements = instr.instr_str.split(',')

                    ## Getting SEW
                    if instr.instr_str[:7] == 'vsetvl ': # we need the space to differentiate it with vsetvli
                        vsetvl_rs2 = vsetvl_elements[2].lstrip() # remove leading whitespace
                        sew_gpr_val = (gpr_registers[vsetvl_rs2] >> 3) & 0b111 # get only bits 5:3 of RS2 for the SEW
                        if sew_gpr_val == 0:
                            vector_sew = 8
                        elif sew_gpr_val == 1:
                            vector_sew = 16
                        elif sew_gpr_val == 2:
                            vector_sew = 32
                        else:
                            vector_sew = 64
                    else:
                        sew_part = next(part.strip() for part in vsetvl_elements if part.strip().startswith('e'))
                        vector_sew = int(sew_part[1:])

                    ## Getting Vector Length
                    if instr.instr_str[:6] == 'vsetvl':
                        vsetvl_rs1 = vsetvl_elements[1].lstrip() # remove leading whitespace
                        vsetvl_vd = vsetvl_elements[0].split()[1]
                        if vsetvl_rs1 == 'zero':
                            if vsetvl_vd != 'zero':
                                vector_length = int(VL_MAX/vector_sew)
                        else:
                            vector_length = gpr_registers[vsetvl_rs1]
                    else:
                        # vsetivli
                        vector_length = int(vsetvl_elements[1].lstrip())

                    logging.debug("Vector Instruction: %s GPR: %s vector_length: %s",   instr.instr_str, instr.gpr, vector_length)
                    vector_vd_num = 1

                if instr.instr_str.split()[1].startswith('v'):
                    vd = instr.instr_str.split()[1]
                    if vd.endswith(','):
                        vd = vd[:-1]

                    if instr.instr_str[:2] == 'vw':
                        effective_vsew = 2 * vector_sew
                    elif instr.instr_str[:6] == 'vle8ff':
                        effective_vsew = 8
                    elif instr.instr_str[:7] == 'vle16ff':
                        effective_vsew = 16
                    elif instr.instr_str[:7] == 'vle32ff':
                        effective_vsew = 32
                    else:
                        effective_vsew = vector_sew

                    vlmax_div_by_sew = VL_MAX//effective_vsew
                    quotient, remainder = divmod(vector_length, vlmax_div_by_sew)
                    vector_vd_num = quotient + (1 if remainder > 0 else 0)
                    if vector_vd_num == 0:
                        vector_vd_num = 1
                    elif vector_vd_num > VD_MAX:
                        vector_vd_num = 1 # you cannot use more than 32, so probably the setting is wrong. Just use 1 vd

                    # Handle special vector instructions
                    if instr.instr_str[:5] == 'vmv1r':
                        vector_vd_num = 1
                    elif instr.instr_str[:5] == 'vmv2r':
                        vector_vd_num = 2
                    elif instr.instr_str[:5] == 'vmv4r':
                        vector_vd_num = 4
                    elif instr.instr_str[:5] == 'vmv8r':
                        vector_vd_num = 8

                    vd_index = int(vd[1:])  # Assuming Vd is in the format "v<num>"
                    vd_list = [f'v{vd_index + i}' for i in range(vector_vd_num)]

                    # Append all Vd registers and their values
                    instr.gpr.clear()
                    for vd_reg in vd_list:
                        if vresult['v_values']:
                            for index, (vreg, value) in enumerate(vresult['v_values']):
                                if vd_reg == vreg and int(vd_reg[1:]) < VD_MAX:
                                    if not full_hex:
                                        short_val = shorten_hex_notation(value)
                                    else:
                                        short_val = value
                                    #instr.gpr.append(vreg + ':' + short_val)
                                    vector_registers[vreg] = short_val
                                    logging.debug("debug! pc: %s instr %s vreg: %s index: %s",    instr.pc, instr.instr_str, vreg, index)
                                    break

                        if int(vd_reg[1:]) < VD_MAX:
                            instr.gpr.append(vd_reg + ':' + vector_registers[vd_reg])
                        if instr.instr_str.startswith(('vse8', 'vse16', 'vse32')):
                            break # Spike only outputs once when using Vector Store elements

                    logging.debug("debug! pc: %s instr %s vreg: %s vector_length: %s vector_sew: %s",    instr.pc, instr.instr_str, vd, vector_length, vector_sew)

        # At EOF, we might have an instruction in hand. Yield it if so.
        if instr is not None:
            yield (instr, False)


def process_spike_sim_log(spike_log, csv, full_trace=False, vector=False, vector_only=False, full_hex=False):
    """Process SPIKE simulation log.

    Extract instruction and affected register information from spike simulation
    log and write the results to a CSV file at csv. Returns the number of
    instructions written.

    """
    logging.info("Processing spike log : {}".format(spike_log))
    instrs_in = 0
    instrs_out = 0

    with open(csv, "w") as csv_fd:
        trace_csv = RiscvInstructionTraceCsv(csv_fd)
        trace_csv.start_new_trace()

        for (entry, illegal) in read_spike_trace(spike_log, full_trace, full_hex):
            instrs_in += 1

            if illegal and full_trace:
                logging.debug("Illegal instruction: {}, opcode:{}"
                              .format(entry.instr_str, entry.binary))

            # Instructions that cause no architectural update (which includes illegal
            # instructions) are ignored if full_trace is false.
            #
            # We say that an instruction caused an architectural update if either we
            # saw a commit line (in which case, entry.gpr will contain a single
            # entry) or the instruction was 'wfi' or 'ecall'.
            if entry.instr_str:
                vector_match = entry.instr_str[0] == 'v'
            else:
                vector_match = False

            # FP match here is when destination register is F register, not necesarilly a floating point instruction
            if entry.gpr:
                fp_match = entry.gpr[0][0] == 'f'
            else:
                fp_match = False

            if illegal:
                logging.debug("Skipped Instruction: %s pc: %s binary: %s",   entry.instr_str, entry.pc, entry.binary)
                continue

            ## Trim captured FP entries to actual 32b (F extension)
            if fp_match:
                entry.trim_fp_gpr_values(trim_size_hex=8)

            if entry.gpr:
                if entry.gpr[0][0] != 'v' and not fp_match:
                    for gpr_entry in entry.gpr:
                        gpr_name, gpr_value = gpr_entry.split(':')
                        gpr_registers[gpr_name] = int(gpr_value, 16)  # Convert hex to integer

            if vector:
                ## if vector instuctions are enabled, then write all instructions when NOT in vector only mode, or when it is a vector instruction
                if (not vector_only or vector_match):
                    trace_csv.write_trace_entry(entry)
                    instrs_out += 1
                    if (vector_match):
                        logging.debug("Vector Instruction: {}" .format(entry.instr_str))
                        if (entry.gpr):
                            logging.debug("Vector Instruction GPR: {}" .format(entry.gpr[0]))

            elif (not vector_match and not vector_only):
                ## if vector instructions are disabled, do write only if it is a non-vector instruction, provided it is not in vector only mode
                trace_csv.write_trace_entry(entry)
                instrs_out += 1

    logging.info("Processed instruction count : {}".format(instrs_in))
    logging.info("Output    instruction count : {}".format(instrs_out))
    logging.info("CSV saved to : {}".format(csv))
    return instrs_out

def parse_line(line):
    # Initialize results
    result = {
        'çore': None,
        'addr': None,
        'insn': None,
        'v_values': [],
        'cstart': None
    }

    # Split the line by spaces
    parts = line.split()

    # Extract core number, count, addr, and binary
    try:
        core_index = parts.index('core') + 2
        result['addr'] = parts[core_index + 1]
        result['insn'] = parts[core_index + 2].strip('()')
    except (IndexError, ValueError):
        # Handle cases where addr or binary might be missing
        pass

    # Extract cX_vstart if present
    try:
        cstart_index = parts.index('c8_vstart')
        if cstart_index != -1 and cstart_index + 1 < len(parts):
            result['cstart'] = parts[cstart_index]
            result['cstart_value'] = parts[cstart_index + 1]
    except ValueError:
        pass

    # Extract vX values
    i = 0
    while i < len(parts):
        if parts[i].startswith('v') and i + 1 < len(parts):
            vreg = "v" + parts[i][1:]
            value = parts[i + 1]
            result['v_values'].append((vreg, value))
            i += 2
        else:
            i += 1

    return result

def shorten_hex_notation(hex_string):
    # Validate input
    if not hex_string.startswith("0x"):
        raise ValueError("Input should be a hexadecimal string starting with '0x'.")

    # Remove the "0x" prefix to work with just the number part
    hex_number = hex_string[2:]

    # Variables to track the repeated sequence
    first_char = hex_number[0]
    count = 1

    # Find the longest sequence of repeated characters at the beginning
    for i in range(1, len(hex_number)):
        if hex_number[i] == first_char:
            count += 1
        else:
            break  # Stop counting once a different character is found

    # Extract the remaining digits after the repeated sequence
    remaining_digits = hex_number[count:]

    # Construct the shortened notation
    shortened = f"{first_char}^{count}"
    if remaining_digits:
        shortened += f"-{remaining_digits}"

    return "0x" + shortened

def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=str, help="Input spike simulation log")
    parser.add_argument("--csv", type=str, help="Output trace csv_buf file")
    parser.add_argument("-f", "--full_trace", dest="full_trace", action="store_true", help="Generate the full trace")
    parser.add_argument("-v", "--verbose", dest="verbose", action="store_true", help="Verbose logging")
    parser.add_argument("-vec", "--vector", dest="vector", action="store_true", help="Vector Parsing Enable")
    parser.add_argument("-vo", "--vector_only", dest="vector_only", action="store_true", help="Vector Parsing Enable")
    parser.add_argument("-fh", "--full_hex", dest="full_hex", action="store_true", help="Full Hex Notation Enable")
    args = parser.parse_args()
    setup_logging(args.verbose)
    # Process spike log
    process_spike_sim_log(args.log, args.csv, args.full_trace, args.vector, args.vector_only, args.full_hex)


if __name__ == "__main__":
    main()
