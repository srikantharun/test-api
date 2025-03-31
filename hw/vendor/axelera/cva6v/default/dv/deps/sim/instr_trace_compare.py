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

Compare the instruction trace CSV
"""

import argparse
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.realpath(__file__)))

from riscv_trace_csv import *


def compare_trace_csv(csv1, csv2, name1, name2, log,
                      in_order_mode=1,
                      coalescing_limit=0,
                      verbose=0,
                      mismatch_print_limit=5,
                      compare_final_value_only=0):
    """Compare two trace CSV file"""
    matched_cnt = 0
    mismatch_cnt = 0

    # ensure that in order mode is disabled if necessary
    if compare_final_value_only:
        in_order_mode = 0

    if log:
        fd = open(log, 'a+')
    else:
        fd = sys.stdout

    fd.write("{} : {}\n".format(name1, csv1))
    fd.write("{} : {}\n".format(name2, csv2))

    with open(csv1, "r") as fd1, open(csv2, "r") as fd2:
        instr_trace_1 = []
        instr_trace_2 = []
        trace_csv_1 = RiscvInstructionTraceCsv(fd1)
        trace_csv_2 = RiscvInstructionTraceCsv(fd2)
        trace_csv_1.read_trace(instr_trace_1)
        trace_csv_2.read_trace(instr_trace_2)
        trace_1_index = 0
        trace_2_index = 0
        mismatch_cnt = 0
        matched_cnt = 0
        if in_order_mode:
            gpr_val_1 = {}
            gpr_val_2 = {}
            for trace in instr_trace_1:
                trace_1_index += 1
                if len(trace.gpr) == 0:
                    continue
                # Check if there's a GPR change caused by this instruction
                gpr_state_change_1 = check_update_gpr(trace.gpr, gpr_val_1)
                if gpr_state_change_1 == 0:
                    continue
                # Move forward the other trace until a GPR update happens
                gpr_state_change_2 = 0
                while (gpr_state_change_2 == 0 and trace_2_index < len(
                        instr_trace_2)):
                    gpr_state_change_2 = check_update_gpr(
                        instr_trace_2[trace_2_index].gpr,
                        gpr_val_2)
                    trace_2_index += 1
                # Check if the GPR update is the same between trace 1 and 2
                if gpr_state_change_2 == 0:
                    mismatch_cnt += 1
                    fd.write("Mismatch[{}]:\n[{}] {} : {}\n".format(
                      mismatch_cnt, trace_1_index, name1,trace.get_trace_string()))
                    fd.write("{} instructions left in trace {}\n".format(
                      len(instr_trace_1) - trace_1_index + 1, name1))
                elif len(trace.gpr) != len(
                        instr_trace_2[trace_2_index - 1].gpr):
                    mismatch_cnt += 1
                    # print first few mismatches
                    if mismatch_cnt <= mismatch_print_limit:
                        fd.write("Mismatch[{}]:\n{}[{}] : {}\n".format(
                          mismatch_cnt, name1, trace_2_index - 1,
                          trace.get_trace_string()))
                        fd.write("{}[{}] : {}\n".format(
                          name2, trace_2_index - 1,
                          instr_trace_2[
                            trace_2_index - 1].get_trace_string()))
                else:
                    found_mismatch = 0
                    for i in range(len(trace.gpr)):
                        if trace.gpr[i] != instr_trace_2[trace_2_index - 1].gpr[i]:
                            mismatch_cnt += 1
                            found_mismatch = 1
                            # print first few mismatches
                            if mismatch_cnt <= mismatch_print_limit:
                                fd.write("Mismatch[{}]:\n{}[{}] : {}\n".format(
                                    mismatch_cnt, name1, trace_2_index - 1,
                                    trace.get_trace_string()))
                                fd.write("{}[{}] : {}\n".format(
                                    name2, trace_2_index - 1,
                                    instr_trace_2[
                                        trace_2_index - 1].get_trace_string()))
                            break
                    if not found_mismatch:
                        matched_cnt += 1
                # Break the loop if it reaches the end of trace 2
                if trace_2_index == len(instr_trace_2):
                    break
            # Check if there's remaining instruction that change architectural state
            if trace_2_index != len(instr_trace_2):
                while trace_2_index < len(instr_trace_2):
                    gpr_state_change_2 = check_update_gpr(
                        instr_trace_2[trace_2_index].gpr,
                        gpr_val_2)
                    if gpr_state_change_2 == 1:
                        fd.write("{} instructions left in trace {}\n".format(
                          len(instr_trace_2) - trace_2_index, name2))
                        mismatch_cnt += len(instr_trace_2) - trace_2_index
                        break
                    trace_2_index += 1
        else:
            pass
        if mismatch_cnt == 0:
            compare_result = "[PASSED]: {} matched\n".format(matched_cnt)
        else:
            compare_result = "[FAILED]: {} matched, {} mismatch\n".format(
                matched_cnt, mismatch_cnt)
        fd.write(compare_result + "\n")
        if log:
            fd.close()
        return compare_result


def check_update_gpr(gpr_update, gpr):
    gpr_state_change = 0
    for update in gpr_update:
        if update == "":
            return 0
        item = update.split(":")
        if len(item) != 2:
            sys.exit("Illegal GPR update format:" + update)
        rd = item[0]
        rd_val = item[1]
        if rd in gpr:
            if rd_val != gpr[rd]:
                gpr_state_change = 1
        else:
            if int(rd_val, 16) != 0:
                gpr_state_change = 1
        gpr[rd] = rd_val
    return gpr_state_change

def main():
    # Parse input arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv_file_1", type=str,
                        help="Instruction trace 1 CSV")
    parser.add_argument("--csv_file_2", type=str,
                        help="Instruction trace 2 CSV")
    parser.add_argument("--csv_name_1", type=str,
                        help="Instruction trace 1 name")
    parser.add_argument("--csv_name_2", type=str,
                        help="Instruction trace 2 name")
    # optional arguments
    parser.add_argument("--log", type=str, default="",
                        help="Log file")
    parser.add_argument("--in_order_mode", type=int, default=1,
                        help="In order comparison mode")
    parser.add_argument("--gpr_update_coalescing_limit", type=int, default=1,
                        help="Allow the core to merge multiple updates to the \
                            same GPR into one. This option only applies to \
                            trace 2")
    parser.add_argument("--mismatch_print_limit", type=int, default=5,
                        help="Max number of mismatches printed")
    parser.add_argument("--verbose", type=int, default=0,
                        help="Verbose logging")
    parser.add_argument("--compare_final_value_only", type=int, default=0,
                        help="Only compare the final value of the GPR")

    args = parser.parse_args()

    # Compare trace CSV
    compare_trace_csv(args.csv_file_1, args.csv_file_2,
                      args.csv_name_1, args.csv_name_2, args.log,
                      args.in_order_mode, args.gpr_update_coalescing_limit,
                      args.verbose, args.mismatch_print_limit,
                      args.compare_final_value_only)


if __name__ == "__main__":
    main()
