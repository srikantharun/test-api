#!/usr/bin/env python3

# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------


#system
import sys
import os
import re
import argparse
import subprocess
from datetime import datetime


class TraceDecoder():
    OUTPUT_COMPACT = 1
    OUTPUT_DETAIL  = 2
    OUTPUT_DEBUG   = 3

    LEVEL_SHIFT_SIZE = 4

    TOOL_VERSION = "1.00a-ea01"

    exec_file = None
    dyn_lib_file = None
    dyn_lib_addr_start = None
    dyn_lib_addr_end = None

    addr_exec_name_dict = {}
    addr_exec_line_dict = {}
    addr_lib_name_dict = {}
    addr_lib_line_dict = {}

    def __init__(self, verb_level=OUTPUT_COMPACT):
        self.set_verb_level(verb_level)

    def set_verb_level(self, verb_level):
        self.verb_level = verb_level

    def get_version(self):
        return TraceDecoder().TOOL_VERSION

    def set_exec_file(self, exec_file):
        if os.path.isfile(exec_file) is False:
            print("ERROR: Executable file %s doesn't exist." + exec_file)
            exit(-1)
        self.exec_file = exec_file

    def set_dyn_lib_file(self, dyn_lib_file):
        if os.path.isfile(dyn_lib_file) is False:
            print("ERROR: Dynamic lib file %s doesn't exist." + dyn_lib_file)
            exit(-1)
        self.dyn_lib_file = dyn_lib_file

    def set_dyn_lib_addr(self, addr, size):
        self.dyn_lib_addr_start = addr
        self.dyn_lib_addr_end = addr + size

    def _get_symbol_name_from_bin(self, addr, bin_file):
        addr_str = "0x%x" % addr
        symbol_name = subprocess.run("addr2line -f -e %s %s | head -1" % (bin_file, addr_str), shell=True, stdout=subprocess.PIPE)
        symbol_name = symbol_name.stdout.decode("utf-8").strip()
        return symbol_name + "()"

    def _get_lib_symbol_name(self, addr):
        if self.dyn_lib_file is None:
            return "0x%x" % addr
        symbol_name = self.addr_lib_name_dict.get(addr)
        if symbol_name is None:        
            symbol_name = self._get_symbol_name_from_bin(addr, self.dyn_lib_file)
            self.addr_lib_name_dict[addr] = symbol_name
        return symbol_name

    def _get_exec_symbol_name(self, addr):
        if self.exec_file is None:
            return "0x%x" % addr
        symbol_name = self.addr_exec_name_dict.get(addr)
        if symbol_name is None:        
            symbol_name = self._get_symbol_name_from_bin(addr, self.exec_file)
            self.addr_exec_name_dict[addr] = symbol_name
        return symbol_name

    def get_symbol_name(self, addr):
        if (self.dyn_lib_addr_start is not None) and (addr > self.dyn_lib_addr_start):
            if addr < self.dyn_lib_addr_end:
                print("ERROR: addr outside %x" % addr)
            symbol_name = self._get_lib_symbol_name(addr - self.dyn_lib_addr_start)
        else:
            symbol_name = self._get_exec_symbol_name(addr)
        return symbol_name

    def _get_symbol_call_file_line_from_bin(self, addr, bin_file):
        addr_str = "0x%x" % addr
        call_file_line = subprocess.run("addr2line -f -e %s %s" % (bin_file, addr_str), shell=True, stdout=subprocess.PIPE)
        call_file_line = call_file_line.stdout.decode("utf-8").splitlines()
        funct_name = call_file_line[0].strip() + "()"
        if len(call_file_line) > 1:
            funct_file_line = call_file_line[1].strip().split(":")
            file_name = os.path.basename(funct_file_line[0])
            if len(funct_file_line) > 1:
                file_line = funct_file_line[1]
                funct_name += ":" + file_line
            if self.verb_level >= self.OUTPUT_DEBUG:
                funct_name = "[" + file_name + "] " + funct_name
        return funct_name

    def _get_lib_symbol_call_file_line(self, addr):
        if self.dyn_lib_file is None:
            return "0x%x" % addr
        call_file_line = self.addr_lib_line_dict.get(addr)
        if call_file_line is None:        
            call_file_line = self._get_symbol_call_file_line_from_bin(addr, self.dyn_lib_file)
            self.addr_lib_line_dict[addr] = call_file_line
        return call_file_line

    def _get_exec_symbol_call_file_line(self, addr):
        if self.exec_file is None:
            return "0x%x" % addr
        call_file_line = self.addr_exec_line_dict.get(addr)
        if call_file_line is None:        
            call_file_line = self._get_symbol_call_file_line_from_bin(addr, self.exec_file)
            self.addr_exec_line_dict[addr] = call_file_line
        return call_file_line

    def get_symbol_call_file_line(self, addr):
        if (self.dyn_lib_addr_start is not None) and (addr > self.dyn_lib_addr_start):
            if addr < self.dyn_lib_addr_end:
                print("ERROR: addr outside %x" % addr)
            call_file_line = self._get_lib_symbol_call_file_line(addr - self.dyn_lib_addr_start)
        else:
            call_file_line = self._get_exec_symbol_call_file_line(addr)
        return call_file_line


    def decode(self, trace_file):
        lib_base_addr_set = False
        level = 0
        level_func_offset = {}
        initial_call_time = None
        time_from_start = 0
        with open(trace_file) as trace_log:
  
            for line in trace_log:
                if line.startswith("TRACE|") is False:
                    print(line.strip())
                    continue

                trace_data = line.split()
                if len(trace_data) == 5:        # Entry/Exit report
                    entry_type = trace_data[1]
                    func_addr  = int(trace_data[2], 0)
                    call_addr  = int(trace_data[3], 0)
                    c_timer    = int(trace_data[4], 0)
                elif len(trace_data) == 4:      
                    entry_type = trace_data[1]
                    base_addr  = int(trace_data[2], 0)
                    base_size  = int(trace_data[3], 0)
                else:
                    print ("Invalid trace log line: %s" % line)
                    exit(-1)
                
                if entry_type == "ADDR|": # Dynamic Address information
                    if lib_base_addr_set is False:
                        print("Set lib address to %x %x " % (base_addr, base_size))
                        self.set_dyn_lib_addr(base_addr, base_size)
                        lib_base_addr_set = True
                    continue

                if initial_call_time is None:
                    initial_call_time = c_timer

                time_from_start = c_timer - initial_call_time
                out_str = "CALL |%5d|" % time_from_start

                func_name = self.get_symbol_name(func_addr)

                if entry_type == "ENTR|":
                    call_name = self.get_symbol_call_file_line( call_addr)
                    print("%s%*s %s -> %s" % (out_str, self.LEVEL_SHIFT_SIZE*level, "", call_name, func_name))
                    level += 1
                    level_func_offset[level] = len(call_name)
                else:
                    level -= 1
                    if self.verb_level >= self.OUTPUT_DETAIL:
                        offset = level_func_offset[level + 1]
                        print("%s%*s %*s <- %s" % (out_str, self.LEVEL_SHIFT_SIZE*level, "", offset, "", func_name))

                    

if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("-v", "--version",       dest='version',          action='store_true', help="Print version")
    parser.add_argument('-l', "--log_level",     dest='log_level',        type=int,            help="Log level")
    parser.add_argument("-e", "--exec",          dest='exec_file',        type=str,            help="Executable file")
    parser.add_argument("-d", "--dynamic_lib",   dest='dynamic_lib_file', type=str,            help="Dynamic library")
    parser.add_argument("-t", "--trace",         dest='trace_file',       type=str,            help="Trace log file")

    results = parser.parse_args()

    if len(sys.argv) == 1:
        parser.error('No arguments provided')

    if results.version is True:
        print ("Version: " + TraceDecoder().get_version())
        exit(0)

    if (results.exec_file is None) and (results.dynamic_lib_file is None):
        parser.error('No executable nor dynamic library define, at least one needs to be set')

    if results.trace_file is None:
        parser.error('Log trace file not defined')

    if os.path.isfile(results.trace_file) is False:
        parser.error("Trace file %s doesn't exist." + results.trace_file)

    decoder = TraceDecoder()

    if (results.log_level is not None):
        decoder.set_verb_level(results.log_level)

    if results.exec_file is not None:
        decoder.set_exec_file(results.exec_file)

    if results.dynamic_lib_file is not None:
        decoder.set_dyn_lib_file(results.dynamic_lib_file)

    decoder.decode(results.trace_file)
