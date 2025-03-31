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
import difflib
from enum import Enum


class VerbosityLevel(Enum):
    """ Enum class that defines the verbosity level that can be controlled by LogUtil """
    COMPACT   = 1
    DETAIL    = 2
    DEBUG     = 3

    def __str__(self):
        return f'{self.name.lower()}'

    def __repr__(self):
        return str(self)

    def __lt__(self, other):
      if self.__class__ is other.__class__:
        return self.value < other.value
      return NotImplemented

    @staticmethod
    def argparse(arg):
        """ VerbosityLevel argument process method """
        try:
            return VerbosityLevel[arg.upper()]
        except KeyError:
            return arg


class LogType(Enum):
    """ Enum class that defines all log types supported by LogUtil """
    DEBUG   = 1
    INFO    = 2
    WARN    = 3
    ERROR   = 4
    TRACE   = 5
    CALL    = 6

    def __str__(self):
        return f'{self.name}'

    def __repr__(self):
        return str(self)

    def __lt__(self, other):
      if self.__class__ is other.__class__:
        return self.value < other.value
      return NotImplemented


class DiffFormat(Enum):
    """ Enum class that defines all the comparation outout format supported by LogUtil """
    SINIT   = 0
    HTML    = 1
    CDIFF   = 2
    NDIFF   = 3
    UDIFF   = 4
    NONE    = 5

    def __str__(self):
        return f'{self.name.lower()}'

    def __repr__(self):
        return str(self)

    @staticmethod
    def argparse(arg):
        """ DiffFormat argument process method """
        try:
            return DiffFormat[arg.upper()]
        except KeyError:
            return arg


class LogUtil():
    LEVEL_SHIFT_SIZE = 4

    TOOL_VERSION = "1.00a-ea01"

    LOG_FILE_A = "LOG_A"
    LOG_FILE_B = "LOG_B"
    LOG_FILE   = "LOG_FILE"

    def __init__(self, verb_level=VerbosityLevel.COMPACT):
        """ Diff default format is set to SINIT """
        self.set_verb_level(verb_level)
        self.diff_format = DiffFormat.SINIT
        self.diff_output = None

    def set_verb_level(self, verb_level):
        """ Set verbosity level """
        self.verb_level = verb_level

    def get_verb_level(self):
        """ returns verbosity level as VerbosityLevel enum """
        return self.verb_level

    def get_version(self):
        """ returns log util string """
        return LogUtil().TOOL_VERSION

    def set_diff_format(self, format):
        """ Set diff output format based on DiffFormat enum """
        self.diff_format = format

    def set_diff_output(self, output):
        """ Set diff output file name or None of stdout """
        self.diff_output = output

    def get_diff_output(self):
        """ returns diff output file name """
        if self.diff_format is DiffFormat.NONE:
            return None
        return self.diff_output

    def process(self, log_file):
        """ reads the log and process it to display only the data based on the configured verbosity level """
        log_output_data = []
        with open(log_file) as log_data:
            for line in log_data:
                log_sections = re.split(r'\|',line)
                if len(log_sections) == 0:
                    continue
                try:
                    log_type = LogType[log_sections[0].strip()]
                except KeyError:
                    log_output_data.append(line.strip())
                    continue
                if log_type == LogType.TRACE or log_type == LogType.CALL:
                    if self.verb_level < VerbosityLevel.DETAIL:
                        continue
                    else:
                        log_output_data.append(line.strip())
                        continue
                if len(log_sections) < 4:
                    log_output_data.append("INVALID LOG_LINE: " + line.strip())
                    continue
                if (self.verb_level < VerbosityLevel.DEBUG) and (log_type == LogType.DEBUG):
                    continue
                if self.verb_level is VerbosityLevel.COMPACT:
                    log_output_data.append(str(log_type) + " | " + (" | ".join(log_sections[5:])).strip())
                    continue
                log_output_data.append(line.strip())
        # return each line back with new lines in the end for the comparation tools
        return ('\n'.join(log_output_data) + "\n").splitlines(keepends=True)

    def compare_count_diffs(self, list_a, list_b):
        """ linear log comparation, fast way to verify if the files match our not, returns number of differences """
        len_a = len(list_a)
        len_b = len(list_b)
        counter = abs(len_a - len_b)
        for line in range(min(len_a, len_b)):
            if list_a[line] != list_b[line]:
                counter += 1
        return counter

    def diff_sinit_format(self, list_a, list_b):
        """ returns the logs differences in the internal format, fast algorithm """
        compare_rst = []
        len_a = len(list_a)
        len_b = len(list_b)
        if len_a != len_b:
            compare_rst.append("%s/%s = %d/%d\n" % \
                               (LogUtil.LOG_FILE_A, LogUtil.LOG_FILE_B, len_a, len_b))
        for line in range(min(len_a, len_b)):
            if list_a[line] != list_b[line]:
                line_diff = "%4d | " % line
                line_diff += ("%*s | " % (len(LogUtil.LOG_FILE_A) , LogUtil.LOG_FILE_A)) + list_a[line]
                line_diff += ("%*s | " % (len(LogUtil.LOG_FILE_B) + 7, LogUtil.LOG_FILE_B)) + list_b[line]
                compare_rst.append(line_diff)
        return compare_rst

    def compare_log_files(self, file_a, file_b):
        """ compares file_a and file_b (lists of strings) and returns a string with the differences
         in the format selected in the class """
        # Read the log files and reduce them depending on the verbosity level
        log_a = self.process(file_a)
        log_b = self.process(file_b)
        # Fast comparation process, exit fast if no changes found
        diff_count = self.compare_count_diffs(log_a, log_b)
        if (diff_count == 0) or (self.diff_format is DiffFormat.NONE):
            return diff_count
        # Diff the log files using the configured method
        if self.diff_format is DiffFormat.SINIT:
            diff = self.diff_sinit_format(log_a, log_b)
        elif self.diff_format is DiffFormat.HTML:
            diff = difflib.HtmlDiff().make_file(log_a, log_b, file_a, file_b, context=True)
        elif self.diff_format is DiffFormat.CDIFF:
            diff = difflib.context_diff(log_a, log_b, file_a ,file_b)
        elif self.diff_format is DiffFormat.UDIFF:
            diff = difflib.unified_diff(log_a, log_b, file_a ,file_b)
        elif self.diff_format is DiffFormat.NDIFF:
            diff = difflib.ndiff(log_a, log_b)
        else:
            raise Exception("Diff format not supported:" + self.diff_format)
        self.ouput_lines(diff)
        return diff_count

    def ouput_lines(self, str_list):
        """ writes the str_list to the output method defined in the class """
        if self.diff_output is None:
            sys.stdout.writelines(str_list)
        else:
            with open(self.diff_output, 'w') as diff_file:
                diff_file.writelines(str_list)

    def _parser_check_file_exist(self, file_id, file):
        """ verifies if the input file exists """
        if os.path.isfile(file) is False:
            parser.error("%s \"%s\" not found." % (file_id, file))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', "--log_level", dest='log_level',
                        type=VerbosityLevel.argparse, choices=list(VerbosityLevel),
                        help="Set ouput verbosity Level")
    parser.add_argument("-d", "--diff_format", dest='diff_format',
                        type=DiffFormat.argparse, choices=list(DiffFormat),
                        help="Comparation differences output format")
    parser.add_argument("-o", "--diff_output", dest='diff_output',
                        type=str, help="Diffs output file, defaults to stdout")

    exclusive_group = parser.add_mutually_exclusive_group()
    exclusive_group.add_argument("-v", "--version",   dest='version',   action='store_true', help="Print version")
    exclusive_group.add_argument("-f", "--log_file",  dest='log_file',  type=str,
                                 metavar=(LogUtil.LOG_FILE), help="Log file")
    exclusive_group.add_argument("-c", "--compare",   dest='compare',   nargs=2,
                                 metavar=(LogUtil.LOG_FILE_A, LogUtil.LOG_FILE_B), help="Files to compare")
    results = parser.parse_args()

    if len(sys.argv) == 1:
        parser.error('No arguments provided')

    log_util = LogUtil()

    if results.version is True:
        print ("Version: " + log_util.get_version())
        exit(0)

    if results.log_level is not None:
        log_util.set_verb_level(results.log_level)

    if results.log_file is not None:
        log_util._parser_check_file_exist(LogUtil.LOG_FILE, results.log_file)
        output = log_util.process(results.log_file)
        log_util.ouput_lines(output)

    if results.diff_format is not None:
        log_util.set_diff_format(results.diff_format)
    if results.diff_output is not None:
        log_util.set_diff_output(results.diff_output)

    if results.compare is not None:
        file_a, file_b = results.compare
        log_util._parser_check_file_exist(LogUtil.LOG_FILE_A, file_a)
        log_util._parser_check_file_exist(LogUtil.LOG_FILE_B, file_b)
        diffs = log_util.compare_log_files(file_a, file_b)
        if diffs > 0:
            print("Files differ, %d differences found." % diffs)
            outfile = log_util.get_diff_output()
            if outfile is not None:
                print("Output written to %s." % outfile)
        exit(diffs)





