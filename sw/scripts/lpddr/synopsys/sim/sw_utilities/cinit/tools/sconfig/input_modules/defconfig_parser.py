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


import sys
import os
import re
from argparse import ArgumentTypeError

# Local
from libconfig.lib_config import LibConfig
from libconfig.types.option import Option
from input_modules.module_data.renamed_configs import RENAMED_CONFIGS_LIST
import libconfig.utils as utils
from libconfig.log import Log
from libconfig.types.eval_expressions import EvalExpressions, EvalExpressionsError

class DefconfigError(Exception):
    def __init__(self, message):
        super().__init__(message)


class DefconfigParser():

    def __init__(self):
        self.lib_config = LibConfig()

    def load_defconfig(self, defconfig_path):
        """ Load configuration form a defconfig file """
        error_msg = ""
        config_list = []
        line_no = 0

        with open(defconfig_path,'r') as defconfig_file:
            for line in defconfig_file:
                line = line.replace('\n','')
                line_no += 1
                # exclude comments and empty lines
                if ((re.match('^#', line)) or ('' == line)):
                    continue

                # expand each line into many if ranges are found
                lines = self.expand_ranges(line)

                for line in lines:
                    ret = self.process_line(line, line_no)
                    if (isinstance(ret, str) is False):
                        config_list.append(ret)
                    else:
                        error_msg += "Line %d: %s\n"%(line_no, ret)

        if (len(error_msg) > 0):
            error_msg = "Errors found in Defconfig %s:\n%s" % (defconfig_path, error_msg)
            Log().error(error_msg)
            exit(utils.EXIT_ERROR)

        # After all parameters are read
        # check if all config options are supported in the current state
        errors_found = False
        for config in config_list:
            if config.is_supported() is False:
                errors_found = True

        if (errors_found is True):
            Log().error("Errors found in configuration state")
            # TODO When the repo is stable without errors add EXIT_ERROR

    def process_line(self, line, line_no=None):
        """ Process each line and store the configuration """

        split_line = line.split('=')
        if (len(split_line) < 2):
            Log().error("Each line of defconfig files must always be <config>=<value>\n%s"%(line))
            exit(utils.EXIT_ERROR)
        param = split_line[0].strip()
        value = split_line[1].strip()

        #ignore _AUX suffix
        param = re.sub('_AUX$', '', param)

        config = self.lib_config.find_config_by_id(param)
        if config is None:
            #ignore CONFIG_ prefix and recheck
            param = re.sub('^(CONFIG_)', '', param)
            config = self.lib_config.find_config_by_id(param)

        if config is None:
            if param in RENAMED_CONFIGS_LIST:
                new_name = RENAMED_CONFIGS_LIST[param]
                error_msg = 'Deprecated: \'%s\' replace with \'%s\'' % (param, new_name)
            else:
                 error_msg = "Invalid configuration in line \'%s\'" % (line)
            raise DefconfigError(error_msg)

        if (isinstance(config, Option) is True):
            config.parent.set_value(param, line, line_no)
            return config.parent

        value = self.process_value(value)
        config.set_value(value, line, line_no)
        return config

    def process_value(self, value):
        """ Convert the value string into a integer when possible """

        if (isinstance(value, str) is True) and ('@' in value):
            return self.process_expression(value)

        if (value == 'y'):
            return 1
        elif (value == 'n'):
            return 0
        elif ('0x' in value):
            return int(value, 16)
        elif (value.isnumeric() is True):
            return int(value)
        else:
            return value

    def validate_file(defconfig_path):
        """ Validate defconfig file errors
            this functions should only be called by argparse while verifying the arguments
            errors must be argparse exceptions"""

        if (os.path.isfile(defconfig_path) is False):
            raise ArgumentTypeError("Defconfig file %s not found" % defconfig_path)

        with open(defconfig_path) as defconfig_data:
            for line in defconfig_data:
                # look for defconfig name
                if ("SNPS_DEFCONFIG" in line):
                    # defconfig is valid
                    return defconfig_path

            raise ArgumentTypeError("File %s is not a valid DEFCONFIG file (SNPS_DEFCONFIG parameter not found)"%defconfig_path)

    def process_expression(self, expression):
        """ Process the condition within a range into an integer or give an error """
        try:
            value = EvalExpressions.evaluate_to_int(expression, LibConfig().get_config_dict(), static_only=True)
        except EvalExpressionsError as err:
            Log().error("ERROR: value of condition %s cannot be evaluated as an integer" % (expression))
            sys.exit(utils.EXIT_ERROR)
        return value

    def expand_ranges(self, line):
        """ expand each line based on any ranges found within the line """

        expanded_lines = []

        # find ranges in defconfig lines
        ret = re.search(r"^(.*)\[(.*):(.*)\](.*)$", line)
        if (ret is None):
            return [line]

        # resolve range conditions
        starting_index = self.process_expression(ret.group(2))
        ending_index   = self.process_expression(ret.group(3))

        # generate a generic format for each line
        expanded_line_format = re.sub(r"^(.*)\[(.*):(.*)\](.*)$", r"\1{idx}\4", line)

        # generate each line in range
        for idx in range(starting_index, ending_index + 1):
            expanded_line = expanded_line_format.format(idx=idx)
            expanded_lines.append(expanded_line)

        return expanded_lines
