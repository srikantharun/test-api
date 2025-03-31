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
import argparse
import json
import array
import math
import copy
import re
import csv
from lxml import etree
from pathlib import Path

from argparse import ArgumentTypeError
from libconfig.types.config_dict import ConfigDict
import libconfig.utils as utils

alternaive_names = { "DDR54_PHY" : {"name": "PhyType", "type": "int", "value": 1},
                     "LPDDR54_PHY" : {"name": "PhyType", "type": "int", "value": 2},
                     "DDR54_PHY_V2" : {"name": "PhyType", "type": "int", "value": 3},
                     "LPDDR5X4_PHY" : {"name": "PhyType", "type": "int", "value": 4},
                     "DDR5_PHY" : {"name": "PhyType", "type": "int", "value": 5},
                     "LPDDR4X_MULTIPHY" : {"name": "PhyType", "type": "int", "value": 6},
                  }

class CHeaderParser():

    def parse_c_headers(c_headers_list, category_name):
        """ Parse cc constants file """

        ddr_ctrl_config = ConfigDict(name=category_name)

        for c_header_path in c_headers_list:
            with open(c_header_path) as cfg_data:
                for line in cfg_data:
                    if line.find("#define") >= 0:
                        config = line.replace("\n", "").replace("#define ", "")
                        config = re.sub(' +', ' ', config)
                        config = re.sub(' +$', '', config)
                        config_list = config.split(" ", 1)
                        config_name = config_list[0]
                        if len(config_list) < 2:
                            param_type = "bool"
                            value = "1"
                        else:
                            config_value = config_list[1]
                            # clean spaces before and after operators
                            config_value = re.sub(r'(\S)([-+*/])', r'\g<1> \g<2>', config_value)
                            config_value = re.sub(r'([-+*/])(\S)', r'\g<1> \g<2>', config_value)
                            if config_value.find("0x") >= 0:
                                # if hex values are present, convert all values into a list
                                d_help = config_value.split(" ")
                                config_value = ""
                                for item in d_help:
                                    if item.find("0x") >= 0:
                                        # if item in list is hex, convert to int
                                        match = re.search(r'0[xX][0-9a-fA-F]+', item)
                                        config_value += item.replace(match.group(0), str(int(match.group(0), 0)))
                                    else:
                                        config_value += item
                            param_type = "int"
                            value = config_value

                        ddr_ctrl_config.add(name=config_name, type=param_type, value=value)

                        # add alternaive names for the same parameter
                        if config_name in alternaive_names:
                            alternaive_name_data = alternaive_names[config_name]
                            ddr_ctrl_config.add(name=alternaive_name_data["name"], type=alternaive_name_data["type"], value=alternaive_name_data["value"])

        return ddr_ctrl_config

    def validate_file_cc_constants(cc_const_path):
        """ Validate cc constants files
            this functions should only be called by argparse while verifying the arguments
            errors must be argparse exceptions"""

        if (os.path.isfile(cc_const_path) is False):
            raise ArgumentTypeError("CC constants file %s not found" % cc_const_path)

        with open(cc_const_path) as cfg_data:
            for line in cfg_data:
                # look for header guard
                if line.startswith("#ifndef") is not True:
                    continue
                # Check if file is a valid C_HEADERS by checking if the guard matches the expected
                if ('DWC_DDRCTL_CC_CONSTANTS_H' in line) or ('DWC_IME_CC_CONSTANTS_H' in line):
                    return cc_const_path
        raise ArgumentTypeError("File %s not a valid CC constants file" % cc_const_path)

    def validate_file_v_defines(vdefines_path):
        """ Validate VDEFINES files
            this functions should only be called by argparse while verifying the arguments
            errors must be argparse exceptions"""

        if (os.path.isfile(vdefines_path) is False):
            raise ArgumentTypeError("VDEFINES file %s not found" % vdefines_path)

        with open(vdefines_path) as cfg_data:
            for line in cfg_data:
                # look for header guard
                if line.startswith("#ifndef") is not True:
                    continue
                # Check if file is a valid VDEFINES by checking if the guard matches the expected
                if ('DWC_DDRPHY_VDEFINES_H' in line):
                    return vdefines_path
        raise ArgumentTypeError("File %s not a valid VDEFINES file" % vdefines_path)
