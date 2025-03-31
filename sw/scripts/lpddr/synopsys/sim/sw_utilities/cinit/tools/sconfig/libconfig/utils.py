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


import os

EXIT_SUCCESS =  0
EXIT_ERROR   = -1

class LibConfigError(Exception):
    def __init__(self, message):
        super().__init__(message)

class Singleton(type):
    """ A metaclass that creates a Singleton base class when called. """
    _instances = {}
    def __call__(cls, *args, **kwargs):
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]

def indent(str, level=1, spacing=4):
    """ Indent a sting according to the indent level """

    line_list = str.split('\n')
    spacing_str = '\n' + ' '*(spacing*level)
    return spacing_str.join(line_list)

def defconfig_banner(name):
    """ Generate a category banner for a report """

    break_string = "#----------------------------------------------------------\n"

    return_string = break_string
    name_spaces = int((len(break_string) - len(name))/2)
    return_string += "#" + ' '*name_spaces + name + '\n'
    return_string += break_string
    return return_string

def list_files_by_extension(dir, extension):
    """ List all files in a directory matching a file extension """

    # for each file
    file_list = []
    for filename in os.listdir(dir):
        # match extension
        if filename.endswith(extension) is True:
            file_list.append(os.path.join(dir, filename))

    return file_list

def hex_or_int(value):
    """ Turn a string into integers regardless of format """

    return int(value, 0)

def get_field(value, bit_offset, mask):
    """ Get field based on a  bit offset and mask """

    return (value & mask) >> bit_offset

def set_field(var, bit_offset, mask, value):
    """ Set field based on a  bit offset and mask """

    return ((var & (~mask)) | (((value) << bit_offset) & (mask)))
