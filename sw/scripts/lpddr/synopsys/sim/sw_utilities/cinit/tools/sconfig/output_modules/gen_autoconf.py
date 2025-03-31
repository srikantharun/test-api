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
import sys
import re

from libconfig.lib_config import LibConfig

class GenAutoConf():

    def gen_header(path):
        """ Generate configuration header """

        lib_config = LibConfig()
        config_db = lib_config.list_parameters()

        with open(path, 'w') as f:
            for config in config_db:

                if ((config.is_supported() is True) and (config.is_static() is False)):
                    f.write(GenAutoConf.get_header_assign_config(config))

    def get_header_assign_config(config):
        """ Generate lines in the format of a C header """

        ret_str = ''
        value = config.get_value()

        # hide False configs of bool type
        if ((config.type == 'bool') and (value == 0)):
            return ''

        if (config.get_id() is not None):
            ret_str += "#define %s %s\n"% (config.get_id(), value)

        if (config.has_options()):
            option = config.find_option_by_value(value)
            ret_str += "#define %s 1\n"% (option.get_id())

        return ret_str
