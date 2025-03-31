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


# Local
from libconfig.types.base_config_obj  import BaseConfigObj
from libconfig.types.eval_expressions import EvalExpressions
from libconfig.lib_config import LibConfig

class Default(BaseConfigObj):
    """ Represents an config default"""

    def __init__(self, value):
        super().__init__("Default")
        self.value = value

    def __str__(self):
        """ Generate a string with the value """

        return str(self.value)

    def set_value(self, value):
        """ Set default value """

        self.value = value

    def get_value(self):
        """ Get default value """

        return self.value

    def is_never_supported(self):
        """ Check if the the depends condition is impossible
            returns True or False """

        for depend in self.depends:
            if '@' in depend:
                return False
            if '{' in depend:
                return False
            rslt = EvalExpressions.evaluate_to_int(depend, None)
            if rslt == 0:
                return True
        return False

    def modify_param(self, param_name, idx):
        """ Modify a default object based on a parameter """

        param_tag = '{' + param_name + '}'
        idx_str = str(idx)

        # modify value
        if (isinstance(self.value, str) is True):
            self.value = self.value.replace(param_tag, idx_str)

        # modify depends
        expand_depends = []
        for depend in self.depends:
            expand_depends.append(depend.replace(param_tag, idx_str))
        self.depends = expand_depends
