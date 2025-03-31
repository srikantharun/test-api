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

class Option(BaseConfigObj):
    """ Represents an config option"""

    def __init__(self, id, name, value, depends):
        super().__init__(name)
        self.id = id
        self.add_depends(depends)
        if ((isinstance(value, str) is True) and (value.isnumeric() is True)):
            self.value = int(value)
        else:
            self.value = value

    def __str__(self):
        """ Generate a string with the option name """

        return "%s"% (self.name)

    def get_id(self):
        """ Get option ID as a string """

        return self.id
    
    def is_static(self):
        """ Options ara always static
            value does not change """

        return True

    def has_value(self):
        """ Check if the option has an enum value
            returns True or False """
        if (self.value is not None):
            return True
        else:
            return False

    def is_set(self):
        """ Check if the parent config is set to this option
            returns True or False """

        return self.parent.get_value() == self.get_value()

    def get_value(self):
        """ Get the option value in the parent option enum """

        return self.value


    def modify_param(self, param_name, idx, param_depends):
        """ Modify a option based on a parameter """

        param_tag = '{' + param_name + '}'
        idx_str = str(idx)

        # modify name
        self.name = self.name.replace(param_tag, idx_str)

        # modify id
        self.id = self.id.replace(param_tag, idx_str)

        # modify depends
        expand_depends = []
        for depend in self.depends:
            expand_depends.append(depend.replace(param_tag, idx_str))
        self.depends = expand_depends
