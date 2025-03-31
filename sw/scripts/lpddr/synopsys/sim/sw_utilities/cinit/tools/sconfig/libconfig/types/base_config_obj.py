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
from libconfig.types.eval_expressions import EvalExpressions
import libconfig.lib_config as lib_config

class BaseConfigObj():
    """ Base config object """

    def __init__(self, name):
        self.name      = name
        self.parent    = None
        self.help      = None
        self.depends   = []

    def __str__(self):
        """ Generate a string representing the configuration """
        return self.name

    def get_name(self):
        """ Get name as a string """
        return self.name

    def get_parent(self):
        """ Get the parent object """
        return self.parent

    def set_parent(self, parent):
        """ Set the parent object """
        self.parent = parent

    def get_help(self):
        """ Get help as a string """
        return self.help

    def set_help(self, help):
        """ Set help multiline string """
        self.help = help

    def get_depends(self):
        """ Get dependencies as a string """
        depends_list = []
        if self.parent is not None:
            parent_depends = self.parent.get_depends()
            if parent_depends is not None:
                depends_list.append(parent_depends)
            
        if len(self.depends) > 0:
            depends_list += self.depends

        if len(depends_list) == 0:
            return None

        depend_str = ""
        for depend in depends_list:
            if len(depend_str) > 0:
                depend_str = "(" + depend_str + ") and (" + depend + ")"
            else:
                depend_str += depend
        return depend_str

    def add_depends(self, depends):
        """ Add category dependencies """
        if depends is not None:
            self.depends.append(depends)

    def is_supported(self, static_only=False):
        """ Check if the config is supported based on the current configuration
            returns True or False """
        result = True
        if self.parent is not None:
            if self.parent.is_supported(static_only=static_only) is False:
                return False

        for depend in self.depends:
            # in static_only mode treat parameters that cannot be solver with static parameters as supported
            if static_only is True:
                result = EvalExpressions.evaluate(depend, lib_config.LibConfig().get_config_dict(), static_only=True)
                if (isinstance(result, str) is True) and ('@' in result):
                    return True

            result = EvalExpressions.evaluate_to_int(depend, lib_config.LibConfig().get_config_dict())
            if result != 1:
                return False
        return True

