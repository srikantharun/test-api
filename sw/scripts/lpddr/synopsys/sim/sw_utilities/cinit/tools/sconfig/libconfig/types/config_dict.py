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


from libconfig.types.category import Category
from libconfig.types.config import Config

class ConfigDict(Category):
    def __init__(self, name):
        super().__init__(name)
        self.configs_dict = {}

    def add(self, name, type, value):
        """ Add - function to behave like a python dict """

        config = Config(name=name, static=True)
        config.set_id(name)
        config.set_type(type)
        config.set_value(value)
        self.add_child_config(config)

        self.configs_dict[name] = config

    def get(self, name):
        """ Get - function to behave like a python dict """

        return self.configs_dict.get(name)

    def list(self):
        """ List - function to behave like a python dict """

        return self.configs_dict.values()

    def is_config_available(self, config_name):
        """ Check if is config available
            return True or False """

        return config_name in self.configs_dict

    def __str__(self):
        """Overwrite parent method
           generate a string with the category name and its contents"""

        configs_string = ""
        for config, config_obj in self.configs_dict.items():
            configs_string += str(config_obj)
        return configs_string
