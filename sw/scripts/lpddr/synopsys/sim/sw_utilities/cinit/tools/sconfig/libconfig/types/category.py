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

import libconfig.utils      as utils
from libconfig.types.base_config_obj  import BaseConfigObj


class Category(BaseConfigObj):
    """ Represents a collection of configs """

    def __init__(self, name):
        super().__init__(name)
        self.child_categories = []
        self.child_configs = []

    def __str__(self):
        """ Generate a string with the category name and its contents """

        return_string = "%s"%(self.name)

        # show all categories
        for child in self.child_categories:
            return_string += "\n" + utils.indent(str(child))

        # show all configs
        for child in self.child_configs:
            return_string += "\n" + utils.indent(str(child))

        return return_string

    def has_set_configs(self):
        """ check if the there are configs within this category which are set """

        # check all configs
        for child in self.child_configs:
            if (child.is_value_set() is True):
                return True

        # check all categories
        for child in self.child_categories:
            if (child.has_set_configs() is True):
                return True

        return False

    def list_child_categories(self):
        """ List the categories directly under this category """

        return self.child_categories

    def add_child_categories(self, child_categories):
        """ Add a list of child categories to this category """

        for child_category in child_categories:
            self.add_child_category(child_category)

    def add_child_category(self, child_category):
        """ Add a child category to this category """

        child_category.set_parent(self)
        self.child_categories.append(child_category)

    def list_child_configs(self):
        """ List the configs directly under this category """

        return self.child_configs

    def add_child_configs(self, child_configs):
        """ Add a list of child configs to this category """

        for child_config in child_configs:
            self.add_child_config(child_config)

    def add_child_config(self, child_config):
        """ Add a child config to this category """

        child_config.set_parent(self)
        self.child_configs.append(child_config)

    def modify_param(self, param_name, idx, param_depends):
        """ Modify a category based on a parameter """

        param_tag = '{' + param_name + '}'
        idx_str = str(idx)

        # modify name
        self.name = self.name.replace(param_tag, idx_str)

        # modify depends
        expand_depends = []
        for depend in self.depends:
            expand_depends.append(depend.replace(param_tag, idx_str))
        self.depends = expand_depends

        # modify help
        if(self.help is not None):
            self.help = self.help.replace(param_tag, idx_str)

        # modify category
        for sub_category in self.child_categories:
            sub_category.modify_param(param_name, idx, param_depends)

        # modify config
        for sub_config in self.child_configs:
            sub_config.modify_param(param_name, idx, param_depends)
