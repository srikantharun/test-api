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

import libconfig.utils as utils
from libconfig.lib_config import LibConfig

class GenDefconfig():

    def gen_defconfig(defconfig_path, show_only_set=True):
        """ Generate configuration defconfig """

        # Get root category
        root_category =  LibConfig().get_config_db()

        # generate defconfig data for the root category
        defconfig_data = GenDefconfig.defconfig_category(root_category, show_only_set)

        with open(defconfig_path,'w') as defconfig_file:
            #write data to file
            defconfig_file.write(defconfig_data)

    def defconfig_category(category, show_only_set):
        """ Returns a multiline string with the name, help and the contents of the category """

        return_string = utils.defconfig_banner(category.name)

        if(category.help is not None):
            return_string += '#  help:\n'
            for line in category.help.split('\n'):
                if(line != ''):
                    return_string += '#  %s\n'%(line)

        # show all configs
        for child in category.child_configs:
            if (child.is_static() is False):
                if ((show_only_set is False) or (child.is_value_set() is True)):
                    return_string += GenDefconfig.defconfig_config(child, show_only_set) + "\n"

        # show all categories
        for child in category.child_categories:
            if ((show_only_set is False) or (child.has_set_configs() is True)):
                return_string += "\n\n" + GenDefconfig.defconfig_category(child, show_only_set)

        return return_string

    def defconfig_config(config, show_only_set):
        """ Returns a multiline string with the name, help and the contents of the config """
        # Name
        return_string = '\n'
        return_string += GenDefconfig._line_entry('Config', config.get_name())
        if (config.get_id() is not None):
            return_string += GenDefconfig._line_entry('Identifier', config.get_id())
        return_string += GenDefconfig._line_entry('Category', config.parent.name)

        # Dependencies
        if (config.get_depends() is not None):
            return_string += GenDefconfig._line_entry('Dependencies', None)
            return_string += GenDefconfig._line_entry('- Requires', config.get_depends())

        # Default
        return_string += GenDefconfig.defconfig_defaults(config.list_defaults())

        # Options
        if (config.has_options() is True):
            return_string += GenDefconfig.defconfig_options(config.list_options(), show_only_set)
        else:
            # value
            if (config.get_id() is not None):
                if ((show_only_set is True) and (config.is_value_set() is True)):
                    return_string += '%s=%s\n'%(config.get_id(), config.get_value())
                else:
                    return_string += '#%s=<value>\n'%(config.get_id())

        return return_string

    def defconfig_defaults(defaults, spaces=24):
        """ Returns a string with the value and depends if available """
        defaults_string = ""
        start_line_str = "%-*s" % (spaces, "#  Default: ")
        for default in defaults:
            value = default.get_value()
            if isinstance(value, int):
                value = str(value)
            else:
                value = value.replace('@', '')
            defaults_string += start_line_str + value
            # Add condition
            if default.get_depends() is not None:
                depends = default.get_depends().replace('@', '')
                defaults_string += ' if %s' % (depends)
            defaults_string += '\n'
            start_line_str = "%-*s" % (spaces, "#")
        return defaults_string

    def defconfig_options(options, show_only_set):
        """ Returns a string with the value and depends if available """

        return_string  =''

        #get largest id
        max_spaces = max([len(a.get_id()) for a in options])

        for option in options:
            if (option.is_set() is False) or (show_only_set is False):
                return_string += '#'

            spaces = max_spaces + 2 - len(option.get_id())
            return_string += '%s=y  %s#%s\n'%(option.get_id(), ' ' * spaces, option.get_name())

        return return_string

    def _line_entry(key, value, spaces=20):
        """ Util used to generate a line for descriptor comment used in defconfigs """

        spaces = spaces-len(key)

        if (value is None):
            value = ''
            spaces = 0
        return '#  %s:%s%s\n'%(key, ' '*spaces, value)
