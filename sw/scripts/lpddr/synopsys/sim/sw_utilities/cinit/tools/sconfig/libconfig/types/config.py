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


#Local
import libconfig.utils as utils
from libconfig.types.base_config_obj  import BaseConfigObj
from libconfig.types.option import Option
from libconfig.types.eval_expressions import EvalExpressions
from libconfig.log import Log
from libconfig.lib_config import LibConfig

class Config(BaseConfigObj):
    """ Represents an config """

    def __init__(self, name, static = False):
        super().__init__(name)
        self.id = None
        self.options = []
        self.type = None
        self.defaults = []
        self.value = None
        self.min = None
        self.max = None
        self.hidden = False
        self.line = None
        self.line_no = None

        self.static = static

    def __str__(self):
        """ Generate a string with the config name and its contents """

        return_string = "%s"% (self.name)
        # show all configs
        for option in self.options:
            return_string += "\n" + utils.indent(str(option))

        return return_string

    def report(self):
        """ Generate a string with the config name and its value """

        return "%s: '%s'"% (self.get_name(), self.get_value())

    def is_static(self):
        """ Check if a config is static
            returns True or False """

        return self.static

    def set_static(self):
        """ Set the config as static """

        self.static = True

    def is_hidden(self):
        """ Check if a config is hidden
            returns True or False """

        return self.hidden

    def set_hidden(self):
        """ Set the config as hidden """

        self.hidden = True

    def get_id(self):
        """ Get config ID as a string """

        return self.id

    def set_id(self, id):
        """ Set config ID with a string """

        self.id = id

    def get_type(self):
        """ Get config type as a string """

        return self.type

    def set_type(self, type):
        """ Set config type with a string """

        self.type = type

    def is_str_type(self):
        """ Returns True if the type matches int """
        return (self.type == "str")

    def is_int_type(self):
        """ Returns True if the type matches int """
        return (self.type == "int")

    def get_min(self):
        """ Get config min value as a int or None """

        if isinstance(self.min, str):
            return  EvalExpressions.evaluate_to_int(self.min, LibConfig().get_config_dict())
        return self.min

    def set_min(self, min):
        """ Set config min """

        self.min = min

    def get_max(self):
        """ Get config max value as a int or None """

        if isinstance(self.max, str):
            return EvalExpressions.evaluate_to_int(self.max, LibConfig().get_config_dict())
        return self.max

    def set_max(self, max):
        """ Set config max """

        self.max = max


    def get_default(self):
        """ Get config default
            if the default can be resolved return value
            if it cannot return a list with the default objects """

        if (len(self.defaults)==0):
            raise utils.LibConfigError("Config has no default: %s"%self.name)

        default_value = self.eval_default()

        # evaluate default value
        default_value = EvalExpressions.evaluate(default_value, LibConfig().get_config_dict())

        return default_value

    def eval_default(self):
        """ Evaluate default based of their dependencies
            returns default value
            raises and exception if multiple defaults are valid simultaneously """

        valid_default_values = []
        for default in self.defaults:
            if (default.is_supported() is True):
                valid_default_values.append(default.get_value())

        if (len(valid_default_values) == 1):
            return valid_default_values[0]

        # Error case: Raise a clear Exception
        if (len(valid_default_values) == 0):
            error_msg = "Config has no valid default: '%s'\n" % (self.name)
        elif (len(valid_default_values) > 1):
            error_msg = "Config has more than one valid default: '%s'\n" % (self.name)

        for default in self.defaults:
            error_msg += "default: " + str(default.get_value()) + ': dependency: \'' + default.get_depends() + '\'\n'
        raise utils.LibConfigError(error_msg)

    def list_defaults(self):
        """ Returns a list with the default objects """

        return self.defaults

    def has_default(self):
        """ Check if the config has defaults
            returns True or False """

        if (len(self.defaults) > 0):
            return True
        else:
            return False

    def has_multiple_default(self):
        """ Check if the config has multiple defaults
            returns True or False """

        if (len(self.defaults) == 1):
            return False
        else:
            return True

    def add_default(self, default):
        """ Add a default object to this config """
        self.defaults.append(default)

    def has_options(self):
        """ Check if the config has options
            returns True or False """

        if (len(self.options) > 0):
            return True
        else:
            return False

    def find_option_by_id(self, id):
        """ Find the config option that matches a id
            returns None if there is no match """

        if (self.has_options()):
            for option in self.options:
                if (id == option.get_id()):
                    return option
        return None

    def find_option_by_value(self, value):
        """ Find the config option that matches a value
            returns None if there is no match """

        if (self.has_options()):
            for option in self.options:
                if (value == option.get_value()):
                    return option
        return None

    def list_options(self):
        """ Returns a list with the configs options """

        return self.options

    def add_options(self, options):
        """ Add a list of option objects to this config """

        for option in options:
            self.add_option(option)

    def add_option(self, option):
        """ Add a option object to this config """

        option.set_parent(self)
        self.options.append(option)

    def is_value_set(self):
        """ Check if the configs value has been explicitly set
            returns True or False """

        if ((self.value is None) or (self.is_static() is True)):
            return False
        return True

    def is_value_valid(self, value):
        """ Check if the configs value is valid according to the current configuration
            returns True or False """

        # validate the option
        if (isinstance(value, Option) is True):
            if (value.is_supported() is False):
                Log().error("Invalid value %s for config %s" % (value.get_name(), self.get_name()))
                self._log_config_line()
                return False

        # validate the value of ints
        if (self.is_int_type() is True):
            if (isinstance(value, int) is False):
                Log().error("Parameter must be set with integer %s %s" % (value, type(value)))
                return False

            if (value < self.get_min()):
                Log().error("Invalid value %d for config %s minium %d" % (value, self.get_name(), self.get_min()))
                self._log_config_line()
                return False

            if (value > self.get_max()):
                Log().error("Invalid value %d for config %s maximum %d" % (value, self.get_name(), self.get_max()))
                self._log_config_line()
                return False

        # validate the length of strings
        if (self.is_str_type() is True):
            if (isinstance(value, str) is False):
                Log().error("Parameter must be set with string %s %s" % (value, type(value)))
                return False

            if (len(value) < self.get_min()):
                Log().error("Invalid value %s for config %s minium length %d" % (value, self.get_name(), self.get_min()))
                self._log_config_line()
                return False

            if (self.get_max() is not None):
                if (len(value) > self.get_max()):
                    Log().error("Invalid value %s for config %s maximum length %d" % (value, self.get_name(), self.get_max()))
                    self._log_config_line()
                    return False

        return True

    def set_value(self, value, line=None, line_no=None):
        """ Set the config value
            value should be an int, the ID of an option or the value of an option """

        self.value = value

        # store the ine used to configure this value
        self.line = line
        self.line_no = line_no

        if ((value == False) or (value == 'False')):
            self.value = 0
        elif ((value == True) or (value == 'True')):
            self.value = 1

        if ((isinstance(value, str) is True) and (self.has_options() is True)):
            for option in self.list_options():
                if ((option.get_id() is not None) and (value == option.get_id())):
                    self.value = option.get_value()

    def get_value(self):
        """ Get the config value
            returns value as a string, int or as an option object """

        if (self.value is None):
            return self.get_default()
        return self.value


    def is_supported(self, static_only=False):
        """ Check if the config is supported based on the current configuration
            returns True or False """
        rslt = super().is_supported(static_only=static_only)

        if (rslt is False) and (self.value is not None):
            Log().error("%s set but invalid" % (self.get_id()))
            self._log_config_line()

        if self.is_value_set() is True:
            if (self.is_value_valid(self.value) is False):
                rslt = False

        return rslt

    def _log_config_line(self):
        """ report how the parameter was set """
        if (self.line is not None):
            Log().error("Parameter set in line %d with '%s'" % (self.line_no, self.line))

    def modify_param(self, param_name, idx, param_depends):
        """ Modify a config based on a parameter """

        param_tag = '{' + param_name + '}'
        idx_str = str(idx)

        # modify name
        self.name = self.name.replace(param_tag, idx_str)

        # modify id
        if (self.id is not None):
            self.id = self.id.replace(param_tag, idx_str)

        # modify depends
        expand_depends = []
        for depend in self.depends:
            expand_depends.append(depend.replace(param_tag, idx_str))
        self.depends = expand_depends

        # modify help
        if(self.help is not None):
            self.help = self.help.replace(param_tag, idx_str)

        # modify options
        for option in self.options:
            option.modify_param(param_name, idx, param_depends)

        # modify defaults
        for default in self.defaults:
            default.modify_param(param_name, idx)

        # remove defaults that are never supported
        # use a copy of the list so that all elements are processed as we remove them from the original list
        for default in self.defaults[:]:
            # Check if depends does not contain references to other params
            if (default.get_depends() is not None) and ('{' not in default.get_depends()):
                if (default.is_never_supported() is True):
                    self.defaults.remove(default)
