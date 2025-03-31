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
import copy
import argparse
from lxml import etree
from enum import Enum

from libconfig.types.category import Category
from libconfig.types.config import Config
from libconfig.types.option import Option
from libconfig.types.default import Default
import libconfig.utils as utils
from libconfig.log import Log

DIR_PATH = os.path.dirname(os.path.realpath(__file__))
SCHEMA_DIR =  os.path.join(DIR_PATH, "module_data")
SCHEMA_FILE_NAME = "CINIT_config_schema.xsd"

class ConfigDBParserError(Exception):
    def __init__(self, message):
        super().__init__(message)

class ConfigDBParser():

    def __init__(self, schema_check=True):
        self.schema_check = schema_check

        if (self.schema_check is True):
            self.xml_schema_file = os.path.join(SCHEMA_DIR, SCHEMA_FILE_NAME)

            with open(self.xml_schema_file) as xml_schema:
                parsed_xml_schema = etree.parse(xml_schema)
                self.xml_schema_obj = etree.XMLSchema(parsed_xml_schema)

    def _transform_expression(self, expression):
        """ Transform expressions from the database format to config tool format """

        # Convert gt and lt to > and < to allow expression evaluation
        expression = expression.replace("gt", " > ")
        expression = expression.replace("lt", " < ")

        return expression

    def validate_xml_files(self, element_tree, db_config_path):
        """ Validate xml files against schema """

        if (self.schema_check is True):
            try:
                self.xml_schema_obj.assertValid(element_tree)
            except Exception as err:
                Log().error("Invalid xml database file: {0}\n{1}".format(db_config_path, err))
                sys.exit(utils.EXIT_ERROR)

    def parse_xml_files(self, db_config_paths):
        """ Parse all xml files in a list of paths """

        if (len(db_config_paths) == 0):
            arg_parser.error('No configuration db found in %s ' % db_dir)
            sys.exit(utils.EXIT_ERROR)

        config_list = []
        for db_config_path in db_config_paths:
            config_list += self.parse_xml_file(db_config_path)
        return config_list

    def parse_xml_file(self, db_config_path):
        """ Parse a xml file and storing the data at the root of the config tree """

        config_tree = etree.parse(db_config_path)
        self.validate_xml_files(config_tree, db_config_path)

        return self.load_category_from_xml_tree(config_tree.getroot())

    def load_category_from_xml_tree(self, category_xml):
        """ Load category data from an xml object """

        # name
        name = category_xml.attrib['name']
        category = Category(name)

        # help
        help_xml = category_xml.find('help')
        if (help_xml is not None):
            category.set_help(help_xml.text)

        # get depends
        if 'depends' in category_xml.attrib:
            depends = category_xml.attrib['depends']
            category.add_depends(self._transform_expression(depends))

        # categories
        for child_category_xml in category_xml.findall('./category'):
            config_list = self.load_category_from_xml_tree(child_category_xml)
            category.add_child_categories(config_list)

        # configs
        for config_xml in category_xml.findall('./config'):
            config_list = self.load_config_from_xml_tree(config_xml)
            category.add_child_configs(config_list)

        # param
        # note parse last
        param_xmls = category_xml.findall('param')
        if (len(param_xmls) > 0):
            return self.itemize_category(param_xmls, category)
        else:
            return [category]

    def load_config_from_xml_tree(self, config_xml):
        """ Load config data from an xml object """

        # name
        name = config_xml.attrib['name']
        config = Config(name)

        # help
        help_xml = config_xml.find('help')
        if (help_xml is not None):
            config.set_help(help_xml.text)

        # id
        if 'id' in config_xml.attrib:
            config.set_id(config_xml.attrib['id'])

        # type
        config.set_type(config_xml.attrib['type'])

        # var type
        var_type = config_xml.attrib['var_type']
        if var_type is None:
            raise ConfigDBParserError("Parameter has no var type '%s'" % name)
        var_type = VarType(var_type)

        # min
        if 'min' in config_xml.attrib:
            config.set_min(config_xml.attrib['min'])
        else:
            config.set_min(var_type.get_min())

        # max
        if 'max' in config_xml.attrib:
            config.set_max(config_xml.attrib['max'])
        else:
            config.set_max(var_type.get_max())

        # get depends
        if 'depends' in config_xml.attrib:
            depends = config_xml.attrib['depends']
            config.add_depends(self._transform_expression(depends))

        # static
        if ('static' in config_xml.attrib) and \
           (config_xml.attrib['static'] == "True"):
            config.set_static()

        # hidden
        if ('hidden' in config_xml.attrib) and \
           (config_xml.attrib['hidden'] == "True"):
            config.set_hidden()

        # get option
        for option_xml in config_xml.findall('./option'):
            option = self.load_option_from_xml_tree(option_xml)
            config.add_option(option)

        # get default
        for default_xml in config_xml.findall('./default'):
            default = self.load_default_from_xml_tree(default_xml)
            config.add_default(default)

        # param
        # note parse last
        param_xmls = config_xml.findall('param')
        if (len(param_xmls) > 0):
            return self.itemize_config(param_xmls, config)
        else:
            return [config]

    def load_option_from_xml_tree(self, option_xml):
        """ Load option data from an xml object """
        name    = option_xml.attrib['name']
        opt_id  = option_xml.attrib['id']
        value   = option_xml.get('value', None)
        depends = option_xml.get('depends', None)
        if depends is not None:
            depends = self._transform_expression(depends)

        option  = Option(id=opt_id, name=name, value=value, depends=depends)
        return option

    def load_default_from_xml_tree(self, default_xml):
        """ Load default data from an xml object """

        # value
        value = default_xml.attrib['value']
        value = self._transform_expression(value)
        default = Default(value)
        # get depends
        if 'depends' in default_xml.attrib:
            depends = default_xml.attrib['depends']
            default.add_depends(self._transform_expression(depends))
        return default

    def load_param_from_xml_tree(self, param_xml):
        """ Load param data from an xml object """

        param_name = param_xml.attrib['name']
        param_min = int(param_xml.attrib['min'])
        param_max = int(param_xml.attrib['max'])
        if 'step' in param_xml.attrib:
            param_step = int(param_xml.attrib['step'])
        else:
            param_step = 1

        if 'depends' in param_xml.attrib:
            param_depends = self._transform_expression(param_xml.attrib['depends'])
        else:
            param_depends = None

        return param_name, param_min, param_max, param_step, param_depends

    def itemize_category(self, param_xmls, category):
        """ Turn one category with parameters into many items """

        category_list = [category]
        for param_xml in param_xmls:
            # for each param det param data
            param_name, param_min, param_max, param_step, param_depends = self.load_param_from_xml_tree(param_xml)

            new_category_list=[]
            for category_elem in category_list:
                for i in range(param_min, param_max+1, param_step):
                    category_copy = copy.deepcopy(category_elem)

                    category_copy.modify_param(param_name, i, param_depends)
                    new_category_list.append(category_copy)

            # replace last list with the new list
            category_list = new_category_list

        return category_list

    def itemize_config(self, param_xmls, config):
        """ Turn one config with parameters into many items """

        config_list = [config]
        for param_xml in param_xmls:
            # for each param det param data
            param_name, param_min, param_max, param_step, param_depends = self.load_param_from_xml_tree(param_xml)

            new_config_list=[]
            for config_elem in config_list:
                for i in range(param_min, param_max+1, param_step):
                    config_copy = copy.deepcopy(config_elem)
                    config_copy.modify_param(param_name, i, param_depends)
                    new_config_list.append(config_copy)

            # replace last list with the new list
            config_list = new_config_list

        return config_list

class VarType(str, Enum):
    """ Enum class that defines all Protocol types supported """
    INT8   = "int8"
    UINT8  = "uint8"
    INT16  = "int16"
    UINT16 = "uint16"
    INT32  = "int32"
    UINT32 = "uint32"
    INT64  = "int64"
    UINT64 = "uint64"
    STRING = "str"

    def __str__(self):
        """ Returns how the object should be present to the user has a string """
        return f'{self.name.lower()}'

    def __repr__(self):
        """ Returns how the object should be represented """
        return str(self)

    def get_max(self):
        """ Returns max value supported for the type """
        max_dict = {"int8"  : 127,
                    "uint8" : 255,
                    "int16" : 32767,
                    "uint16": 65535,
                    "int32" : 2147483647,
                    "uint32": 4294967295,
                    "int64" : 9223372036854775807,
                    "uint64": 18446744073709551615,
                    "str"   : None}

        return max_dict[self]

    def get_min(self):
        """ Returns min value supported for the type """
        min_dict = {"int8"  : -128,
                    "uint8" : 0,
                    "int16" : -32768,
                    "uint16": 0,
                    "int32" : -2147483648,
                    "uint32": 0,
                    "int64" : -9223372036854775808,
                    "uint64": 0,
                    "str"   : 0}

        return min_dict[self]
