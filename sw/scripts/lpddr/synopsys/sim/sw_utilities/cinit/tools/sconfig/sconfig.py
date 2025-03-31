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
import argparse

import libconfig.utils as utils
from libconfig.log import Log, LogLevel
from libconfig.lib_config import LibConfig
from output_modules.gen_html_doc import GenHTMLDoc
from output_modules.gen_autoconf import GenAutoConf
from output_modules.gen_reg_table import GenRegistersTable
from output_modules.gen_defconfig import GenDefconfig

from input_modules.defconfig_parser import DefconfigParser
from input_modules.xml_db_parser import ConfigDBParser
from input_modules.c_header_parser import CHeaderParser
from input_modules.reg_map_parser import RegMapParser

class SConfigTool():
    SCONFIG_VERSION = "1.00a-ea01"
    DIR_PATH = os.path.dirname(os.path.realpath(__file__))
    CONFIGS_DB = DIR_PATH + '/db_config'
    cc_const_db = None
    reg_configs = None

    def __init__(self, cc_constants_list, memmap_csv_file):
        db_config_paths = utils.list_files_by_extension(self.CONFIGS_DB, '.xml')
        self.lib_config = LibConfig()

        self.load_db_config(db_config_paths)
        self.load_cc_const(cc_constants_list)
        self.load_reg_configs(memmap_csv_file)

        # create index
        self.lib_config.index_config_db()

    @staticmethod
    def get_version():
        return SConfigTool.SCONFIG_VERSION

    def list_available(self, output_file):
        """ List all available configs in the format of a report """

        GenDefconfig.gen_defconfig(output_file, show_only_set=False)

    def gen_html_doc(self, output_dir, show_all):
        """ Generate html documentation """

        self.gen_doc_obj = GenHTMLDoc()
        self.gen_doc_obj.gen_doc(output_dir, show_all)

    def gen_conf_header(self, defconfig_file, output_file, report_file=None):
        """ Generate a C header with all configuration parameters """

        DefconfigParser().load_defconfig(defconfig_file)

        if (report_file is None):
            report_file = output_file + '_report'
        GenDefconfig.gen_defconfig(report_file, show_only_set=True)

        GenAutoConf.gen_header(output_file)
        print("Successfully generated: %s" % output_file)

    def print_reg_map(self):
        """ Print a list of all registers and their fields with addresses and defaults """
        print(self.reg_configs)

    def gen_c_reg_map(self, output_dir):
        """ Generates the register table in the folder defined """
        gen_reg = GenRegistersTable(self.reg_configs)
        gen_reg.gen_c_reg_map(output_dir)

    def load_db_config(self, db_config_paths):
        """ Load configuration database """

        # load config data from xml file
        config_list = ConfigDBParser().parse_xml_files(db_config_paths)
        # add configs to database
        self.lib_config.db_config.add_child_categories(config_list)

    def load_cc_const(self, cc_constants_list):
        """ Load HW configuration form cc constants """

        self.cc_const_db = CHeaderParser.parse_c_headers(cc_constants_list, "CC Constants")
        self.lib_config.add_category(self.cc_const_db)

    def load_reg_configs(self, memmap_csv_file):
        """ Load register map configurations """
        reg_map_parser = RegMapParser()
        self.reg_configs = reg_map_parser.parse_reg_map(memmap_csv_file, self.cc_const_db)
        self.lib_config.add_category(self.reg_configs)


if __name__ == "__main__":
    defconfig_file = None
    output_file = None
    report_file = None

    arg_parser = argparse.ArgumentParser()

    # Add arguments
    arg_parser.add_argument("-c", "--cc_constants",        dest='cc_constants',     type=CHeaderParser.validate_file_cc_constants,
                            nargs='+', help="DDR controller cc_constants configuration header")
    arg_parser.add_argument("-m", "--memmap_csv",          dest='memmap_csv_file',  type=RegMapParser.validate_file,
                            help="Memory map register definition CSV file")
    arg_parser.add_argument("-d", "--defconfig",           dest='defconfig_file',   type=DefconfigParser.validate_file,
                            help="Import configuration from defconfig file")
    arg_parser.add_argument("-o", "--output",              dest='output',           type=str,
                            help="Output folder/file")
    arg_parser.add_argument("-r", "--report",              dest='report_file',      type=str,
                            help="Configuration report file")
    arg_parser.add_argument("--show_all",                 action='store_true',
                            help="show all parameters in documentation")

    # add program name used to call the application to the log
    Log().cfg(prefix = "%s :" % arg_parser.prog, level = LogLevel.INFO)

    # add mutually exclusive options
    excl = arg_parser.add_mutually_exclusive_group(required=True)
    excl.add_argument("--list_available",      action='store_true',
                      help="List available configuration options")

    excl.add_argument("--gen_config_header",   action='store_true',
                      help="Generate C configuration header")

    excl.add_argument("--gen_html_doc",        action='store_true',
                       help="Generate HTML documentation")

    excl.add_argument("--print_reg_map",       action='store_true',
                      help="Show register default values")

    excl.add_argument("--gen_c_reg_map", action='store_true',
                      help="Generate Register Map in C code")

    excl.add_argument("-v", "--version",       dest='version',  action='store_true', help="Print version")

    parsed_args = arg_parser.parse_args()

    if parsed_args.version is True:
        print("Version: " + SConfigTool.get_version())
        exit(utils.EXIT_SUCCESS)

    # CC constants file and Register Map is always required
    if parsed_args.cc_constants is None:
        arg_parser.error("CC constants file not defined")
    for cc_constant in parsed_args.cc_constants:
        if (os.path.isfile(cc_constant) is False):
            arg_parser.error("DDRCTL CC constants file \"%s\" not found" % cc_constant)

    if parsed_args.memmap_csv_file is None:
        arg_parser.error("Memory map register file not defined")
    if (os.path.isfile(parsed_args.memmap_csv_file) is False):
        arg_parser.error("Memory map register file \"%s\" not found" % parsed_args.memmap_csv_file)

    if parsed_args.output is not None:
        # test output_dir if output is set
        output_dir = os.path.dirname(os.path.abspath(parsed_args.output))
        if os.path.isdir(output_dir) is False:
            arg_parser.error("Output directory \"%s\" not found" % output_dir)

    config_tool = SConfigTool(parsed_args.cc_constants, parsed_args.memmap_csv_file)

    if (parsed_args.list_available is True):
        if parsed_args.output is None:
            arg_parser.error("Output not defined")
        config_tool.list_available(parsed_args.output)
        exit(utils.EXIT_SUCCESS)

    if (parsed_args.gen_html_doc is True):
        if parsed_args.output is None:
            arg_parser.error("Output not defined")
        config_tool.gen_html_doc(parsed_args.output, parsed_args.show_all)
        exit(utils.EXIT_SUCCESS)

    if (parsed_args.print_reg_map is True):
        config_tool.print_reg_map()
        exit(utils.EXIT_SUCCESS)

    if parsed_args.gen_c_reg_map is True:
        if parsed_args.output is None:
            arg_parser.error("Output not defined")
        config_tool.gen_c_reg_map(parsed_args.output)
        exit(utils.EXIT_SUCCESS)

    if (parsed_args.gen_config_header is True):
        if parsed_args.defconfig_file is None:
            arg_parser.error("Defconfig file not defined")

        if os.path.isfile(parsed_args.defconfig_file) is False:
            arg_parser.error("Defconfig file \"%s\" not found" % parsed_args.defconfig_file)

        if parsed_args.output is None:
            arg_parser.error("Output not defined")

        if parsed_args.report_file is not None:
            report_dir = os.path.dirname(os.path.abspath(parsed_args.report_file))
            if os.path.isdir(report_dir) is False:
                arg_parser.error("Report file path not valid \"%s\"" % report_dir)

        config_tool.gen_conf_header(parsed_args.defconfig_file, parsed_args.output, parsed_args.report_file)
        exit(utils.EXIT_SUCCESS)

    arg_parser.print_help()
