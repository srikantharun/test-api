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
import re
import csv
from argparse import ArgumentTypeError

# Local
from libconfig.types.register_field import Field
from libconfig.types.register       import Register
from libconfig.types.register_block import RegisterBlock
from libconfig.types.register_map   import RegisterMap
from libconfig.types.eval_expressions import EvalExpressions
import input_modules.reg_map_rules_parser as reg_map_rules
from libconfig.log import Log


DIR_PATH = os.path.dirname(os.path.realpath(__file__))
REG_RULES_FILE =  os.path.join(DIR_PATH, "module_data", "reg_map_rules.xml")

class RegMapParser():
    cc_const = None

    def __init__(self):
        self.rules = reg_map_rules.RegMapRulesParser(REG_RULES_FILE)

    def parse_reg_map(self, memmap_csv_file, cc_const_dict):
        """ Parse register map csv file """
        register_map = RegisterMap()
        self.cc_const= cc_const_dict
        csv_data    = open(memmap_csv_file, newline='')
        block       = None
        register    = None

        mem_map_reader = csv.DictReader(csv_data)
        for row in mem_map_reader:
            if row["Visible"] is None:
                continue
            block_name      = row["Bank Name"]
            register_name   = row["Register Name"]
            address         = row["Addr"]
            visible         = row["Visible"]
            # convert expression format to python
            visible         = int(self.process_expression(visible))
            visible         = True if visible == 1 else False

            if (block is None) or (block.name != block_name):
                id = "DWC_DDRCTL_CINIT_" + block_name.upper()
                block = RegisterBlock(block_name, id, address)
                rule = self.rules.get_rule(block.get_id())
                if rule is not None:
                    block.add_depends(rule.get_depends())
                register_map.add_register_block(block)

            if (register is None) or (register.name != register_name):
                security = row.get("Access Type", "Non-secure")
                security = re.sub('`', '@', security)  # change format to match the other fields
                security = self.process_expression(security).strip()
                id = "DWC_DDRCTL_CINIT_" + (block_name + '_' + register_name).upper()
                register = Register(name=register_name, id=id, address=address,
                                    security=security, visible=visible)
                rule = self.rules.get_rule(register.get_id())
                if rule is not None:
                    register.add_depends(rule.get_depends())
                block.add_register(register)
                continue

            # read value from row
            field_name  = row["Field Name"]
            offset      = row["Offset"]
            access      = row["Access"]
            field_size  = row["Size"]
            reset_value = row["Reset Value"]
            description = row["Description"]
            field_type  = row["Type"]

            # convert expression format to python
            field_size  = int(self.process_expression(field_size))
            reset_value = int(self.process_expression(reset_value))
            id = "DWC_DDRCTL_CINIT_" + (block_name + '_' + register_name + '_' + field_name).upper()

            if field_size < 0:
                Log().warn("Negative field size for %s (expression: %s)" % (id, row["Size"]))
                field_size = 0

            field = Field(id=id, name=field_name, size=field_size, offset=offset, access=access,
                          field_type=field_type,  default=reset_value, help=description, visible=visible)

            rule = self.rules.get_rule(field.get_id())
            if rule is not None:
                if rule.is_allow() is True:
                    field.force_support()
                else:
                    field.add_depends(rule.get_depends())

            register.add_field(field)

        csv_data.close()
        return register_map


    def process_expression(self, expression):
        """ Transform expressions from memory map format to config tool format """
        expression = expression.replace('\n', ' ')
        expression = expression.replace('\r', ' ')
        expression = expression.replace(" gt ", " > ")
        expression = expression.replace(" lt ", " < ")
        expression = expression.replace("{", "(")
        expression = expression.replace("}", ")")
        expression = expression.replace('Non-secure', '"Non-secure"')
        expression = EvalExpressions.evaluate(expression, self.cc_const)
        return expression

    def validate_file(memmap_csv_file):
        """ Validate register map csv file
            this functions should only be called by argparse while verifying the arguments
            errors must be argparse exceptions"""

        if (os.path.isfile(memmap_csv_file) is False):
            raise ArgumentTypeError("Register map csv file %s not found" % memmap_csv_file)

        with open(memmap_csv_file) as csv_data:
            first_line = csv_data.readline()
            # check first line for the csv field names
            if ("Bank Name,Register Name,Addr" in first_line):
                return memmap_csv_file
            else:
                raise ArgumentTypeError("File %s is not a valid Register map file (Table header doesn't match)" % memmap_csv_file)
