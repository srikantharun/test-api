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
from libconfig.types.category import Category


class RegisterMap(Category):
    def __init__(self):
        super().__init__("Register control")
        self.reg_block_addr_dict = {}
        self.reg_block_name_dict = {}

    def add_register_block(self, block):
        """ Add register block to the register map """
        self.add_child_category(block)
        self.reg_block_addr_dict[block.address] = block
        self.reg_block_name_dict[block.name]    = block

    def get_register_block_by_name(self, name):
        """ Get a block in this register map that matches a given name """
        return self.reg_block_name_dict.get(name)

    def get_register_block_by_addr(self, address):
        """ Get a block in this register map that matches a given address """
        return self.reg_block_addr_dict.get(address & 0xFFFFF000)

    def __str__(self):
        """ Generate a string with the register map address and name and its contents """

        output = ""
        for addr in sorted(self.reg_block_addr_dict.keys()):
            reg_block = self.get_register_block_by_addr(addr)
            output +=  "%s\n" % reg_block
        return output
