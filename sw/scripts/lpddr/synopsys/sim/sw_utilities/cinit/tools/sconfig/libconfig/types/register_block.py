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


# System
from enum import Enum

# Local
import libconfig.utils as utils
from libconfig.types.category import Category


class RegisterBlockType(Enum):
    """ Enum class that defines all register block types """
    FREQ        = "REGB_FREQ"
    DDRC        = "REGB_DDRC"
    ARB_PORT    = "REGB_ARB_PORT"
    ADDR_MAP    = "REGB_ADDR_MAP"
    IME         = "REGB_IME"

    def __str__(self):
        """ Override string implementation """
        return "%s" % self.value.lower()

    def __repr__(self):
        """ Override repr implementation """
        return str(self)

    def find_type(block_name):
        """ Return the Register block type based on block name """
        for block_type in RegisterBlockType:
            if block_type.value in block_name:
                return block_type
        return None


class RegisterBlock(Category):
    def __init__(self, name, id, address):

        super().__init__(name)
        self.id                 = id
        self.address = utils.hex_or_int(address) & 0xFFFFFF00 # All register blocks are align at 1k
        self.type           = RegisterBlockType.find_type(name)
        self.reg_addr_dict = {}
        self.reg_name_dict = {}
        self.max_reg_name_len   = 0
        self.visible_registers  = 0

    def add_register(self, register):
        """ Add a register to this block """
        self.add_child_category(register)
        self.reg_addr_dict[register.address] = register
        self.reg_name_dict[register.name] = register
        if register.is_visible() is True:
            self.visible_registers += 1
            name_len = len(register.name.strip())
            if self.max_reg_name_len < name_len:
                self.max_reg_name_len = name_len

    def get_id(self):
        """ Return block ID """
        return self.id

    def get_type(self):
        """ Returns the register block type enum (RegisterBlockType) """
        return self.type

    def get_max_reg_name_len(self):
        """ Returns length of the bigger register name """
        return self.max_reg_name_len

    def get_registers_addr_dict(self):
        """ Returns registers block dictionary with address as key"""
        return self.reg_addr_dict

    def get_register_by_name(self, name):
        """ Get the register in this block that matches name """

        return self.reg_name_dict.get(name)

    def get_register_by_addr(self, address):
        """ Get the register in this block that matches address """

        return self.reg_addr_dict.get(address)

    def get_num_visible_registers(self):
        """ Returns the number of registers visible for the load DDR controller configuration """
        return self.visible_registers

    def __str__(self):
        """ Generate a string with the register block address and name and its contents """

        output = "0x%08x - %s" % (self.address, self.name)
        for addr in sorted(self.reg_addr_dict.keys()):
            register = self.get_register_by_addr(addr)
            output +=  "\n\t%s" % register
        return output
