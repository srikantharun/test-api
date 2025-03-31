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


class Security(Enum):
    """ Enum class that defines all security access types """
    NON_SECURE   = "Non-secure"
    ROOT         = "Root"
    SECURE       = "Secure"
    REALM        = "Realm"

    def __str__(self):
        """ Override string implementation """
        return "SEC_%s" % self.name

    def __repr__(self):
        """ Override repr implementation """
        return str(self)



class Register(Category):
    def __init__(self, name, id, address, security, visible):
        super().__init__(name)
        self.address            = utils.hex_or_int(address)
        self.default            = 0
        self.decoded            = False
        security = security.strip().replace('"','')
        if len(security) == 0:
            self.security       = Security.NON_SECURE
        else:
            self.security       = Security(security)
        self.visible            = visible
        self.id                 = id
        self.field_offset_dict  = {}
        self.field_name_dict    = {}
        self.max_field_name_len = 0

    def get_id(self):
        """ Return register ID """
        return self.id

    def add_field(self, field):
        """ Add a field to this register """
        self.add_child_config(field)
        self.field_offset_dict[field.offset] = field
        self.field_name_dict[field.name] = field
        self._set_field(field.get_offset(), field.get_mask(), field.get_default())
        if field.is_visible() is False:
            return
        if self.max_field_name_len < len(field.name):
            self.max_field_name_len = len(field.name)

    def get_max_field_name_len(self):
        """ Returns the length of the longer field name """
        return self.max_field_name_len

    def get_security(self):
        """ Returns the register secure access type """
        return self.security

    def get_field_value(self, reg_value, field_name):
        """ Get the value of this field from the value of the parent register """

        field = self.get_field_by_name(field_name)
        if field is None:
            raise utils.LibConfigError("Field %s not present in %s" % (field_name, self.name))
        return utils.get_field(reg_value, field.get_offset(), field.get_mask())

    def set_field_value(self, reg_value, field_name, field_value):
        """ Set the value of this field in the value of the parent register """

        field = self.get_field_by_name(field_name)
        if field is None:
            raise utils.LibConfigError("Field %s not present in %s" % (field_name, self.name))
        return utils.set_field(reg_value, field.get_offset(), field.get_mask(), field_value)

    def _set_field(self, offset, mask, value):
        """ Set the value of a field in the default of this register """

        self.default = utils.set_field(self.default, offset, mask, value)

    def get_fields_offset_dict(self):
        """ Returns fields dictionary with offset as key"""
        return self.field_offset_dict

    def is_supported(self, static_only=False):
        """ Overwrite parent method
            Check if the register category is supported based on the current configuration
            and the visible field of the register map
            returns True or False """

        return self.visible and super().is_supported(static_only=static_only)

    def get_field_by_name(self, name):
        """ Get a field in this register that matches a given name """

        return self.field_name_dict.get(name.lower())

    def get_field_by_offset(self, offset):
        """ Get a field in this register that matches a given offset """

        return self.field_offset_dict.get(offset)

    def is_visible(self):
        """ Returns true if the register is visible else false"""
        return self.visible

    def __str__(self):
        """ Generate a string with the register block address and name and its contents """

        output =  "%s = 0x%08x  (0x%08x)" % (self.name, self.default, self.address)
        for offset in sorted(self.field_offset_dict.keys()):
            field = self.field_offset_dict[offset]
            output +=  "\n\t\t%s" % field
        return output
