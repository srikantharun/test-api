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
from libconfig.types.config import Config
from libconfig.types.default import Default
from libconfig.log import Log


class AccessMode(Enum):
    """ Enum class that defines all Access mode types """
    READ_WRITE   = "read-write"
    READ         = "read-only"
    WRITE        = "write-only"
    UNKNOWN      = "unknown"

    def __str__(self):
        """ Override string implementation """
        return "ACCESS_%s" % self.name

    def __repr__(self):
        """ Override repr implementation """
        return str(self)


class ProgMode(Enum):
    """ Enum class that defines all program modes """
    STATIC         = "static"
    DYNAMIC        = "dynamic"
    QUASI_DYNAMIC  = "quasi-dynamic"
    UNKNOWN        = "unknown"

    def __str__(self):
        """ Override string implementation """
        return "PROG_%s" % self.name

    def __repr__(self):
        """ Override repr implementation """
        return str(self)


class Field(Config):
    def __init__(self, id, name, offset, size, access, field_type, default, help, visible):
        super().__init__(name)
        access = access.strip()
        if len(access) == 0:
            self.access = AccessMode.UNKNOWN
        else:
            self.access = AccessMode(access)
        self.offset     = utils.hex_or_int(offset)
        self.size       = size
        self.visible    = visible
        self.help       = help
        try:
            self.field_type = ProgMode(field_type)
        except ValueError:
            self.field_type = ProgMode.UNKNOWN
        self.decoded    = False
        self.id         = id
        self.default    = Default(default)
        self.set_min(0)
        self.set_max((1 << self.size) - 1)
        self.support_forced = False

    def get_id(self):
        """ Return field id """
        return self.id

    def __str__(self):
        """ Generate a string with the field data """
        return "%s: %2d - %s - %s - %d - %s" % (self.id, self.offset, self.name, self.default, self.size, self.is_supported())

    def get_offset(self):
        """ Returns the field offset """
        return self.offset

    def get_width(self):
        """ Returns the field width """
        return self.size

    def get_mask(self):
        """ Returns the field mask """
        return (self.get_max() << self.offset) & 0xFFFFFFFF

    def get_access_type(self):
        """ Returns the access type string """
        return self.access

    def get_prog_mode(self):
        """ Returns the field program mode """
        return self.field_type

    def has_multiple_default(self):
        """ Override parent method
            always returns False
            fields cannot have multiple defaults """
        return False

    def get_default(self, _=None):
        """ Override parent method
            returns default value
            fields cannot have multiple defaults """
        return self.default.get_value()


    def list_defaults(self):
        """ Returns a list with the default objects """
        return [self.default]

    def force_support(self):
        self.support_forced = True

    def is_supported(self, static_only=False):
        """ Override parent method
            Check if the config is supported based on the current configuration
            and the visible field of the register map
            returns True or False """
        
        if self.support_forced is True:
            return True

        rslt = super().is_supported(static_only=static_only) and self.visible

        if (rslt is False) and (self.value is not None):
            Log().error("%s set but invalid" % (self.get_id()))
            self._log_config_line()

        if self.is_value_set() is True:
            if (self.is_value_valid(self.value) is False):
                rslt = False

        return rslt

    def is_visible(self):
        """ Returns true if the field is visible else false"""
        return self.visible
