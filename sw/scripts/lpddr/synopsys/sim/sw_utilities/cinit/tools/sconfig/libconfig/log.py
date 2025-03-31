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
from libconfig.utils import Singleton


class LogLevel(Enum):
    """ Enum class that defines all log types supported by LogUtil """
    DEBUG   = 1
    INFO    = 2
    WARN    = 3
    ERROR   = 4

    def __str__(self):
        return "%-5s" % self.name

    def __repr__(self):
        return str(self)

    def __lt__(self, other):
      if self.__class__ is other.__class__:
        return self.value < other.value
      return NotImplemented

    def __le__(self, other):
      if self.__class__ is other.__class__:
        return self.value <= other.value
      return NotImplemented


class Log(metaclass = Singleton):
    """ Log class to manage all the logging messages """
    def __init__(self):
        """ Init function does nothing """
        self.prefix = None
        self.level  = LogLevel.INFO

    def cfg(self, prefix=None, level=None):
        """ Initialize Log with the program name used to call the application """
        if prefix is not None:
            self.prefix = prefix
        if level is not None:
            self.level = level

    def _print_log(self, level, msg):
        """ Print log message if the configured log level lower or equal to the level passed """
        if self.level <= level:
            output_msg = ""
            if self.prefix is not None:
                output_msg += "%s" % self.prefix
            output_msg += "%s: %s" % (level, msg)
            print(output_msg)

    def debug(self, msg):
        """ Print debug message """
        self._print_log(LogLevel.DEBUG, msg)

    def info(self, msg):
        """ Print info message """
        self._print_log(LogLevel.INFO, msg)

    def warn(self, msg):
        """ Print warning message """
        self._print_log(LogLevel.WARN, msg)

    def error(self, msg):
        """ Print error message """
        self._print_log(LogLevel.ERROR, msg)
