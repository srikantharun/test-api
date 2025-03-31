# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Types and definitions for a unified configuration of the pad soldering process.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import enum

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "DirectionEnum",
    "direction_to_prefix",
    "OrientationEnum",
    "PadTypeEnum",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Implementation
# --------------------------------------------------------------------------------------------------

class DirectionEnum(enum.Enum):
    INPUT = "input"
    OUTPUT = "output"
    INOUT = "inout"

def direction_to_prefix(direction: DirectionEnum) -> str:
    if direction is DirectionEnum.INPUT:
        return "i"
    if direction is DirectionEnum.OUTPUT:
        return "o"
    if direction is DirectionEnum.INOUT:
        return "io"
    raise ValueError(f"Unknown direction: {direction}")

class OrientationEnum(enum.Enum):
    HORIZONTAL = "horizontal"
    VERTICAL = "vertical"

class PadTypeEnum(enum.Enum):
    FAST = "fast"
    SLOW = "slow"
    OSCILLATOR_SLOW = "oscillator_slow"
    OSCILLATOR_FAST = "oscillator_fast"
