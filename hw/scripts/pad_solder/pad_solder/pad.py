# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Description of a Pad configuration.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import package_lib.exceptions

import logging
import dataclasses
import functools

import impl

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "FunctionalPad",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

class PadError(package_lib.exceptions.HandledException):
    """Errors Caused by invalid pad configurations."""


# --------------------------------------------------------------------------------------------------
# Implementation
# --------------------------------------------------------------------------------------------------

@dataclasses.dataclass(frozen=True, kw_only=True)
class FunctionalPad:
    name: str
    direction: impl.DirectionEnum
    padtype: impl.PadTypeEnum
    orientation: impl.OrientationEnum = impl.OrientationEnum.HORIZONTAL
    core_signal_output: str = "1'b0"
    core_signal_output_enable: str = "1'b0"
    core_signal_oe_active_low: bool = False
    core_signal_ie_active_low: bool = False
    core_signal_input: str = "/* open */"
    core_signal_input_enable: str = "1'b1"
    core_signal_pull_type: str = "1'b0"
    core_signal_pull_enable: str = "1'b0"
    core_signal_drive: str = "'0"
    core_signal_schmitt: str = "1'b0"
    row_index: int = 0
    dft: bool = False

    @functools.cached_property
    def name_sanitized(self) -> str:
        ret = self.name.replace("[", "_")
        ret = ret.replace("]", "")
        return ret

    @functools.cached_property
    def implementation_key(self) -> str:
        return f"{self.padtype.value}_{self.orientation.value}"

    @functools.cached_property
    def pad_signal(self) -> str:
        if self.is_bus:
            return f"{impl.direction_to_prefix(self.direction)}_pad_{self.busname}[{self.bus_index}]"
        return f"{impl.direction_to_prefix(self.direction)}_pad_{self.name_sanitized}"

    @functools.cached_property
    def instance_name(self) -> str:
        return f"u_{self.direction.value}_{self.name_sanitized}"

    @functools.cached_property
    def is_oscillator_pad(self) -> bool:
        return self.padtype in [
            impl.PadTypeEnum.OSCILLATOR_SLOW,
            impl.PadTypeEnum.OSCILLATOR_FAST,
        ]

    @functools.cached_property
    def is_bus(self) -> bool:
        return "[" in self.name

    @functools.cached_property
    def bus_index(self) -> int:
        if not self.is_bus:
            raise PadError(f"Pad {self.name} is not a bus")

        return int(self.name.split("[")[1].split("]")[0])

    @functools.cached_property
    def busname(self) -> str:
        if not self.is_bus:
            raise PadError(f"Pad {self.name} is not a bus")

        return self.name.split("[")[0]

    @functools.cached_property
    def output_enable_expr(self) -> str:
        if self.core_signal_oe_active_low:
            return f"(1'b1 ^ {self.core_signal_output_enable})"
        return self.core_signal_output_enable

    @functools.cached_property
    def input_enable_expr(self) -> str:
        if self.core_signal_ie_active_low:
            return f"(1'b1 ^ {self.core_signal_input_enable})"
        return self.core_signal_input_enable

    @functools.cached_property
    def dft_signal_output(self) -> str:
        if self.direction is impl.DirectionEnum.INPUT:
            raise PadError("Pad {self.name} is not an input pad")
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_oup[{self.bus_index}]"
        return f"i_dft_{self.name_sanitized}_oup"

    @functools.cached_property
    def dft_signal_output_enable(self) -> str:
        if self.direction is impl.DirectionEnum.INPUT:
            raise PadError("Pad {self.name} is not an input pad")
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_oup_en[{self.bus_index}]"
        return f"i_dft_{self.name_sanitized}_oup_en"

    @functools.cached_property
    def dft_signal_input(self) -> str:
        if self.direction is impl.DirectionEnum.OUTPUT:
            raise PadError("Pad {self.name} is not an output pad")
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"o_dft_{self.busname}_inp[{self.bus_index}]"
        return f"o_dft_{self.name_sanitized}_inp"

    @functools.cached_property
    def dft_signal_input_enable(self) -> str:
        if self.direction is impl.DirectionEnum.OUTPUT:
            raise PadError("Pad {self.name} is not an output pad")
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_inp_en[{self.bus_index}]"
        return f"i_dft_{self.name_sanitized}_inp_en"

    @functools.cached_property
    def dft_signal_pull_type(self) -> str:
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_pull_type"
        return f"i_dft_{self.name_sanitized}_pull_type"

    @functools.cached_property
    def dft_signal_pull_enable(self) -> str:
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_pull_en"
        return f"i_dft_{self.name_sanitized}_pull_en"

    @functools.cached_property
    def dft_signal_schmitt(self) -> str:
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_schmitt"
        return f"i_dft_{self.name_sanitized}_schmitt"

    @functools.cached_property
    def dft_signal_drive(self) -> str:
        if not self.dft:
            raise PadError("Pad {self.name} is not dft muxed")
        if self.is_bus:
            return f"i_dft_{self.busname}_drive"
        return f"i_dft_{self.name_sanitized}_drive"


@dataclasses.dataclass(frozen=True, kw_only=True)
class OscillatorPad(FunctionalPad):

    @functools.cached_property
    def implementation_key(self) -> str:
        if not self.padtype in [impl.PadTypeEnum.OSCILLATOR_SLOW, impl.PadTypeEnum.OSCILLATOR_FAST]:
            raise PadError(f"Oscillator Pad {self.name} has wrong padtype: '{self.padtype}'")
        fast_or_slow = self.padtype.value.replace("oscillator_", "")
        return f"{fast_or_slow}_{self.orientation.value}"

    @functools.cached_property
    def pad_signal_inp(self) -> str:
        return f"i_pad_{self.name_sanitized}"

    @functools.cached_property
    def pad_signal_oup(self) -> str:
        return f"o_pad_{self.name_sanitized}"

    @functools.cached_property
    def pad_signal(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.pad_signal")

    @functools.cached_property
    def bus_index(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.bus_index")

    @functools.cached_property
    def busname(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.busname")

    @functools.cached_property
    def dft_signal_output(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_output")

    @functools.cached_property
    def dft_signal_output_enable(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_output_enable")

    @functools.cached_property
    def dft_signal_input(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_input")

    @functools.cached_property
    def dft_signal_input_enable(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_input_enable")

    @functools.cached_property
    def dft_signal_pull_type(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_pull_type")

    @functools.cached_property
    def dft_signal_pull_enable(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_pull_enable")

    @functools.cached_property
    def dft_signal_schmitt(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_schmitt")

    @functools.cached_property
    def dft_signal_drive(self) -> str:
        raise PadError(f"Oscillator Pad {self.name} not allowed to access self.dft_signal_drive")
