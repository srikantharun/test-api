# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Read and validate the pad configuration csv
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import pathlib
import csv
from typing import Annotated, Any
from typing_extensions import Self

import pydantic

import impl

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "PadModel",
    "PadConfigModel",
    "read_config_file",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

_signal_str = pydantic.constr(pattern=r"^[a-zA-Z0-9_\[\]' ]*$")
_number_str = pydantic.constr(pattern=r"^[0-9]*$")

# --------------------------------------------------------------------------------------------------
# Models
# --------------------------------------------------------------------------------------------------

class PadModel(pydantic.BaseModel):
    cell_name: str
    direction: impl.DirectionEnum
    padtype: impl.PadTypeEnum
    orientation: impl.OrientationEnum
    pad_signal: _signal_str
    core_side_input: _signal_str
    input_enable: _signal_str
    core_side_output: _signal_str
    output_enable: _signal_str
    oe_active_low: bool
    ie_active_low: bool
    drive_strength: _signal_str
    pull_enable: _signal_str
    pull_type: _signal_str
    schmitt_trigger: _signal_str
    high_impedance: str | None = None
    dft_mux: bool
    row_index: _number_str | None = None

    @pydantic.model_validator(mode="after")
    def validate_direction(self) -> Self:

        if self.padtype in [impl.PadTypeEnum.OSCILLATOR_FAST, impl.PadTypeEnum.OSCILLATOR_SLOW]:
            if self.direction is not impl.DirectionEnum.INPUT:
                raise ValueError(f"Oscillator pad '{self.cell_name}' must be configured as input!")
        return self

    @pydantic.field_validator("core_side_input")
    @classmethod
    def default_core_side_input(cls, v: str) -> str:
        if not v:
            return "1'b0"
        return v

    @pydantic.field_validator("core_side_output")
    @classmethod
    def default_core_side_output(cls, v: str) -> str:
        if not v:
            return "/* open */"
        return v

    @pydantic.model_validator(mode="after")
    def default_input_and_output_enable(self) -> Self:
        if not self.output_enable:
            if self.direction is impl.DirectionEnum.OUTPUT:
                self.output_enable = "1'b1"
            if self.direction is impl.DirectionEnum.INOUT:
                raise ValueError("inout pad needs an output enable")
            if self.direction is impl.DirectionEnum.INPUT:
                self.output_enable = "1'b0"

        if not self.input_enable:
            if self.direction is impl.DirectionEnum.OUTPUT:
                self.input_enable = "1'b0"
            if self.direction is impl.DirectionEnum.INOUT:
                if self.oe_active_low:
                    self.input_enable  = self.output_enable
                else:
                    # Use of an xor instead of an inverter to use the port detection via `'`
                    self.input_enable = f"(1'b1 ^ {self.output_enable})"
            if self.direction is impl.DirectionEnum.INPUT:
                self.input_enable = "1'b1"

        return self

    @pydantic.field_validator("drive_strength")
    @classmethod
    def default_drive_strength(cls, v: str) -> str:
        if not v:
            return "'0"
        return v

    @pydantic.field_validator("pull_enable")
    @classmethod
    def default_pull_enable(cls, v: str) -> str:
        if not v:
            return "1'b0"
        return v

    @pydantic.field_validator("pull_type")
    @classmethod
    def default_pull_type(cls, v: str) -> str:
        if not v:
            return "1'b0"
        return v

    @pydantic.field_validator("schmitt_trigger")
    @classmethod
    def default_schmitt_trigger(cls, v: str) -> str:
        if not v:
            return "1'b0"
        return v

    @pydantic.field_validator("row_index")
    @classmethod
    def default_row_index(cls, v: str) -> str:
        if not v:
            return "0"
        return v

class PadConfigModel(pydantic.BaseModel):
    pads: list[PadModel]


def read_config_file(
    config_file: pathlib.Path,
) -> PadConfigModel:
    """Read the pad configuration file and validate it.

    Args:
        config_file: The path to the pad configuration file.

    Returns:
        The validated pad configuration.

    Raises:
        pydantic.ValidationError: If the configuration file is invalid.
    """
    with config_file.open("r") as file:
        config = list(csv.DictReader(file))
    _logger.debug("Read config file.")
    return PadConfigModel(pads=config)
