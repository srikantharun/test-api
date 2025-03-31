# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Read and validate the memory map yaml
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import pathlib
import typing
from typing import Annotated, Literal
import yaml
import pydantic

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "MemoryMap",
    "read_config_file",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Models
# --------------------------------------------------------------------------------------------------

class MemoryMap(pydantic.BaseModel):
    name: str
    description: typing.Optional[str] = None
    offset: int
    size: int
    regions: typing.Optional[typing.List["MemoryMap"]] = None
    type: Literal['device', 'memory']  | None = None
    flags: typing.Optional[typing.List[Literal['R', 'W', 'X']]] = None
    noc_addr_scheme: Literal['absolute', 'relative']  | None = None
    block: typing.Optional[str] = None   # this is only used in the internal representation

    @pydantic.model_validator(mode='after')
    def check_type_and_flags(cls, values):
        type_value = values.type
        flags_value = values.flags
        name_value=values.name

        # Check that the flags are set always when the endpoint is not reserved area
        if 'reserved' not in name_value:
            if type_value and not flags_value:
                raise ValueError(f'If type "{type_value}" is defined, flags must also be defined.')

        return values

    @pydantic.model_validator(mode='after')
    def check_alignment(cls,values):
        size = values.size
        offset=values.offset
        if size is not None and offset is not None:
            if offset & (size - 1) != 0:
                raise ValueError(f'Start address is not aligned with the size {size} for offset {offset}.')
        return values


    @pydantic.model_validator(mode='after')
    def check_region_size(cls,values):
        size = values.size
        # Check if size is a multiple of 4KB
        if size % (4 * 1024) != 0:
            raise ValueError(f'Size {size} is not a multiple of 4KB.')
        return values
    class Config:
        # Required for self-referencing models
        arbitrary_types_allowed = True


class MemoryMapModel(pydantic.BaseModel):
    memory_map: typing.List[MemoryMap]

class CpuRegion (pydantic.BaseModel):
    type: Annotated[str, "device, memory"]
    offset: int
    mask: int
    size: int
    name : str | None

def read_config_file(
    config_file: pathlib.Path,
) -> MemoryMapModel:
    """Read the memory map file and validate it.

    Args:
        config_file: The path to the memory map file.

    Returns:
        The validated Memory Map configuration.

    Raises:
        pydantic.ValidationError: If the configuration file is invalid.
    """
    with config_file.open("r") as file:
        config = yaml.safe_load(file)
    _logger.debug("Read config file.")
    return MemoryMapModel.model_validate(config)
