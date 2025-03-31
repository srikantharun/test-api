# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Read and validate the performance scenario yaml."""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import pathlib
from typing import Annotated, Literal, Optional, List, Dict, Tuple
import yaml
import pydantic
from arch import Arch
import utils
from pathlib import Path
# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "Scenarios",
    "read_config_file",
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Architecture
# --------------------------------------------------------------------------------------------------
ArchInitiators = Literal[tuple(Arch.keys())]
ArchAllDmas=Literal[utils.extract_unit_union(Arch)]

# --------------------------------------------------------------------------------------------------
# Models
# --------------------------------------------------------------------------------------------------


# TODO: check the naming convention of the PVE DMAs
class Task(pydantic.BaseModel):
    name: str
    resource: Literal[ArchInitiators]
    instance:  Literal[ArchAllDmas]
    type:  Optional[Literal["SNPS_DW", "SNPS_PCIE", "AXE"]] = pydantic.Field(default=None)  # Will be set based on instance
    mode: str
    num_channels: int
    channels: List[Literal[0,1,2,3,4]]
    source_address: List[Optional[str]]
    destination_address: List[Optional[str]]
    burst_length:  List[Literal[4,8,16,32,64]]
    osr: List[Literal[0,1,3,7,15]]
    src_xbytesize: List[int]  # in bytes
    dst_xbytesize: List[int]  # in bytes
    src_ms: List[int]
    dst_ms: List[int]

    # Fields indicated only for the AXE-DMA
    src_xaddrinc: List[Optional[int]] = pydantic.Field(default=None)
    dst_xaddrinc: List[Optional[int]] = pydantic.Field(default=None)
    tran_size: List[Optional[Literal[0,1,2,3,4,5,6]]] = pydantic.Field(default=None)
    xtype: List[Optional[Literal[0,1,2,3]]] = pydantic.Field(default=None)
    fillval: List[Optional[int]] = pydantic.Field(default=None)
    fillval_mode: List[Optional[Literal[0,1]]] = pydantic.Field(default=None)
    ytype: List[Optional[Literal[0,1,2,3]]] = pydantic.Field(default=None)
    src_yrowsize: List[Optional[int]] = pydantic.Field(default=None)
    dst_yrowsize: List[Optional[int]] = pydantic.Field(default=None)
    src_yaddrstride: List[Optional[int]] = pydantic.Field(default=None)
    dst_yaddrstride: List[Optional[int]] = pydantic.Field(default=None)


    #TODO have to fix the fact that the same instance name might be a different type
    @pydantic.model_validator(mode='before')
    def set_type_based_on_instance(cls, values):
        instance = values['instance']
        values['type']=Arch[values['resource']][instance]
        return values

class Scenarios(pydantic.BaseModel):
    name: str
    description: Optional[str] = None
    data_check: bool
    data_random: bool
    perf_counter: bool
    label: List[str]
    requirement_ids: List[str] 
    tasks: List[Task]

    #TODO: Add validation of selected memory vs the address
    @pydantic.model_validator(mode='after')
    def check_resource_and_instance(cls, values):

        for task in values.tasks:
            allowed_instances=Arch[task.resource]
            if task.instance not in allowed_instances:
                raise ValueError(f'If the resource name is {task.resource}, task instance must be one of {allowed_instances}, but got {task.instance}')

        return values

    @pydantic.model_validator(mode='after')
    def check_scenario_name(cls, values):
        if not values.name.startswith("test_"):
           raise ValueError("The test name does not start with 'test_'.")
        return values

    @pydantic.model_validator(mode='after')
    def check_num_fields(cls, values):
        # Checks if all the fields have the right number of elements depending on the number of channels configured
        for task in values.tasks:
            assert len(task.channels) == task.num_channels, f'The channel list {task.channels} does not  match the number of channels {task.num_channels}'
            assert len(task.src_xbytesize) == task.num_channels, f'The destination list {task.src_xbytesize} does not  match the number of channels {task.num_channels}'
            assert len(task.burst_length) == task.num_channels, f'The destination list {task.burst_length} does not  match the number of channels {task.num_channels}'
            assert len(task.osr) == task.num_channels, f'The destination list {task.osr} does not  match the number of channels {task.num_channels}'
            if task.source_address:
                assert len(task.source_address) == task.num_channels, f'The destination list {task.source_address} does not  match the number of channels {task.num_channels}'
            if task.destination_address:
                assert len(task.destination_address) == task.num_channels, f'The destination list {task.destination_address} does not  match the number of channels {task.num_channels}'
        return values


    @pydantic.model_validator(mode='after')
    def check_axe_tasks_fields(cls, values):
        for task in values.tasks:
            if task.type == "AXE":
                assert task.src_xaddrinc is not None and task.dst_xaddrinc is not None, f'SRC and DST Xaddrinc need to be defined for AXE DMA task.'
                assert task.tran_size is not None, f'Tran_size needs to be defined for AXE DMA task.'
                assert task.xtype is not None and task.ytype is not None, f'XTYPE and YTYPE need to be defined for AXE DMA task.'

                for i,_ in enumerate(task.src_xaddrinc):
                     assert task.src_xaddrinc[i]==task.dst_xaddrinc[i], f'Europa supports only equal INCR values.'

                for i,_ in enumerate(task.src_xbytesize):
                    if task.src_xbytesize != task.dst_xbytesize or task.src_yrowsize != task.dst_yrowsize:
                         assert task.fillval is not None  and task.fillval_mode is not None, f'Fillval mode and value need to be defined in case of uneven src and dst sizes.'

                    #TODO: Below constraints are a current limitation not an illegal scenario. They will be addressed in the future of T-REX
                    assert task.src_xbytesize[i] == task.src_xbytesize[i], f'T-REX currently does not support different SRC and DST xbyte sizes'

                for i, v in enumerate(task.ytype):
                    if v != 0: # if the ytype is not disabled then all fields need to be defined
                        assert task.src_yrowsize[i] is not None and task.dst_yrowsize[i] is not None, f'SRC and DST row size needs to be defined.'
                        assert task.src_yaddrstride[i] is not None and task.dst_yaddrstride[i] is not None, f'SRC and DST row size needs to be defined.'

                        #TODO: Below constraints are a current limitation not an illegal scenario. They will be addressed in the future of T-REX
                        assert task.src_yrowsize[i] == task.dst_yrowsize[i], f'T-REX currently does not support different SRC and DST row sizes'
                        assert v==1, f'T-REX currently does not support WRAP/FILL on the Y-dimension.'

        #TODO: add legal values of yrow and xbytesize
        return values

    @pydantic.model_validator(mode='after')
    def check_snps_task_fields(cls, values):
        for task in values.tasks:
            if task.type != "AXE":
                for i,_ in enumerate(task.src_xbytesize):
                    assert task.src_xbytesize[i]==task.dst_xbytesize[i], f'The src and dst number of bytes transferred needs to be the same for SNPS IPs'
                    assert task.src_xbytesize[i] > 0 and (task.src_xbytesize[i] & (task.src_xbytesize[i] - 1)) == 0, f'The src and dst number of bytes transferred needs to be a power of 2!'

        return values


   # TODO: Check that if the test is AXE dma the following are defined,src_ms,dst_ms and all the ystride etc)


class ScenariosModel(pydantic.BaseModel):
    scenarios: List[Scenarios]


def read_config_file(
    config_file: pathlib.Path,
) -> ScenariosModel:
    """Read the performance scenarios file and validate it.

    Args:
        config_file: The path to the Scenarios file.

    Returns:
        The validated Performance Scenario configuration.
        The name of the source file that will be used to generate the respective
        test_fw.yaml file.

    Raises:
        pydantic.ValidationError: If the configuration file is invalid.
    """
    with config_file.open("r") as file:
        config = yaml.safe_load(file)
        filename=Path(file.name).stem
    _logger.debug("Read config file.")
    return ScenariosModel.model_validate(config), filename
