# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Core utilities to filter out different sections of the memory map.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import collections

import package_lib.exceptions

import copy
import mmap_config


# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "match_addr_region",
    "get_block_names",
    "check_continuous_addr",
    "flatten_endpoints",
    "flatten_top",
    "check_unique_name_combinations",
    "remove_reserved_endpoints",
    "filter_memories",
    "create_cpu_regions",
    "filter_cpu_device_regions",
    "modify_endpoint_type"
]
# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

class CoreError(package_lib.exceptions.HandledException):
    """Errors Caused by functional Errors of the core logic."""

# --------------------------------------------------------------------------------------------------
# Implemenation
# --------------------------------------------------------------------------------------------------

def match_addr_region(
    regions: list[mmap_config.MemoryMap],
    address,
) -> mmap_config.MemoryMap:
    """Extracts the region in which the address lies within.
    """
    for region in regions:
        start_addr=region.offset
        end_addr= region.offset + region.size -1
        if start_addr <= int(address,16) <= end_addr:
            matched_region = copy.deepcopy(region)
    return matched_region

def get_block_names(
    memory_map: list[mmap_config.MemoryMap],
) -> list[str]:
    """Extracts the names of the top level blocks in the Memory map
    """
    blocks=[]
    for region in memory_map:
        if 'reserved' not in region.name:
            blocks.append(region.name)
    return blocks

def check_continuous_addr(
    regions: list[mmap_config.MemoryMap],
) -> None:
    """Checks that there are no gaps in the memory map
    """
    prev_region_end=None

    for region in regions:
        if prev_region_end and region.offset != prev_region_end+1:
            raise ValueError(f'Start address of region {region.block}_{region.name} is not continuous of the previous region.')
        prev_region_end = region.offset + region.size - 1

def check_unique_name_combinations(objects):
    """Checks that the name created by the combination of block and name are unique.
       Common issue when having multiple reserved areas in the same block.
    """
    seen_combinations = set()
    for obj in objects:
        combo = (obj.block,obj.name )
        if combo in seen_combinations:
            raise ValueError(f"Duplicate combination of block and name found in: {combo}. Please use another name.")
        seen_combinations.add(combo)

def flatten_endpoints(
    memory_map: list[mmap_config.MemoryMap],
    blocks: list[str],
    include_all_hier: bool = False,
    parent: mmap_config.MemoryMap = None,
) -> list[mmap_config.MemoryMap]:
    """Extracts the endpoints of the Memory map
    """
    regions=copy.deepcopy(memory_map)

    result: list[mmap_config.MemoryMap] = []
    for region in regions:

        if parent:
            # Set block and name based on parent
            if parent.name in blocks:
                region.block = parent.name
            else:
                region.block = parent.block
                region.name= "_".join([parent.name, region.name])

            # Flatten address offsets
            region.offset = parent.offset + region.offset
            # Inherit type and flags from parent
            region.type = parent.type if region.type is None else region.type
            region.flags = parent.flags if region.flags is None else region.flags
        else:
            region.block = region.name
            if 'reserved' not in region.name:
                assert not region.noc_addr_scheme is None, f"Endpoint '{region.name}' does not have a NoC Addr scheme"

        # If we want to include also the top hierarchies of each block
        if include_all_hier:
            result.append(region)

        else:
            # Endpoint reached
            if not region.regions:
                assert not region.type is None, f"Endpoint '{region.name}' does not have a type"
                assert not region.flags is None, f"Endpoint '{region.name}' does not have flags"
                result.append(region)

        # Recursively filter subregions
        if region.regions:
            result.extend(flatten_endpoints(region.regions, parent=region, blocks=blocks, include_all_hier=include_all_hier))

    try:
        check_unique_name_combinations(result)
    except ValueError as e:
        print(e)

    return result


def flatten_top(
    memory_map: list[mmap_config.MemoryMap],
) -> list[mmap_config.MemoryMap]:
    """Extracts the top level view of the Memory map
    """
    regions=copy.deepcopy(memory_map)
    result=[]
    for region in regions:
        region.block = region.name
        result.append(region)
    return result


def remove_reserved_endpoints(
    regions: list[mmap_config.MemoryMap],
) ->list[mmap_config.MemoryMap]:
    """Remove the reserved areas from the endpoints
    """
    result=[]
    for region in regions:
        if 'reserved' not in region.name:
            result.append(region)

    return result

def change_field(node: mmap_config.MemoryMap, field_name, new_value):
    # Change the field in the current node
    setattr(node, field_name, new_value)

    # Recursively change the field in all children
    if node.regions:
        for region in node.regions:
            change_field(region, field_name, new_value)

def modify_endpoint_type(
    memory_map: list[mmap_config.MemoryMap],
    blocks: list[str]
) -> list[mmap_config.MemoryMap]:

    """Modifies the type of the endpoints that match the input block list and makes them device regions.
    This is done to remove them from the regions a CPU from another level sees.
    """
    regions=copy.deepcopy(memory_map)
    for block in blocks:
        for region in regions:
            if block in region.block:
                change_field(region, 'type', 'device')
    return regions

def filter_memories(
    regions: list[mmap_config.MemoryMap],
) -> list[mmap_config.MemoryMap]:
    """Extracts the memories of the Memory map regions passed as input argument.
    """
    result = []

    for region in regions:
        if region.type=='memory' and 'reserved' not in region.name and 'datapath' not in region.name:
            result.append(region)
    return result

def has_continuous_bits(mask):
    # Convert the integer to a binary string and strip the '0b' prefix
    bin_mask = bin(mask)[2:]

    # Strip leading and trailing zeros
    stripped_bin_mask = bin_mask.strip('0')

    # Check if there's any '0' in the stripped binary string
    return '0' not in stripped_bin_mask

def create_cpu_regions(
    regions: list[mmap_config.MemoryMap],
) -> list[mmap_config.CpuRegion]:
    """Creates CPU regions
    """
    cpu_regions = []

    # Initialize variables
    current_type = None
    continuous_area: list[mmap_config.MemoryMap] = []
    continuous_areas = []

    # Iterate through entries
    for region in regions:

        # If current_type is None, initialize it
        if current_type is None:
            current_type = region.type
            continuous_area = [region]
        elif region.type == current_type:
            start_addr=continuous_area[0].offset
            end_addr=region.offset + region.size - 1
            size = end_addr - start_addr
            # Check that the address size is aligned with the start_addr
            if (start_addr & size == 0):
                continuous_area.append(region)
            else:
                #Check continued area mask
                start_addr=continuous_area[0].offset
                end_addr=continuous_area[-1].offset + continuous_area[-1].size -1
                size = end_addr - start_addr
                mask = size ^ 0xFFFFFFFFFFFFFFFF
                if has_continuous_bits(mask):
                    continuous_areas.append(continuous_area)
                else:
                    raise ValueError(f'Mask is  "{mask}" for start addr {hex(start_addr)} and {hex(size)}')
                current_type = region.type
                continuous_area = [region]
        else:
            continuous_areas.append(continuous_area)
            current_type = region.type
            continuous_area = [region]

    # Append the last continuous area after loop ends
    if continuous_area:
        continuous_areas.append(continuous_area)

    # Process all the areas
    for continuous_area in continuous_areas:
        type=continuous_area[0].type
        start_addr=continuous_area[0].offset
        end_addr=continuous_area[-1].offset + continuous_area[-1].size -1
        size = end_addr - start_addr
        mask = size ^ 0xFFFFFFFFFFFFFFFF
        assert start_addr & size == 0, f'{continuous_area[0].name} not aligned start of region for address {hex(start_addr)} and size {hex(size)} '
        assert end_addr & mask == start_addr, f'not aligned end of for address {hex(end_addr)} and size {hex(size)} '

        # Concatenate the names of the units in the region
        concatenated_names = ''
        # Loop through each item in continuous_area and concatenate the names
        for idx in range(len(continuous_area)):
            if idx == 0:
                concatenated_names = continuous_area[idx].name
            else:
                concatenated_names += ' ' + continuous_area[idx].name
        cpu_regions.append(mmap_config.CpuRegion(type=type, name=concatenated_names,  offset=start_addr, mask=mask, size=size+1))

    return cpu_regions

def filter_cpu_device_regions(
    regions: list[mmap_config.CpuRegion],
) -> list[mmap_config.CpuRegion]:
    """Extracts the device regions of the regions that the APU CPUs see.
    """
    result = []

    for region in regions:
        if region.type=='device':
            result.append(region)

    return result
