# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Command line interface for memory map helper file generation
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------
import os
import logging
from typing import Annotated
import pathlib

import package_lib.cli
import typer

import jinja2

import mmap_config
import core
import utils
# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

__version__ = "0.1.0"
_logger = logging.getLogger(__name__)


# --------------------------------------------------------------------------------------------------
# Path variables
# --------------------------------------------------------------------------------------------------

# Default paths
REPO_ROOT = os.environ.get("REPO_ROOT")

default_templates= os.path.join(REPO_ROOT,"hw/scripts/addr_map/templates")
default_addr_map_src = os.path.join(REPO_ROOT,"hw/impl/europa/data/europa_memory_map.csv")
default_addr_map_pkg= os.path.join(REPO_ROOT,"hw/impl/europa/asic/rtl/pkg/aipu_addr_map_pkg.sv")
default_addr_map_hdr= os.path.join(REPO_ROOT,"sw/src/lib/common/include/memorymap.h")
default_addr_map_struct= os.path.join(REPO_ROOT,"sw/src/lib/common/memories.c")
default_addr_map_header=os.path.join(REPO_ROOT,"sw/src/lib/common/include/memories.h")

default_aicore_cva6_cpu_regions= os.path.join(REPO_ROOT,"hw/impl/europa/data/memory_map/rendered_files/aicore_cva6_regions.txt")
default_pve_cva6_cpu_regions= os.path.join(REPO_ROOT,"hw/impl/europa/data/memory_map/rendered_files/pve_cva6_regions.txt")
default_apu_cpu_regions= os.path.join(REPO_ROOT,"hw/impl/europa/data/memory_map/rendered_files/apu_regions.txt")
default_memory_map = os.path.join(REPO_ROOT,"docs/europa/memory_map/europa_memory_map.md")
default_detailed_memory_map = os.path.join(REPO_ROOT,"docs/europa/memory_map/europa_detailed_memory_map.md")
# --------------------------------------------------------------------------------------------------
# Command Declarations
# --------------------------------------------------------------------------------------------------

app = typer.Typer(
    name="mem_map",
    help="A helper script for generating all helper files from the memory map",
    pretty_exceptions_show_locals=False,
    add_completion=False,
)


package_lib.cli.create_main_callback(
    app,
    enable_logging=True,
    enable_version=True,
    version=__version__,
    package_name="mmap",
)

# --------------------------------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------------------------------
@app.command("info")
@package_lib.cli.handle_exceptions
def _info(
    address: Annotated[
        str,
        typer.Option(
            "--address",
            "-a",
            help="Address that info is requested.",
            show_default=False,
        ),
    ],
    config: Annotated[
        pathlib.Path,
        typer.Option(
            "--config",
            "-c",
            help="Path to the configuration file.",
            show_default=False,
        ),
    ],

) -> None:
    """Provide info on a requested address"""

    configuration = mmap_config.read_config_file(config)
    memory_map=configuration.memory_map

    # Extract top level block names
    blocks=core.get_block_names(memory_map)

    # Extract all the endpoints
    only_endpoints = core.flatten_endpoints(memory_map,blocks)

    # Find the region that this matches and print info
    region=core.match_addr_region(only_endpoints,address)
    print(f'The address {address} is in the {region.block.upper()}-{region.name.upper()} address space region.')


@app.command("render")
@package_lib.cli.handle_exceptions
def _render(

    config: Annotated[
        pathlib.Path,
        typer.Option(
            "--config",
            "-c",
            help="Path to the configuration file.",
            show_default=False,
        ),
    ],

) -> None:
    """Render the Memory Map generated files."""
    _logger.info("Rendering the chip memory map generated files.")

    templates=default_templates

    configuration = mmap_config.read_config_file(config)
    memory_map=configuration.memory_map

    # Extract top level block names
    blocks=core.get_block_names(memory_map)

    # Extract the different views needed for the endpoints
    all_hierarchy = core.flatten_endpoints(memory_map,blocks,True)

    # Extract only the endpoints
    only_endpoints= core.flatten_endpoints(memory_map,blocks)

     # Extract only the top level view
    only_top= core.flatten_top(memory_map)

    # Check that there are no gaps in the memory map
    core.check_continuous_addr(only_endpoints)
    core.check_continuous_addr(only_top)

    # Extract the memories
    memories = core.filter_memories(only_endpoints)

    # Set-up render env
    _jinja_env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(templates),
        autoescape=jinja2.select_autoescape(),
    )

    _jinja_env.filters['hex'] = utils.hex
    _jinja_env.filters['indent'] = utils.indent
    _jinja_env.tests['contains_strings'] = utils.contains_strings

    # ------------------------
    # Render addr map package
    # ------------------------
    template = _jinja_env.get_template("axe_aipu_addr_map_pkg.sv.jinja2")

    rendered_aipu_pkg= template.render(items=all_hierarchy)

    # Write the rendered content to the output file
    with open(default_addr_map_pkg, 'w') as file:
        file.write(rendered_aipu_pkg)

    # ------------------------
    # Render the memorymap.h file
    # ------------------------
    template = _jinja_env.get_template("axe_memorymap.h.jinja2")

    rendered_memorymap_hdr= template.render(items=all_hierarchy)

    # Write the rendered content to the output file
    with open(default_addr_map_hdr, 'w') as file:
        file.write(rendered_memorymap_hdr)

    # ------------------------
    # Render the memories.c file
    # ------------------------
    template = _jinja_env.get_template("axe_memories.c.jinja2")

    rendered_memories= template.render(items=memories)

    # Write the rendered content to the output file
    with open(default_addr_map_struct, 'w') as file:
        file.write(rendered_memories)

    # ------------------------
    # Render the memories.h file
    # ------------------------
    template = _jinja_env.get_template("axe_memories.h.jinja2")

    rendered_memories= template.render()

    # Write the rendered content to the output file
    with open(default_addr_map_header, 'w') as file:
        file.write(rendered_memories)

    # ---------------------------------
    # Render the APU cpu regions
    # ---------------------------------
    # For the APU the AICORE and PVE are marked as device regions
    apu_endpoints=core.modify_endpoint_type(only_endpoints,['aicore','pve','sys_spm', 'l2','apu','reserved_4','reserved_3'])

    apu_regions=core.create_cpu_regions(apu_endpoints)

    # The APU AX65 only cares about device regions. Everything else is considered memory.
    apu_device_regions=core.filter_cpu_device_regions(apu_regions)

    template = _jinja_env.get_template("axe_apu_cpu_regions.txt.jinja2")

    rendered_cpu_regions= template.render(items=apu_device_regions)

    # Write the rendered content to the output file
    with open(default_apu_cpu_regions, 'w') as file:
        file.write(rendered_cpu_regions)


    # ---------------------------------
    # Render the AICORE cpu regions
    # ---------------------------------

    # AICOREs see the AICORE regions and other shared regions L2/DDR/PCIE etc
    # AICOREs see APU and PVE as device regions
    aicore_cva6_regions=core.modify_endpoint_type(only_endpoints,['pve','apu'])

    cva6_regions=core.create_cpu_regions(aicore_cva6_regions)

    template = _jinja_env.get_template("axe_cva6_cpu_regions.txt.jinja2")

    rendered_cpu_regions= template.render(merged_regions=cva6_regions, detailed_regions=aicore_cva6_regions)

    # Write the rendered content to the output file
    with open(default_aicore_cva6_cpu_regions, 'w') as file:
        file.write(rendered_cpu_regions)

    # ---------------------------------
    # Render the PVE cpu regions
    # ---------------------------------

    # PVEs see the PVE regions and other shared regions L2/DDR/PCIE etc
    # PVEs see APU and AICOREs as device regions
    pve_cva6_regions=core.modify_endpoint_type(only_endpoints,['aicore','apu'])

    cva6_regions=core.create_cpu_regions(pve_cva6_regions)

    template = _jinja_env.get_template("axe_cva6_cpu_regions.txt.jinja2")

    rendered_cpu_regions= template.render(merged_regions=cva6_regions, detailed_regions=pve_cva6_regions)

    # Write the rendered content to the output file
    with open(default_pve_cva6_cpu_regions, 'w') as file:
        file.write(rendered_cpu_regions)


    # ---------------------------------
    # Render CSV file
    # ---------------------------------
    template = _jinja_env.get_template("axe_memory_map.md.jinja2")

    # Write the detailed memory map
    rendered_memory_map= template.render(items=only_endpoints, detailed=True)

    # Write the rendered content to the output file
    with open(default_detailed_memory_map, 'w') as file:
        file.write(rendered_memory_map)

    # Write the top level only memory map
    rendered_memory_map= template.render(items=only_top, detailed=False)

    # Write the rendered content to the output file
    with open(default_memory_map, 'w') as file:
        file.write(rendered_memory_map)

# --------------------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    app()
