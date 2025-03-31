# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Command line interface for pad_solder
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
from typing import Annotated
import pathlib

import package_lib.cli
import typer

import jinja2

import core
import pad_config

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

__version__ = "0.1.0"
_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Command Declarations
# --------------------------------------------------------------------------------------------------

app = typer.Typer(
    name="pad_solder",
    help="A helper script for generating chip pads modules",
    pretty_exceptions_show_locals=False,
    add_completion=False,
)


package_lib.cli.create_main_callback(
    app,
    enable_logging=True,
    enable_version=True,
    version=__version__,
    package_name="pad_solder",
)

# --------------------------------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------------------------------

@app.command("render")
@package_lib.cli.handle_exceptions
def _render(
    templates: Annotated[
        pathlib.Path,
        typer.Option(
            "--templates",
            "-t",
            help="Path to the template directory file.",
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
    """Render the chip pads module."""
    _logger.info("Rendering the chip pads module.")

    configuration = pad_config.read_config_file(config)

    pad_list = core.pads_from_config(configuration)
    functional_list, oscillator_list = core.split_functional_and_oscillator(pad_list)

    port_groups = core.extract_portgroups(pad_list)

    _jinja_env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(templates),
        autoescape=jinja2.select_autoescape()
    )

    template = _jinja_env.get_template("axe_tcl_pad_sf5a.sv.jinja2")

    print(
        template.render(
            top_level_name=config.stem,
            port_groups=port_groups,
            pad_list=functional_list,
            oscillator_list=oscillator_list,
            number_of_pad_rows=core.number_of_pad_rows(pad_list),
        )
    )

# --------------------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    app()
