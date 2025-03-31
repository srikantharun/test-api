# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Command line interface for performance regression generation
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------
import os
import logging
from typing import Annotated, Optional
import pathlib
import package_lib.cli
import typer
import jinja2
import utils
import trex_config
import core

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
default_templates= os.path.join(REPO_ROOT,"scripts/trex/templates")
default_testdir= os.path.join(REPO_ROOT,"sw/src/tests/generated/")
trex_drv_dir= os.path.join(REPO_ROOT,"sw/src/lib/common/drv/trex/")
default_testlistdir= os.path.join(REPO_ROOT,"verifsdk/")
# --------------------------------------------------------------------------------------------------
# Command Declarations
# --------------------------------------------------------------------------------------------------

app = typer.Typer(
    name="trex",
    help="A script for generating performance test infrastructure based on a scenario.yaml input",
    pretty_exceptions_show_locals=False,
    add_completion=False,
)


package_lib.cli.create_main_callback(
    app,
    enable_logging=True,
    enable_version=True,
    version=__version__,
    package_name="trex",
)

# --------------------------------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------------------------------
@app.command("render")
@package_lib.cli.handle_exceptions
def _render(

    config: Annotated[
        pathlib.Path,
        typer.Option(
            "--config",
            "-c",
            help="Path to the configuration file that defines the scenarios to be tested (YAML).",
            show_default=False,
        ),
    ],

) -> None:
    """Render the test files needed for the scenarios indicated in the YAML file."""
    _logger.info("Rendering the tests from the config file.")

    templates=default_templates

    configuration, filename = trex_config.read_config_file(config)
    scenarios=configuration.scenarios

    # Set-up render env
    _jinja_env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(templates),
        autoescape=jinja2.select_autoescape(),
    )
    _jinja_env.filters['hex'] = utils.hex
    _jinja_env.filters['indent'] = utils.indent
    _jinja_env.tests['contains_strings'] = utils.contains_strings

    test_template = _jinja_env.get_template("test_dma.c.jinja2")
    testlist_template = _jinja_env.get_template("tests.yaml.jinja2")

    # Process the scenarios
    testlist = core.process_scenario(scenarios,
                                    test_template,
                                    testlist_template,
                                    default_testdir,
                                    default_testlistdir,
                                    trex_drv_dir,
                                    filename)

    # Output the results
    print(f"Tests generated in PATH: {default_testdir}:")
    print(testlist)


@app.command("parse")
@package_lib.cli.handle_exceptions
def _parse(

    config: Annotated[
        pathlib.Path,
        typer.Option(
            "--config",
            "-c",
            help="Path to the configuration file that defines the scenarios to be tested (YAML).",
            show_default=False,
        ),
    ],

    label: Annotated[
        str,
        typer.Option(
            "--label",
            "-l",
            help="Verifsdk label used for the testsuite.",
            show_default=False,
        ),
    ],

    test_name: Annotated[
        Optional[str],  # Added test_name as an optional argument
        typer.Option(
            "--test-name",
            "-t",
            help="Specific test name to run. If provided, label will be ignored.",
            show_default=False,
        ),
    ] = None,  # Default to None if not provided

) -> None:
    """Parse the log files after a regression and create a results.csv"""
    _logger.info("Rendering the tests from the config file.")

    templates=default_templates

    configuration, filename = trex_config.read_config_file(config)
    scenarios=configuration.scenarios

    test_list=[]
    # If a specific test is specified then run the results only for this test
    # else run for every test with the same label
    if not test_name:
        for scenario in scenarios:
            test_list.append(scenario.name)
    else:
        test_list.append(test_name)
    core.gen_results_df(label=label,test_list=test_list,test_path=os.getcwd())


# --------------------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    app()

