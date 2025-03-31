# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Command line interface for the synthesis constraints
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
from typing import Annotated
import pathlib

import typing

import package_lib.cli
import package_lib.utils
import package_lib.config
import typer

import jinja2

import model

import yaml

# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
]

# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

__version__ = "0.1.0"
_logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------------------
# Command Declarations
# --------------------------------------------------------------------------------------------------

app = typer.Typer(
    name="synth_constraints",
    help="A helper script for snthesis constraint management",
    pretty_exceptions_show_locals=True,
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

@app.command("validate")
@package_lib.cli.handle_exceptions
def _validate(
    constraints: Annotated[
        pathlib.Path,
        typer.Argument(
            help="The path to the constraints YAML to validate"
        )
    ],
) -> None:
    """Validate a constraint model agains the template."""

    constraint_data = package_lib.utils.load_data(constraints)
    validated_data = model.ConfigModel.model_validate(constraint_data)
    package_lib.cli.console.print(validated_data)
    package_lib.cli.console.print("Validation Successful!")


@app.command("render_rtla")
@package_lib.cli.handle_exceptions
def _render_rtla(
    constraints: Annotated[
        pathlib.Path,
        typer.Argument(
            help="The path to the constraints YAML to render"
        )
    ],
    output: Annotated[
        pathlib.Path,
        typer.Option(
            "-o",
            "--output",
            help="Specify an output file instead of printing",
        )
    ] = None,
    constraint_mode: Annotated[
        model.ModeEnum,
        typer.Option(
            "--mode",
            help="Select the constraint mode",
            case_sensitive=False,
        )
    ] = model.ModeEnum.func,
) -> None:
    """Render the sdc fot RTLA"""

    def filter_by_mode(
        items: list[typing.Any],
        mode: model.ModeEnum,
    ) -> list[typing.Any]:
        return [item for item in items if item.mode == mode]

    constraint_data = package_lib.utils.load_data(constraints)
    validated_data = model.ConfigModel.model_validate(constraint_data)
    _jinja_env = jinja2.Environment(
        loader=jinja2.FileSystemLoader(package_lib.config.find_project_root() / "hw" / "scripts" / "synth_constraints" / "templates"),
        autoescape=jinja2.select_autoescape(),
        keep_trailing_newline=True,
    )
    _jinja_env.filters["filter_by_mode"] = filter_by_mode

    template = _jinja_env.get_template("rtla.tcl.jinja2")

    constraint_render = template.render(
        constraint_mode=constraint_mode,
        data=validated_data,
    )

    if output:
        with output.open("w") as f:
            f.write(constraint_render)
    else:
        print(constraint_render)


@app.command("schema")
@package_lib.cli.handle_exceptions
def _schema(
) -> None:
    def resolve_refs(schema, defs):
        if isinstance(schema, dict):
            if '$ref' in schema:
                ref = schema['$ref'].split('/$defs/')[-1]
                if ref in defs:
                    return resolve_refs(defs[ref], defs)
                else:
                    return schema
            else:
                return {k: resolve_refs(v, defs) for k, v in schema.items()}
        elif isinstance(schema, list):
            return [resolve_refs(i, defs) for i in schema]
        else:
            return schema
    schema = model.ConfigModel.schema()

    package_lib.cli.console.print(yaml.dump(resolve_refs(schema, schema["$defs"])))


# --------------------------------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------------------------------

if __name__ == "__main__":
    app()
