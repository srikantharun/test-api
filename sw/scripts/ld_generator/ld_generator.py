#!/usr/bin/env python3

from typing import List, Optional, Iterable
from datetime import datetime
from jinja2 import Template
from pathlib import Path
import argparse
import yaml
import sys
import os


# global constants
NUMBER_OF_AICORES = 8
NUMBER_OF_PVES    = 2
SCRIPT_DIR = Path(__file__).parent
LD_GENERATOR_TEMPLATE = SCRIPT_DIR / "ld_generator_template.jinja"

# repo root global variable
_repo_root_cache: Optional[Path] = None

def _get_repo_root() -> Path:
    global _repo_root_cache
    if _repo_root_cache is None:
        repo_root = os.environ.get("REPO_ROOT", "")
        if not repo_root:
            print("Linker Generator: Variable $REPO_ROOT required but not set.")
            sys.exit(1)
        _repo_root_cache = Path(repo_root)
    return _repo_root_cache

def validate_input_aicores(aicore_str):
    # Convert the comma-separated list of numbers into a list of integers
    aicores = [int(aicore) for aicore in aicore_str.split(',')]

    # Validate that each aicore is in the range [0, NUMBER_OF_AICORES - 1]
    for aicore in aicores:
        if not (0 <= aicore < NUMBER_OF_AICORES):
            raise argparse.ArgumentTypeError(f"Aicore ID {aicore} is out of range (0 to {NUMBER_OF_AICORES - 1})")
    return aicores

def validate_input_pves(pve_str):
    # Convert the comma-separated list of numbers into a list of integers
    pves = [int(pve) for pve in pve_str.split(',')]

    # Validate that each pve is in the range [0, NUMBER_OF_PVES - 1]
    for pve in pves:
        if not (0 <= pve < NUMBER_OF_PVES):
            raise argparse.ArgumentTypeError(f"PVE ID {pve} is out of range (0 to {NUMBER_OF_PVES - 1})")
    return pves

# generates a list of integers, representing the aicores
def generate_aicores_list(keys: Iterable[str]) -> List[int]:
    aicores = []
    for key in keys:
        if key.startswith('aicore'):
            core_num = int(key.replace('aicore', ''))
            aicores.append(core_num)
    return aicores

# generates a list of integers, representing the pves
def generate_pves_list(keys: Iterable[str]) -> List[int]:
    pves = []
    for key in keys:
        if key.startswith('pve'):
            pve_num = int(key.replace('pve', ''))
            pves.append(pve_num)
    return pves

def validate_aicores(cores : List[int]):
    assert all(0 <= core <= (NUMBER_OF_AICORES - 1) for core in cores), f"Aicores IDs are out of range (0 to {NUMBER_OF_AICORES - 1})"

def validate_pves(pves : List[int]):
    assert all(0 <= pve <= (NUMBER_OF_PVES - 1) for pve in pves), f"PVEs IDs are out of range (0 to {NUMBER_OF_PVES - 1})"

def parse_args():
    parser = argparse.ArgumentParser(
        description="Generate linker script from verifsdk YAML and Jinja template.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "-F",
        "--file",
        required=True,
        help="Path to YAML configuration file."
    )
    parser.add_argument(
        "--aicores",
        required=False,
        type=validate_input_aicores,
        help=f"Choose specific aicores (0 to {NUMBER_OF_AICORES - 1}), e.g. --aicores 0,1,2"
    )
    parser.add_argument(
        "--pves",
        required=False,
        type=validate_input_pves,
        help=f"Choose specific pves (0 to {NUMBER_OF_PVES - 1}), e.g. --pves 0,1"
    )

    return parser.parse_args()

def main():
    args = parse_args()

    # Load YAML config
    with open(args.file, 'r') as file:
        config = yaml.safe_load(file)

    # Load and process the Jinja template
    with open(LD_GENERATOR_TEMPLATE, "r") as file:
        template_content = file.read()
        template = Template(template_content, trim_blocks=True, lstrip_blocks=True)

    # get current time and date
    current_datetime = datetime.now().strftime("%Y-%m-%d, %H:%M:%S")

    # extract the lists
    processors_keys = config['verifsdk']['firmware']['processors'].keys()
    aicores = generate_aicores_list(processors_keys)
    pves    = generate_pves_list(processors_keys)

    # validate the core IDs are in range
    validate_aicores(aicores)
    validate_pves(pves)

    # If the aicores argument is provided, keep only matching aicores
    if args.aicores is not None:
        aicores = [core for core in aicores if core in args.aicores]

    # If the pves argument is provided, keep only matching pves
    if args.pves is not None:
        pves = [pve for pve in pves if pve in args.pves]

    # Render the template with the provided YAML configuration
    rendered_linker_script = template.render(
        current_time = current_datetime,
        aicores=aicores,
        pves=pves
    )

    _repo_root_cache = _get_repo_root()

    # Output the rendered script to a link.ld file
    output_file = _repo_root_cache / "sw/src/lib/common/link.ld"
    with open(output_file, "w") as f:
        f.write(rendered_linker_script)

    return 0

if __name__ == "__main__":
    exit(main())
