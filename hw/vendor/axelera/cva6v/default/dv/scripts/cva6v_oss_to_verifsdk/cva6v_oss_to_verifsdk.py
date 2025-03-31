#!/usr/bin/env python3

"""
Script Name: cva6v_oss_to_verifsdk
Description:
    Converts open source yml tpo verifsdk yaml
    Not a production script

"""

import argparse
import os, shutil
import subprocess
import yaml
import datetime

def read_yaml_file(yaml_path):
    """Read a YAML file and return its contents as a Python object."""


    root = os.path.abspath(os.path.dirname(yaml_path))
    with open(yaml_path, 'r') as file:
        return yaml.safe_load(file)


def parse_arguments():
    parser = argparse.ArgumentParser(description="Run regression tests from a YAML configuration file or a C test file.")
    parser.add_argument("--input",  type=str, required=True,   help="Path to the oss YAML configuration file")
    parser.add_argument("--output", type=str, required=True,   help="Path to the verifsdk YAML configuration file")
    parser.add_argument("--prefix", type=str,                  help="Testname Prefix", default="")
    parser.add_argument("--labels", type=str, action='append', help="Testname labels")

    return parser.parse_args()

def process(args):

    # Input
    tests = read_yaml_file(args.input)

    labels = ['CVA6V_DV_TESTS', 'CVA6V_DV_OSS_TESTS'] + args.labels
    owner  = 'Abhilash Chadhar'
    flags  = '[]'

    # Test template
    fin = open(os.path.join(os.environ['REPO_ROOT'], 'hw/vendor/axelera/cva6v/default/dv/scripts/cva6v_oss_to_verifsdk/template.txt'), 'r')
    template = fin.read()
    fin.close()

    # Output
    fout = open(args.output, 'w')
    fout.write('tests:\n')

    done = []
    for t in tests:
        if t['test'] not in done:

            elf = t['asm_tests'].replace('<path_var>', 'ELF=$REPO_ROOT/hw/vendor/axelera/cva6v/default/dv/deps/tests/build')
            elf = os.path.splitext(elf)[0]

            fout.write(template.format(
                name        = args.prefix + '_' + t['test'],
                description = '"TODO"',
                labels      = str(labels).replace("'", ""),
                owner       = owner,
                flags       = f'[{elf}]'
            ))
        done.append(t['test'])
    fout.close()


if __name__ == "__main__":
    args           = parse_arguments()

    process(args)
