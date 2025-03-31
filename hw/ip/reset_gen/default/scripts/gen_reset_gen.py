#!/usr/bin/env python3
# (C) Copyright Axelera AI 2021
# All Rights Reserved
# *** Axelera AI Confidential ** *
r"""Mako template to Hjson register description
"""
import hjson
import sys
import argparse
from io import StringIO

from mako.template import Template


def main():
    parser = argparse.ArgumentParser(prog="reset_gen")
    parser.add_argument('input',
                        nargs='?',
                        metavar='file',
                        type=argparse.FileType('r'),
                        default=sys.stdin,
                        help='input template file')
    parser.add_argument('--cfg',
                        '-c',
                        type=argparse.FileType('r'),
                        required=True,
                        help='Reset gen configuration file.')

    args = parser.parse_args()

    # Determine output: if stdin then stdout if not then ??

    reg_tpl = Template(args.input.read())
    # Read HJSON description of System.
    with args.cfg as file:
        cfg = hjson.loads(file.read(), use_decimal=True)

    out = StringIO()
    out.write(
        reg_tpl.render(cfg=cfg))

    print(out.getvalue())
    out.close()


if __name__ == "__main__":
    main()
