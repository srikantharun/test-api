#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

"""
For documentation of Verible Formatter, refer to the following document:
docs/flow_docs/flows/verible_formatter.md
"""

import shutil
import sys
import os
import argparse
import subprocess
import logging
import difflib
import glob

from pathlib import Path

logger = logging.getLogger('verible_format')

VERIBLE_ARGS = [
    "--formal_parameters_indentation=indent",
    "--named_parameter_indentation=indent",
    "--named_port_indentation=indent",
    "--port_declarations_indentation=indent",
    "--named_port_alignment=align"
]


def get_repo_top():
    return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip()


def get_verible_executable_path():
    return shutil.which('verible-verilog-format')


def get_verible_version(verible_exec_path):
    return subprocess.run([verible_exec_path, '--version'],
                          check=True,
                          universal_newlines=True,
                          stdout=subprocess.PIPE).stdout.strip().split('\n')[0]


def process_file(filename_abs,
                 verible_exec_path,
                 inplace=False,
                 show_diff=False,
                 show_cst=False):
    args = [verible_exec_path] + VERIBLE_ARGS
    if inplace:
        args.append('--inplace')
    args.append(filename_abs)

    verible = subprocess.run(args,
                             check=False,
                             universal_newlines=True,
                             stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE)

    ret = 0

    if len(verible.stderr) > 0:
        logger.error(f'ERROR: {verible.stderr}')
        ret = 1
    elif not inplace:
        with open(filename_abs, 'r') as fp:
            orig = fp.read().split('\n')

        formatted = verible.stdout.split('\n')

        diff = list(
            difflib.unified_diff(orig,
                                 formatted,
                                 lineterm='',
                                 n=3,
                                 fromfile=filename_abs,
                                 tofile=filename_abs + '.formatted'))
        ret = len(diff) > 0

        if not show_diff and len(diff) > 0:
            logger.info(f'INFO: File differs: {filename_abs}')

        if show_diff and len(diff) > 0:
            logger.info('')
            for line in diff:
                logger.info(line)

        if len(diff) > 0 and show_cst:
            cst = subprocess.run(
                ['verible-verilog-syntax', '--printtree', filename_abs],
                check=False,
                universal_newlines=True,
                stdout=subprocess.PIPE)
            logger.info(cst.stdout)

    return ret


def main():
    repo_top_dir = get_repo_top()

    parser = argparse.ArgumentParser(
        description='Format source code with Verible formatter')
    parser.add_argument('-q',
                        '--quiet',
                        action='store_true',
                        default=False,
                        help='print only errors and warnings')
    parser.add_argument('-v',
                        '--verbose',
                        action='store_true',
                        default=False,
                        help='print extra debug messages')
    parser.add_argument('--show-diff',
                        action='store_true',
                        default=False,
                        help='print diff (when files differ)')
    parser.add_argument('--show-cst',
                        action='store_true',
                        default=False,
                        help='print CST tree')
    parser.add_argument('--progress',
                        action='store_true',
                        default=False,
                        help='show progress')
    parser.add_argument('--inplace',
                        action='store_true',
                        default=False,
                        help='format files in place (overwrite original files)')
    parser.add_argument('-l',
                        '--allowlist',
                        action='store_true',
                        default=False,
                        help='process only files from allow list')
    parser.add_argument('-af',
                        '--allowlist-file',
                        type=str,
                        default=Path(repo_top_dir) / 'hw' / 'scripts' / 'gen_files' / 'verible_format_allowlist.txt',
                        help='Path to the allow list file (default: %(default)s)')
    parser.add_argument('-i',
                        '--ignore',
                        action='store_true',
                        default=False,
                        help='Ignore file in this list.')
    parser.add_argument('-if',
                        '--ignore-file',
                        type=str,
                        default=Path(repo_top_dir) / 'hw' / 'scripts' / 'gen_files' / 'verible_format_ignore.txt',
                        help='Path to the ignore file list (default: %(default)s)')
    parser.add_argument('-a',
                        '--all',
                        action='store_true',
                        default=False,
                        help='process all files in repository (.sv and .svh)')
    parser.add_argument('-f',
                        '--files',
                        metavar='file',
                        type=str,
                        nargs='+',
                        default=[],
                        help='process provided files')
    args = parser.parse_args()

    if not args.quiet:
        logger.addHandler(logging.StreamHandler())
        logger.setLevel(logging.INFO)

        if args.verbose:
            logger.setLevel(logging.DEBUG)

    logger.debug(f"DEBUG: Script Arguments: {args}")

    if args.inplace:
        logger.warning(
            'WARNING: Operating in-place - so make sure to make a backup or '
            'run this on an experimental branch')

    verible_exec_path = get_verible_executable_path()

    if not verible_exec_path:
        logger.error(
            'ERROR: verible-verilog-format either not installed or not visible in PATH'
        )
        sys.exit(1)
    else:
        logger.info('INFO: Using Verible formatter version: ' +
                    get_verible_version(verible_exec_path))

    logger.debug(f'DEBUG: repo_top: {repo_top_dir}')
    logger.debug(f'DEBUG: verible exec: {verible_exec_path}')
    logger.debug(f'DEBUG: verible args: {VERIBLE_ARGS}')

    verible_files = []

    for f in args.files:
        # First check if the given path exists as is
        if os.path.exists(f):
            logger.debug(f"DEBUG: Found given file: {f}")
            verible_files.append(f)

        else:
            # Path doesn't exist, check if it's relative
            if not os.path.isabs(f):
                # It's relative, prepend the repo_top_dir and check if it exists
                logger.debug(f"DEBUG: Did not find relative file path: {f}, searching for file relative to repo root: {repo_top_dir}")
                f_modified = os.path.join(repo_top_dir, f)

                if os.path.exists(f_modified):
                    verible_files.append(f_modified)
                    logger.debug(f"DEBUG: Found relative file path: {f}, in repo root: {repo_top_dir}")
                else:
                    logger.error(f"ERROR: Relative file path: {f} not found even after prepending repo top directory: {repo_top_dir}")

            else:
                # It's absolute but doesn't exist, log an error
                logger.error(f"ERROR: File not found: {f}")

    if args.allowlist:
        with open(args.allowlist_file,
                  'r') as fp:
            for line in fp:
                if line[0] == '#':
                    continue

                filename = line.strip()

                if len(filename) == 0:
                    continue

                filename_abs = os.path.join(repo_top_dir, filename)
                verible_files.extend(glob.glob(filename_abs, recursive=True))

    ignore_list = list()

    if args.ignore:
        with open(args.ignore_file,
                  'r') as fp:
            for line in fp:
                if line[0] == '#':
                    continue

                filename = line.strip()

                if len(filename) == 0:
                    continue

                filename_abs = os.path.join(repo_top_dir, filename)
                ignore_list += glob.glob(filename_abs, recursive=True)

    if args.all:
        for root, dirs, files in os.walk(repo_top_dir):
            for f in files:
                if not (f.endswith('.sv') or f.endswith('.svh')):
                    continue

                filename_abs = os.path.join(root, f)
                if os.path.exists(
                        filename_abs) and filename_abs not in ignore_list:
                    verible_files.append(filename_abs)

    logger.info(f'INFO: files to format: {verible_files}')

    ret = 0
    total_no_files = len(verible_files)  # Total number of files to process
    for i, f in enumerate(verible_files):
        r = process_file(f,
                         verible_exec_path,
                         inplace=args.inplace,
                         show_diff=args.show_diff,
                         show_cst=args.show_cst)
        ret = ret + r

        # Check if progress display is enabled
        if args.progress:
            # Calculate the percentage of completion
            percent_complete = (i + 1) / total_no_files * 100

            # Print progress status
            logger.info(f'\rINFO: Processed {i + 1}/{total_no_files} ({percent_complete:.2f}%)')
            sys.stdout.flush()  # Ensure the progress is displayed immediately

    return ret > 0


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
