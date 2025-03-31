#!/usr/bin/env python3
"""
Script Name: cva6v_yml_to_elf.py
Description: This script automates the process of running regression tests based on a YAML configuration file
             Used for parsing OSS & Imperas test suites, from yaml to ELF
             It sets up the environment and compiles tests
             Specifically, it performs the following tasks:
             1. Reads and parses a YAML configuration file or a C test file.
             2. Substitutes environment variables and default options for paths and compilation options.
             3. Compiles tests using GCC (if source files are provided).
             All detailed command outputs are saved to a single log file, whose name is of the form:
                 cva6v_compile_<listname>.log
             while the terminal shows only a summary (e.g. "Compiling X tests.." and "Compile complete for X tests.")
             
Usage:
    ./cva6v_yml_to_elf.py --testlist <path_to_yaml> [--testname <test_name>] [--gcc_options "<options>"]
                          [--linker_file <linker_file>] [--clean] [--arch <arch>]

For help, run:
    ./cva6v_yml_to_elf.py --help
"""

import argparse
import os
import shutil
import subprocess
import yaml
import logging

# Global logger variable; will be configured in main.
logger = None

def configure_logging(testlist_path):
    """
    Configure and return a logger that writes to a file named
    cva6v_compile_<listname>.log, where <listname> is derived from the testlist filename.
    """
    base_name = os.path.splitext(os.path.basename(testlist_path))[0]
    log_file_name = f"cva6v_compile_{base_name}.log"
    _logger = logging.getLogger("compile_log")
    _logger.setLevel(logging.DEBUG)
    # Remove any existing handlers (in case the logger was previously configured)
    if _logger.hasHandlers():
        _logger.handlers.clear()
    fh = logging.FileHandler(log_file_name)
    fh.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    fh.setFormatter(formatter)
    _logger.addHandler(fh)
    return _logger

def read_yaml_file(yaml_path):
    """Read a YAML file and return its contents as a Python object."""
    root = os.path.abspath(os.path.dirname(yaml_path))
    with open(yaml_path, 'r') as file:
        # Replace the placeholder <path_var> with the directory containing the YAML file.
        filedata = file.read().replace("<path_var>", root)
        return yaml.safe_load(filedata)

def execute_command(cmd):
    """
    Execute a command using subprocess, log its output,
    and print an error message to the terminal only if the command fails.
    """
    logger.info(f"Executing command: {cmd}")
    result = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    logger.info(result.stdout)
    if result.returncode != 0:
        error_msg = f"Error executing command:\n{cmd}\n{result.stdout}"
        print(error_msg)
        logger.error(error_msg)
        return False
    return True

def parse_arguments():
    parser = argparse.ArgumentParser(
        description="Run regression tests from a YAML configuration file or a C test file. "
                    "Detailed logs are written to a single log file (cva6v_compile_<listname>.log), while the terminal shows only summary output."
    )
    parser.add_argument("--testlist", type=str, required=True, help="Path to the YAML configuration file")
    parser.add_argument("--testname", type=str, help="Optional specific test name to run", default=None)
    parser.add_argument("--gcc_options", type=str, help="Additional GCC options", default='')
    parser.add_argument("--linker_file", type=str, help="GCC Linker file option", default=None)
    parser.add_argument("--clean", action='store_true', help="Clean build directory")
    parser.add_argument("--arch", type=str, default="rv64imafc_zicsr_zifencei_zve32f_zfh_zfhmin", help="Architecture to build on")
    return parser.parse_args()

def process_test(test, args):
    """
    Compile the test based on YAML and command-line options.
    Detailed logging is performed, while the terminal output remains minimal.
    """
    testname       = test.get('test')
    test_arch      = test.get('arch', None)
    gcc_options    = test.get('gcc_opts', '') + " " + args.gcc_options
    include_dirs   = test.get('include_dirs', [])
    include_flags  = ' '.join([f'-I{d}' for d in include_dirs])
    asm_tests      = test.get('asm_tests')
    # Generate the output (ELF) path by replacing the source directory with the build directory.
    elf = asm_tests.replace('.S', '')
    elf = elf.replace(args.src_dir, args.build_dir)
    elf_dir = os.path.dirname(elf)

    if args.clean:
        if os.path.isfile(elf):
            logger.info(f"Removing {elf}")
            os.remove(elf)
        return True
    else:
        logger.info(f"Compiling {elf}")
        if not os.path.exists(elf_dir):
            os.makedirs(elf_dir)
        cmd = (
            f"riscv64-unknown-elf-gcc -O0 {asm_tests} {include_flags} -T {args.linker_file} {gcc_options} "
            f"-o {elf} -march={args.arch if test_arch is None else test_arch} -mabi=lp64f"
        )
        return execute_command(cmd)

def process_all_tests(args):
    tests = read_yaml_file(args.testlist)
    total_tests = len(tests)
    print(f"Compiling {total_tests} tests..")
    logger.info(f"Compiling {total_tests} tests..")
    errors = 0
    for test in tests:
        if not process_test(test, args):
            errors += 1
    print(f"Compile complete for {total_tests} tests.")
    logger.info(f"Compile complete for {total_tests} tests.")
    if errors:
        error_summary = f"{errors} test(s) failed."
        print(error_summary)
        logger.error(error_summary)

if __name__ == "__main__":
    args = parse_arguments()
    # Define source and build directories based on the location of the testlist YAML file.
    args.src_dir = os.path.abspath(os.path.dirname(args.testlist))
    args.build_dir = os.path.join(args.src_dir, 'build')

    # Configure logging: the log file name will be based on the testlist filename.
    logger = configure_logging(args.testlist)

    if args.clean:
        if os.path.exists(args.build_dir):
            clean_msg = f"Cleaning build directory: {args.build_dir}"
            print(clean_msg)
            logger.info(clean_msg)
            shutil.rmtree(args.build_dir, ignore_errors=True)

    if args.testname is None:
        process_all_tests(args)
    else:
        # If a specific test is specified via --testname, search for it in the YAML file.
        tests = read_yaml_file(args.testlist)
        found = False
        for test in tests:
            if test.get('test') == args.testname:
                found = True
                if not process_test(test, args):
                    print(f"Compilation failed for test: {args.testname}")
                break
        if not found:
            not_found_msg = f"Test '{args.testname}' not found in the test list."
            print(not_found_msg)
            logger.error(not_found_msg)
