#!/usr/bin/env python3
# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>

import argparse
import os
import pydantic
import re
import subprocess
import sys
import yaml
from datetime import datetime
from jinja2 import Template
from pathlib import Path
from typing import Dict, List

import architectural_requirements
import pipewatch_helper
from firmware import get_builtin_compile_flags
from models import *
from settings import load_verifsdk_settings, Settings


# global constants
SCRIPT_DIR = Path(__file__).parent
CMAKE_FILE = SCRIPT_DIR / "verifsdk.cmake"
CMAKELISTS_TEMPLATE = SCRIPT_DIR / "CMakeListsTemplate.jinja"


def print_prefixed(value, prefix=""):
    str_value = str(value)
    for line in str_value.split("\n"):
        print(prefix, line, sep="")


def filter_tests(tests, args, context_filtered):
    tests_filtered = {
        test.name: test
        for test in tests.values()
        if test.filter(args, context_filtered)
    }
    if args.test_list:
        if not tests_filtered:
            print(
                f"VerifSDK error: Tests '{args.test_list}' not available with given platform/label/flavors combination."
            )
            sys.exit(1)
    return tests_filtered


def append_file_to_cores(context):
    processors = get_all_possible_cores(context["settings"])

    filesPerCore = context["files"]
    attrs = {key: value for sub_dict in context["attrs"].values() for key, value in sub_dict.items()}

    for processor in processors:
        applyToAllCores = []
        if processor == "coreX":
            applyToAllCores = list(filesPerCore.keys())
        elif processor.endswith('X'):
            i = 0
            key_base = processor[:-1]
            while(f"{key_base}{i}" in filesPerCore.keys()):
                applyToAllCores.append(f"{key_base}{i}")
                i += 1
        else:
            applyToAllCores.append(processor)

        # Process attributes
        for name, attr in attrs.items():
            file = list(getattr(attr, processor))
            if len(file) == 0:
                continue

            for applyToAllCore in applyToAllCores:
                if name in filesPerCore[applyToAllCore]:
                    filesPerCore[applyToAllCore][name].extend(list(file))  # Append to existing list
                else:
                    filesPerCore[applyToAllCore][name] = list(file)       # Create a new entry
    context["files"] = filesPerCore

    return context

def filter_context(context, args):
    platforms = context.get("attrs").get("platforms")
    labels = context.get("attrs").get("labels")
    flavors = context.get("attrs").get("flavors")

    # Filter out invalid attributes based on the CLI args
    platforms_filtered = (
        {args.platform: platforms[args.platform]}
        if args.platform is not None and args.platform in platforms.keys()
        else {}
    )

    labels_filtered = (
        {args.label: labels[args.label]}
        if args.label is not None and args.label in labels.keys()
        else {}
    )

    # select flavors
    # step 1: default flavors specified for platform
    flavors_by_prefix = dict()
    for flavor in platforms[args.platform].default_flavors:
        prefix = flavor.split(".", 1)[0]
        flavors_by_prefix[prefix] = flavor
    # step 2: overwrite as needed with flavors from CLI
    if args.flavors:
        for flavor in args.flavors:
            prefix = flavor.split(".", 1)[0]
            flavors_by_prefix[prefix] = flavor
    flavors_filtered = {
        flavor: flavors[flavor] for flavor in flavors_by_prefix.values()
    }

    attrs_filtered = {
        "platforms": platforms_filtered,
        "labels": labels_filtered,
        "flavors": flavors_filtered,
    }
    context["attrs"] = attrs_filtered

    return context


def parse_tests(
    settings: Settings,
    config_dir: Path,
    jtag: bool = False,
    selected_platform: str | None = None,
    regex: str | None = None,
    test_list: str | None = None,
) -> any:
    # Load config
    config_file = config_dir / "config.yaml"
    with config_file.open("r") as file:
        config = yaml.load(file, Loader=yaml.CSafeLoader)

    # Check no tests are defined in config.yaml
    for key in config.keys():
        if key not in ["platforms", "flavors", "labels", "lib"]:
            print(f"VerifSDK error: Invalid top-level key in {config_file}: '{key}'")
            sys.exit(1)

    # Load tests
    tests_files = config_dir.glob("tests_*.yaml")
    tests_per_file = dict()
    for tests_file in tests_files:
        with tests_file.open("r") as f:
            data = yaml.load(f, Loader=yaml.CSafeLoader)
            for key in data.keys():
                if key != "tests":
                    print(
                        f"VerifSDK error: Invalid top-level key in {tests_file}: '{key}'"
                    )
                    sys.exit(1)
            tests_per_file[tests_file] = data["tests"]

    # Check each test name is unique
    file_for_test = dict()
    for path, tests in tests_per_file.items():
        for test in tests:
            name = test.get("name", "")
            if not name:
                print(
                    f"VerifSDK error: {path} contains at least one test with no name specified."
                )
                sys.exit(1)
            if name in file_for_test:
                print(f"VerifSDK error: test '{name}' exists in multiple files:")
                print(f"  - {file_for_test[name]}")
                print(f"  - {path}")
                sys.exit(1)
            file_for_test[name] = path

    # Merge tests into single list
    config["tests"] = []
    for file_tests in tests_per_file.values():
        config["tests"].extend(file_tests)

    # Check requirement_ids exist
    all_archi_reqs = architectural_requirements.get_architectural_requirements()
    for test in config["tests"]:
        for req_id in test["requirement_ids"]:
            if req_id not in all_archi_reqs:
                print(f"test {test['name']}: requirement_id {req_id} does not exist")
                print(
                    "list all requirement ids with: check_architectural_requirements -v"
                )
                sys.exit(1)

    # Build context used for model validation
    context = {
        "attrs": {},
        "lib_sources": config["lib"],
        "settings": settings,
    }
    processors = settings.firmware.processors
    files = {}
    for processor in processors:
        files[processor] = {}
    context["files"] = files


    platform_model = create_test_instance_model(BasePlatformAttributes, settings)
    label_model = create_test_instance_model(BaseLabelAttributes, settings)
    flavor_model = create_test_instance_model(BaseFlavorAttributes, settings)
    test_model = create_test_instance_model(BaseTestInstance, settings, isTestModel=True)

    # Parse the provided config
    try:
        labels: Dict[str, LabelAttributes] = {
            label["name"]: label_model.model_validate(label, context=context)
            for label in config["labels"]
        }
    except pydantic.ValidationError as err:
        print("VerifSDK error while parsing labels:")
        print_prefixed(err, prefix="> ")
        sys.exit(1)
    context["attrs"]["labels"] = labels

    try:
        flavors: Dict[str, FlavorAttributes] = {
            flavor["name"]: flavor_model.model_validate(flavor, context=context)
            for flavor in config["flavors"]
        }
    except pydantic.ValidationError as err:
        print("VerifSDK error while parsing flavors:")
        print_prefixed(err, prefix="> ")
        sys.exit(1)
    context["attrs"]["flavors"] = flavors

    try:
        platforms: Dict[str, PlatformAttributes] = {
            platform["name"]: platform_model.model_validate(
                platform, context=context
            )
            for platform in config["platforms"]
        }
    except pydantic.ValidationError as err:
        print("VerifSDK error while parsing platforms:")
        print_prefixed(err, prefix="> ")
        sys.exit(1)
    # If JTAG is target, replace platform with JTAG target
    if jtag:
        assert selected_platform, "jtag == True requires platform != None"
        design, platform = selected_platform.split(".", 1)
        platforms[selected_platform].run_script = (
            f"./run_jtag.sh --design {design} --platform {platform}"
        )
    context["attrs"]["platforms"] = platforms

    # update config['tests'] based on the regex provided
    if regex and test_list:
        assert False, "Unreachable"
    elif regex:
        pattern = re.compile(regex)
        filtered_tests = [
            test for test in config["tests"] if pattern.search(test["name"])
        ]
        config["tests"] = filtered_tests
    elif test_list:
        filtered_tests = [
            test for test in config["tests"] if test["name"] in test_list
        ]
        if len(filtered_tests) != len(test_list):
            print(f"VerifSDK error: Tests with names '{test_list}' don't exist.")
            sys.exit(1)
        config["tests"] = filtered_tests

    try:
        tests: Dict[str, BaseTestInstance] = {
            test["name"]: test_model.model_validate(test, context=context)
            for test in config["tests"]
        }
    except pydantic.ValidationError as err:
        print("VerifSDK error while parsing tests:")
        print_prefixed(err, prefix="> ")
        sys.exit(1)

    return tests, context


def parse_arguments():
    """
    Parses command-line arguments.
    """
    parser = argparse.ArgumentParser(
        description="This script is used to generate the CMakeList.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "-G",
        default="Ninja",
        help="The build system generator (passed to CMake).",
    )
    parser.add_argument(
        "-P", "--platform", default="", required=False, help="The target platform."
    )
    parser.add_argument("-L", "--label", default=None, help="The target test label.")
    parser.add_argument(
        "-F",
        "--flavors",
        action="append",
        default=None,
        help="The target flavor. This arguments optionally takes zero, one, or more group arguments.",
    )
    parser.add_argument(
        "-C",
        "--directory",
        type=Path,
        default=None,
        help="Change to another directory before running CMake.",
    )
    parser.add_argument(
        "--no-cmake",
        default=False,
        action="store_true",
        help="Only generates CMakeLists file without running CMake.",
    )
    parser.add_argument(
        "--no-ninja",
        default=False,
        action="store_true",
        help="Only configure CMakeLists file using CMake without running Ninja.",
    )
    parser.add_argument(
        "-I",
        "--input",
        type=Path,
        default=None,
        help="Path to directory with VerifSDK config and test lists (override).",
    )
    parser.add_argument(
        "-v",
        "-V",
        "--verbose",
        default=False,
        action="store_true",
        help="Verbose output",
    )
    parser.add_argument(
        "--jtag",
        default=False,
        action="store_true",
        help="Enable JTAG on specified platform.",
    )
    parser.add_argument("-R", "--regex", default=None, help=argparse.SUPPRESS)
    parser.add_argument(
        "--only",
        dest="test_list",
        metavar="TEST_NAME",
        nargs='+',
        default=None,
        help="Name of tests to run (exact match).",
    )
    parser.add_argument(
        "--no-optimize",
        default=False,
        action="store_true",
        help="Do not optimize code (-O0).",
    )
    parser.add_argument(
        "--verify-yaml",
        default=False,
        action="store_true",
        help="Just verify the yaml files only.",
    )
    parser.add_argument(
        "--list",
        default=False,
        action="store_true",
        help="List all selected tests.",
    )
    parser.add_argument(
        "--ctest",
        nargs=argparse.REMAINDER,
        default=None,
        help='ALWAYS PUT THIS ARGUMENT AT THE END. ALL additional flags after the "--ctest" are forwarded to ctest, i.e "--ctest -N -R test" calls "ctest -N -R test" during execution.',
    )

    args, custom_flags = parser.parse_known_args()

    # Conditional requirement for -P
    if not args.verify_yaml and not args.platform:
        parser.error(
            "The following arguments are required: -P/--platform if --verify-yaml is not set."
        )
    # Do not set both -R and --only
    if args.regex and args.test_list:
        parser.error(
            "Specifying a regex (-R/--regex) is not allowed when --only is set."
        )

    return args, custom_flags


def validate_argument_single(
    arg_type: str, args: List[str], valid_values: Dict[str, any]
) -> None:
    """
    Validates whether `arg` is a valid option for `arg_type`.
    Prints an error and exits the program on failure.
    """
    for arg in args:
        if arg not in valid_values:
            print(
                f"VerifSDK error: '{arg}' is not a valid {arg_type} (one of {', '.join(valid_values)}).",
                file=sys.stderr,
            )
            sys.exit(1)


def validate_arguments(args, context) -> None:
    """
    Validates whether certain flag arguments are valid options.
    Prints an error and exits the program on failure.
    """
    # Platform is required, not guarding for None.
    validate_argument_single("platform", [args.platform], context["attrs"]["platforms"])
    if args.label is not None:
        validate_argument_single("label", [args.label], context["attrs"]["labels"])
    if args.flavors is not None:
        validate_argument_single("flavors", args.flavors, context["attrs"]["flavors"])

        # ensure at most one flavor is provided for each flavor prefix
        flavors_by_prefix = group_by_prefix(args.flavors)
        for prefix, flavors in flavors_by_prefix.items():
            if len(flavors) > 1:
                flavors_str = ", ".join(flavors)
                print(
                    f"VerifSDK error: specified multiple flavors for tag {prefix}.* ({flavors_str}), only one is allowed"
                )
                sys.exit(1)


def get_compile_flags(args, custom_flags: List[str]) -> List[str]:
    flags = custom_flags
    if args.no_optimize:
        flags.append("-O0")
    else:
        flags.append("-O2")
    return flags

def apply_repeat_count_multiplier(tests_filtered, context_filtered):

    labels = context_filtered["attrs"]["labels"].values()

    repeat_count_multiplier = next(iter(labels)).repeat_count_multiplier if len(labels) == 1 else 1

    for t in tests_filtered.values():
        if t.repeat_count == 0:
            continue

        repetitions = t.repeat_count * repeat_count_multiplier
        while len(t.seeds) < repetitions:
            t.seeds.append(random.randint(0, 2**31 - 1))

    return tests_filtered


def run_command(command, verbose):
    with subprocess.Popen(command, stdout=subprocess.PIPE, text=True) as proc:
        if verbose:
            for line in proc.stdout:
                print(line, end="")
        else:
            stdout, _ = proc.communicate()
        proc.wait()

        if proc.returncode != 0:
            if not verbose:
                print(stdout)
            exit(proc.returncode)


def main() -> int:
    # Parse the command-line arguments
    args, custom_flags = parse_arguments()

    settings = load_verifsdk_settings()

    if "TODO" == args.platform:
        # Expand 'TODO' to 'todo.TODO'.
        args.platform = f"todo.{args.platform}"
    if "." not in args.platform:
        # Make 'top.' prefix implicit for platforms.
        args.platform = f"top.{args.platform}"
    # Use config directory from settings if not specified on CLI.
    config_dir = args.input if args.input else settings.directories.config

    tests, context = parse_tests(
        settings,
        config_dir,
        jtag=args.jtag,
        selected_platform=args.platform,
        regex=args.regex,
        test_list=args.test_list,
    )

    # Return if we only check the yaml files
    if args.verify_yaml:
        print("[PASSED] YAML files are correct.")
        return 0

    validate_arguments(args, context)  # exits on failure
    context_filtered = filter_context(context, args)
    context_with_files_per_core = append_file_to_cores(context_filtered)
    tests_filtered = filter_tests(tests, args, context_with_files_per_core)
    tests_filtered = apply_repeat_count_multiplier(tests_filtered, context_with_files_per_core)
    additional_flags = get_compile_flags(args, custom_flags)

    if args.list:
        for t in tests_filtered:
            print(f"{t}")
        return 0

    command_line = f"'python {' '.join(sys.argv)}'"
    time_now = datetime.now().strftime("%Y-%m-%d, %H:%M:%S")

    template = Template(
        CMAKELISTS_TEMPLATE.read_text(),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    rendered = template.render(
        settings=settings,
        command_line=command_line,
        time_now=time_now,
        builtin_includes=[CMAKE_FILE],
        builtin_flags=get_builtin_compile_flags(context_with_files_per_core),
        tests=tests_filtered,
        additional_flags=additional_flags,
        lib_sources=context_with_files_per_core["lib_sources"],
        attributes=context_with_files_per_core["attrs"],
        files=context_with_files_per_core["files"],
    )

    if args.directory:
        args.directory.mkdir(exist_ok=True)
        os.chdir(str(args.directory))

    # create sw/ pointing to source dir
    local_sw_dir = Path("sw")
    local_sw_dir.mkdir(exist_ok=True)
    for sw_content in settings.directories.sw.glob("*"):
        if not (local_sw_dir/sw_content.name).exists():
            run_command(["ln", "-sf", sw_content, local_sw_dir/sw_content.name], False)

    # Write the rendered text to the CMakeLists.txt file
    cmake_lists_path = local_sw_dir / "CMakeLists.txt"
    cmake_lists_path.write_text(rendered)

    # Return if no CMake
    if args.no_cmake:
        return 0

    if args.verbose:
        print("##########################################")
        print("# CMake")
        print("##########################################")

    run_command(
        ["cmake", "-G", args.G, "-S", "sw" , "-B", "."], args.verbose
    )

    # Return if no Ninja
    if args.no_ninja:
        return 0

    if args.verbose:
        print("##########################################")
        print("# Ninja")
        print("##########################################")

    run_command(["ninja"], args.verbose)

    if args.ctest is not None:
        ctest = ["ctest", "-T", "test"]
        ctest.extend(args.ctest)

        if args.verbose:
            print("##########################################")
            print("# Ctest")
            print("##########################################")

        with subprocess.Popen(ctest, stdout=subprocess.PIPE, text=True) as proc:
            for line in proc.stdout:
                print(line, end="")
            proc.wait()

            pipewatch_helper.parse(settings.directories.root, tests_filtered)

            return proc.returncode

    return 0


if __name__ == "__main__":
    exit(main())
