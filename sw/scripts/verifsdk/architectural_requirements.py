#!/usr/bin/env python3
# check all architectural_requirements.yaml in docs/europa_architecture are formatted properly

import os
import yaml
import glob
import argparse
import csv

import verifsdk
from models import *


class ArchitecturalRequirement:
    """describe an architectural requirement and check its formatting"""

    # requirement format was defined here: https://git.axelera.ai/prod/europa/-/issues/744
    required_keys = [
        "block",
        "category",
        "index",
        "description",
        "criticality",
        "owner",
    ]
    optional_keys = ["prefix", "optional_description"]
    legal_keys = required_keys + optional_keys
    legal_prefixes = ["TOP"]
    legal_blocks = [
        # Impl blocks
        "AICORE",
        "APU",
        "PVE",
        "CVA6V",
        "DECODER",
        "L2",
        "SYS_SPM",
        "SDMA",
        "SOC_MGMT",
        "SOC_PERIPH",
        "PCIE",
        "LPDDR",
        "NOC",
        "TOK_NET",  # Token network is distributed among blocks
        "TOP",
        # IPs
        "SPM",
        "DP_CMD_GEN",
        "ACD",
        "MVM",
        "DWPU"
    ]
    legal_categories = [
        "CONN",
        "CLK",
        "RST",
        "FEAT",
        "BOOT",
        "SEC",
        "MBIST",
        "DFT",
        "PERF",
        "PWR",
        "DBG",
        "NET",
        "APP",
        "E2E",
        "RAL",
        "PRG_EXE",
        "PRG_CMD",
        "EXE_CMD",
        "BYPASS",
        "IRQ",
        "TM",
        "OBS",
        "DIBW",
        "INT16",
        "ICDF",
        "TOKEN",
        "UTILS",
        "PRG_MODE",
        "RAND_SEQ_MODE",
        "CMDBLK"
    ]
    legal_criticalities = ["bronze", "silver", "gold"]

    def __str__(self) -> str:
        req_dict = self.requirement_dict
        return f"[{self.requirement_id}] ({req_dict['criticality']}) {req_dict['description']}"

    def __init__(self, requirement_dict: dict) -> None:
        # check requirement_dict
        self.requirement_dict = requirement_dict
        self.check_required_keys()
        self.check_legal_keys()
        self.check_legal_prefix()
        self.check_legal_block()
        self.check_legal_category()
        self.check_legal_criticality()

        # set optional keys if not present
        for key in self.optional_keys:
            if key not in self.requirement_dict:
                self.requirement_dict[key] = None

        self.block_id = self.get_name_from_fields(["prefix", "block"])
        self.requirement_id = self.get_name_from_fields(
            ["prefix", "block", "category", "optional_description", "index"]
        )

    def get_name_from_fields(self, fields):
        return "_".join(
            [
                str(self.requirement_dict[k])
                for k in fields
                if k in self.requirement_dict
                and self.requirement_dict[k] is not None
                and self.requirement_dict[k] != ""
            ]
        )

    def check_required_keys(self):
        for key in self.required_keys:
            if key not in self.requirement_dict:
                print(f"ERROR: {key} not found for requirement={self.requirement_dict}")
                raise Exception("ArchitecturalRequirementKeyError")

    def check_legal_keys(self):
        for key in self.requirement_dict:
            if key not in self.legal_keys:
                print(
                    f"ERROR: {key} is not legal for requirement={self.requirement_dict}. Should be one of {self.legal_keys}"
                )
                raise Exception("ArchitecturalRequirementKeyError")

    def check_legal_prefix(self):
        if "prefix" in self.requirement_dict:
            prefix = self.requirement_dict["prefix"]
            if prefix not in self.legal_prefixes:
                print(
                    f"ERROR: prefix={prefix} is not legal for requirement={self.requirement_dict}. Should be one of {self.legal_prefixes}"
                )
                raise Exception("ArchitecturalRequirementValueError")

    def check_legal_block(self):
        block = self.requirement_dict["block"]
        if block not in self.legal_blocks:
            print(
                f"ERROR: block={block} is not legal for requirement={self.requirement_dict}. Should be one of {self.legal_blocks}"
            )
            raise Exception("ArchitecturalRequirementValueError")

    def check_legal_category(self):
        category = self.requirement_dict["category"]
        if category not in self.legal_categories:
            print(
                f"ERROR: category={category} is not legal for requirement={self.requirement_dict}. Should be one of {self.legal_categories}"
            )
            raise Exception("ArchitecturalRequirementValueError")

    def check_legal_criticality(self):
        criticality = self.requirement_dict["criticality"]
        if criticality not in self.legal_criticalities:
            print(
                f"ERROR: criticality={criticality} is not legal for requirement={self.requirement_dict}. Should be one of {self.legal_criticalities}"
            )
            raise Exception("ArchitecturalRequirementValueError")


def get_architectural_requirements(
    verbosity_level: int = 0,
) -> dict[str, ArchitecturalRequirement]:
    requirements: dict[str, ArchitecturalRequirement] = {}
    repo_root = os.environ.get("REPO_ROOT")

    for f in glob.glob(
        f"{repo_root}/docs/**/architectural_requirements.yaml",
        recursive=True,
    ):
        if verbosity_level >= 1:
            print(f"-- {f}")
        with open(f, "r") as file:
            yaml_dict = yaml.load(file, Loader=yaml.CSafeLoader)
            for req in yaml_dict["requirements"]:
                archi_req = ArchitecturalRequirement(req)
                req_id = archi_req.requirement_id
                if req_id in requirements:
                    print(f"ERROR: {req_id} already exists")
                    raise Exception("ArchitecturalRequirementIdError")
                if verbosity_level >= 2:
                    print(archi_req)
                requirements[req_id] = archi_req

    return requirements


def get_architectural_requirement_verif_waivers(
    verbosity_level: int = 0,
) -> dict[str, str]:
    repo_root = os.environ.get("REPO_ROOT")
    waivers: dict[str, str] = {}

    for f in glob.glob(
        f"{repo_root}/docs/**/architectural_requirement_verif_waivers.yaml",
        recursive=True,
    ):
        if verbosity_level >= 1:
            print(f"-- {f}")
        with open(f, "r") as file:
            yaml_dict = yaml.load(file, Loader=yaml.CSafeLoader)
            for waiver in yaml_dict["waivers"]:
                req_id = waiver["requirement_id"]
                description = waiver["description"]
                if "owner" not in waiver:
                    print("ERROR: waiver is missing 'owner' key")
                    raise Exception("WaiverKeyError")
                if verbosity_level >= 2:
                    print(f"(waived) [{req_id}] {description}")
                waivers[req_id] = description

    return waivers


def link_tests_and_requirements(
    tests: dict[str, BaseTestInstance],
    requirements: dict[str, ArchitecturalRequirement],
    verif_waivers: dict[str, str],
    verbosity_level: int = 0,
    test_owner_filter: str = "",
    req_criticality_filter: str = "",
    req_block_filter: str = "",
    test_limit: int  = 64 # Max number of tests returned by requirement. If 0, all requirements are returned
) -> dict[str, dict[str, str | list[str] | None]]:
    # generate dicts
    status_to_req_dict: dict[str, set[str]] = {
        "waived": set(),
        "fulfilled": set(),
        "todo": set(),
        "unfulfilled": set(),
    }
    req_to_status_dict: dict[str, str] = {}
    req_to_testnames_dict: dict[str, list[str]] = {}
    requirement_ids = []
    req_filter = req_block_filter or req_criticality_filter
    for req_id in requirements.keys():
        requirement_dict = requirements[req_id].requirement_dict
        if req_criticality_filter and requirement_dict["criticality"] != req_criticality_filter:
            continue
        if req_block_filter and req_block_filter not in requirements[req_id].block_id:
            continue
        requirement_ids.append(req_id)
        req_to_testnames_dict[req_id] = []
    for testname in tests:
        test = tests[testname]
        if test_owner_filter and test_owner_filter not in test.owner:
            continue
        for req_id in test.requirement_ids:
            if req_filter and req_id not in req_to_testnames_dict:
                continue
            req_to_testnames_dict[req_id].append(testname)
    # req is "fulfilled" if it has at least 1 test, none of its tests are TODO
    # req is "todo" if at least 1 of its test is TODO
    # req is "unfulfilled" if it has no associated test
    for req_id in req_to_testnames_dict:
        status = "unfulfilled"
        if req_id in verif_waivers:
            status = "waived"
        else:
            for testname in req_to_testnames_dict[req_id]:
                if "TODO" in tests[testname].labels:
                    status = "todo"
                    break
                else:
                    status = "fulfilled"
        # when filtering by test, "unfulfilled" requirements do not make sense
        if test_owner_filter and status in ["unfulfilled", "waived"]:
            continue
        status_to_req_dict[status].add(req_id)
        req_to_status_dict[req_id] = status

    # assertions
    status_to_req_total_length = sum([len(s) for s in status_to_req_dict.values()])
    if not test_owner_filter:
        assert len(requirement_ids) == status_to_req_total_length
        assert len(requirement_ids) == len(req_to_status_dict)
    for waived_req_id in verif_waivers:
        linked_tests = []
        # If testlist has been filtered, waived requirement might not be part of the list
        if waived_req_id in req_to_testnames_dict:
            linked_tests = req_to_testnames_dict[waived_req_id]
        # If waived requirement is part of the list, make sure that no requirement is linked to it
        if len(linked_tests) > 0:
            print(f"ERROR: req_id={waived_req_id} is both waived and link in the following tests={linked_tests}")
            raise Exception("WaiverRequirementIdError")

    # printing
    for status in status_to_req_dict:
        if verbosity_level < 1:
            continue
        print(f"\n-- {status} ({len(status_to_req_dict[status])}/{status_to_req_total_length})")
        if verbosity_level < 2:
            continue
        for req_id in sorted(status_to_req_dict[status]):
            archi_req = requirements[req_id]
            print(archi_req)
            if status == "waived":
                print(f"-> {verif_waivers[req_id]}")

    # generate req_to_info_dict
    req_to_info_dict: dict[str, dict[str, str | list[str] | None]] = {}
    for req_id in requirement_ids:
        # when filtering by test, "unfulfilled" requirements do not make sense
        if test_owner_filter and req_id not in req_to_status_dict:
            continue
        archi_req = requirements[req_id]
        associated_tests = req_to_testnames_dict[req_id] if req_id in req_to_testnames_dict else []
        if test_limit > 0 and len(associated_tests) > test_limit:
            associated_tests  = associated_tests[0:test_limit]
        req_to_info_dict[req_id] = {
            "req_id": req_id,
            "status": req_to_status_dict[req_id],
            "block_id": archi_req.block_id,
            "associated_tests": " ".join(associated_tests),
            "pipeline_schedule": os.environ.get("CI_PIPEMASTER_SCHEDULE", None),
        }
        for key in archi_req.requirement_dict:
            req_key = key
            if key == "index":
                req_key = f"req_{key}"
            req_to_info_dict[req_id][req_key] = archi_req.requirement_dict[key]

    return req_to_info_dict


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="""Goals:
1. check all architectural_requirements.yaml in docs/europa_architecture are formatted properly
2. link verifsdk/tests_*.yaml tests to those requirements""",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("-v", action="store_true", help="verbose output")
    parser.add_argument("--dump_csv", action="store_true", help="dump csv file, input to pipewatch")
    parser.add_argument("--test_owner", default="", help="only link tests matching test_owner")
    parser.add_argument(
        "--req_criticality", default="", help="only link requirements matching req_criticality"
    )
    parser.add_argument("--req_block", default="", help="only link requirements matching req_block")
    parser.add_argument("--no-limit", action="store_true", help="Dump all tests linked to a requirement. Number of tests is capped at 64 by default.")
    args = parser.parse_args()

    if args.v:
        verbosity_level = 2
    else:
        verbosity_level = 1

    is_filtered = args.test_owner or args.req_criticality or args.req_block

    requirements = get_architectural_requirements(0 if is_filtered else verbosity_level)
    verif_waivers = get_architectural_requirement_verif_waivers(
        0 if is_filtered else verbosity_level
    )
    for waived_req_id in verif_waivers:
        if waived_req_id not in requirements:
            print(
                f"ERROR: waived requirement_id={waived_req_id} is not found in the architectural_requirements.yaml files"
            )
            raise Exception("WaiverRequirementIdError")

    verifsdk_settings = verifsdk.load_verifsdk_settings()
    tests, _ = verifsdk.parse_tests(verifsdk_settings, verifsdk_settings.directories.config)
    test_limit = 0 if args.no_limit else 64
    req_to_info_dict = link_tests_and_requirements(
        tests,
        requirements,
        verif_waivers,
        verbosity_level,
        args.test_owner,
        args.req_criticality,
        args.req_block,
        test_limit
    )

    if args.dump_csv:
        header = list(next(iter(req_to_info_dict.values())).keys())

        with open("data.csv", "w", newline="") as csvfile:
            writer = csv.DictWriter(
                csvfile, quotechar='"', quoting=csv.QUOTE_MINIMAL, fieldnames=header
            )
            writer.writeheader()
            for info in req_to_info_dict.values():
                writer.writerow(info)
