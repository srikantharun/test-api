#!/usr/bin/env python3

import yaml
import argparse
import os
from typing import Dict
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--print-platforms", action="store_true")
parser.add_argument("--print-labels", action="store_true")
parser.add_argument("--print-flavors", action="store_true")
parser.add_argument("--print-tests", action="store_true")
parser.add_argument("-p", "--platform", type=str, required=False, default=None)
parser.add_argument("-l", "--label", type=str, required=False, default=None)

args = parser.parse_args()

repo_root = os.getenv("REPO_ROOT")
if repo_root is None:
    exit(1)

config_dir = Path(repo_root) / "verifsdk"
config_file = config_dir / "config.yaml"
if not config_file.exists():
    exit(1)
with config_file.open("r") as file:
    config = yaml.load(file, Loader=yaml.CSafeLoader)

data = []
if args.print_platforms:
    data += [p["name"] for p in config["platforms"]]

if args.print_labels:
    data += [p["name"] for p in config["labels"]]

if args.print_flavors:
    data += [p["name"] for p in config["flavors"]]


class ConfigChecker:
    def __init__(self, platform, label):
        self.platform = platform
        self.prefix = self.get_prefix()
        self.label = label

    def get_prefix(self) -> str:
        prefix = ""
        if self.platform is not None:
            split = self.platform.split(".", 1)
            if len(split) > 1:
                prefix = f"{split[0]}.*"
        return prefix

    def check_test(self, test: Dict[str, str]) -> bool:
        try:
            if self.label is not None and self.label not in test["labels"]:
                return False
            if self.platform is not None:
                if self.platform not in test["platforms"] and self.prefix not in test["platforms"]:
                    return False
            return True
        except KeyError:
            return False


if args.print_tests:
    checker = ConfigChecker(args.platform, args.label)
    tests_files = config_dir.glob("tests_*.yaml")
    tests_per_file = dict()
    for tests_file in tests_files:
        with tests_file.open("r") as f:
            tests = yaml.load(f, Loader=yaml.CSafeLoader)
            for t in tests["tests"]:
                if checker.check_test(t):
                    data.append(t["name"])

print(" ".join(data))
