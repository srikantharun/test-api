#!/usr/bin/env python3

import argparse
import dataclasses
import logging
import re
import subprocess
import sys
import time

_logger = logging.getLogger(__name__)

@dataclasses.dataclass
class License:
    feature: str
    issued: int
    used: int

    @property
    def available(self) -> bool:
        return self.issued > self.used


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Wait for a certain license feature to become available"
    )

    parser.add_argument(
        "-f",
        "--features",
        type=str,
        default=["Design-Compiler"],
        help="Feature to check license for",
        nargs="+",
    )
    parser.add_argument(
        "-w",
        "--wait",
        type=int,
        default=3600,
        help="Total seconds to wait for license to become free",
    )
    parser.add_argument(
        "-i",
        "--interval",
        type=int,
        default=60,
        help="Seconds to wait between checks",
    )
    parser.add_argument(
        "--log-level",
        type=str,
        default="INFO",
        help="Log level",
        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"],
    )

    return parser.parse_args()


def run_lmstat(feature: str) -> License:
    try:
        completed_process = subprocess.run(
            args=["lmstat", "-f", feature],
            capture_output=True,
            text=True,
            check=True,
        )

        _logger.debug(f"Called lmstat with: '{' '.join(completed_process.args)}'")
    except subprocess.CalledProcessError as e:
        _logger.error(f"lmstat failed with exit code {e.returncode}")
        _logger.error(e.stderr)
        sys.exit(e.returncode)

    return parse_lmstat_output(feature, completed_process.stdout.split("\n"))


def parse_lmstat_output(feature: str, lmstat_output: list[str]) -> License:
    ISSUED_REGEX = re.compile(r"Total of (\d+) licenses? issued")
    USED_REGEX = re.compile(r"Total of (\d+) licenses? in use")

    for line in lmstat_output:
        if not "Users of" in line:
            _logger.debug(f"Skipping line no Users  : {line}")
            continue

        if not feature in line:
            _logger.debug(f"Skipping line no feature: {line}")
            continue

        if "Error" in line:
            _logger.debug(f"License for {feature} not supported")
            continue

        _logger.debug(f"Found line for feature  : {line}")

        number_issued = int(re.findall(ISSUED_REGEX, line)[0])
        number_used = int(re.findall(USED_REGEX, line)[0])

        license = License(feature, number_issued, number_used)
        _logger.info(f"Found license: {license}")

        return license

    _logger.error(f"Could not find license for {feature} in server output:")
    _logger.error(f"Command: 'lmstat -f {feature}'")
    _logger.error("\n".join(lmstat_output))
    sys.exit(1)


def get_licenses(features: list[str]) -> list[License]:
    licenses = []
    for feature in features:
        licenses.append(run_lmstat(feature))
    return licenses


def all_licenses_available(licenses: list[License]) -> bool:
    for license in licenses:
        if not license.available:
            _logger.info(f"License for {license.feature} currently not available")
            return False
    return True


if __name__ == "__main__":
    args = parse_arguments()

    logging.basicConfig(level=args.log_level)

    _logger.debug(f"Arguments: {args}")

    startTime = time.time()
    while (startTime + args.wait > time.time()):
        _logger.info(f"Checking licenses for: {args.features}")
        licenses = get_licenses(args.features)
        if all_licenses_available(licenses):
            _logger.info(f"All licenses available for: {args.features}")
            sys.exit(0)

        _logger.info(f"Sleeping for {args.interval} seconds")
        time.sleep(args.interval)

    _logger.error(f"Waited {args.wait} seconds for licenses to become free")
    sys.exit(1)
