from xml.etree import ElementTree as ET
import glob
import re
import os
import csv
from pathlib import Path


def parse(repo_roots: Path, tests_filtered: dict):
    path_test_results = repo_roots / "tests_results.csv"

    # The path to the XML file
    wildcard_path = "Testing/*/Test.xml"
    matching_files = glob.glob(wildcard_path)
    file_path = matching_files[-1]

    # Read the XML file from the disk
    tree = ET.parse(file_path)
    root = tree.getroot()

    # Iterate through each Test element
    test_results = {}
    all_tests = root.findall(".//Testing/Test")

    for test in root.findall(".//Testing/Test"):
        # Extract the test name
        full_name = (
            test.find("Name").text if test.find("Name") is not None else "Unknown"
        )

        pattern = re.compile(r"(.*)_seed_(\d+)$")
        match = pattern.match(full_name)
        if match:
            name = match.group(1)
            seed = match.group(2)
        else:
            name = full_name
            seed = None

        # Determine the exit code based on the test status
        status = test.get("Status")
        if status == "passed":
            exit_code = 0
        else:
            # If failed, try to get the specific exit value, default to 1 if not found
            exit_value_element = test.find(
                ".//NamedMeasurement[@name='Exit Value']/Value"
            )
            exit_code = (
                int(exit_value_element.text) if exit_value_element is not None else 1
            )

        # Extract the execution time
        execution_time_element = test.find(
            ".//NamedMeasurement[@name='Execution Time']/Value"
        )
        execution_time = (
            float(execution_time_element.text)
            if execution_time_element is not None
            else 0.0
        )

        test_results[full_name] = {
            "ctest_name": name,
            "ctest_exit_code": exit_code,
            "ctest_execution_time": execution_time,
            "ctest_seed": seed,
            "ctest_labels": tests_filtered[name].labels,
            "ctest_platforms": tests_filtered[name].platforms,
            "ctest_owner": tests_filtered[name].owner[0],
            "ctest_description": f'"{tests_filtered[name].description}"',
            "pipeline_schedule": os.environ.get("CI_PIPEMASTER_SCHEDULE", None),
        }

    # Get the header from the first test result
    header = list(next(iter(test_results.values())).keys())

    # Open the file for writing
    with open(path_test_results, "w", newline="") as csvfile:
        writer = csv.DictWriter(
            csvfile, quotechar='"', quoting=csv.QUOTE_MINIMAL, fieldnames=header
        )

        # Write the header
        writer.writeheader()

        # Write the data rows
        for details in test_results.values():
            writer.writerow(details)

    return test_results
