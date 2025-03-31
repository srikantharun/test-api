# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""Core utilities to filter out different sections of the scenario file.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------

import logging
import collections
from typing import Dict, List
import package_lib.exceptions
import re
import copy
import trex_config
from arch import Arch
import utils
import pandas as pd
import os


# --------------------------------------------------------------------------------------------------
# Exports
# --------------------------------------------------------------------------------------------------

__all__ = [
    "filter_tasks_per_init"
]
# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)

class CoreError(package_lib.exceptions.HandledException):
    """Errors Caused by functional Errors of the core logic."""

# --------------------------------------------------------------------------------------------------
# Implementation
# --------------------------------------------------------------------------------------------------

def filter_tasks_per_init(
    scenario: trex_config.Scenarios,
    Arch:  Dict,
) -> Dict[str, List ]:
    """Extracts the tasks that each initiator needs to perform."""
    result = {}

    # Split the tasks per initiator
    for initiator in Arch.keys():
        initiator_tasklist=[]
        for task in scenario.tasks:
            if initiator in task.resource:
                initiator_tasklist.append(copy.deepcopy(task))
        result[initiator]= initiator_tasklist

    # Update the initiator in the list to match the dict key
    for key in result.keys():
       value = result[key]
       for task in value:
           task.resource=[key]

    return result


def process_scenario(scenarios,test_template,testlist_template,default_testdir,default_testlistdir,trex_drv_dir,filename):
    """Process a single scenario and generate test files."""
    # Filter tasks and add additional information

    testlist=[]
    data_size_list=[]


    for scenario in scenarios:
        tasklist = filter_tasks_per_init(scenario, Arch)


        # Prepare file paths and directories
        test_name = f"{scenario.name}"
        testdir = f"{default_testdir}{test_name}/"
        utils.ensure_directory_exists(testdir)

        for key,value in tasklist.items():

            testfile = f"{test_name}_{key.lower()}.c"
            test_path = f"{testdir}{testfile}"

            if key =='APU':
                core_list=[key for key, value in tasklist.items() if value not in ('APU',None, '', [], {}, ())]

                rendered_scenario = test_template.render(
                    tasklist=value,
                    data_check=scenario.data_check,
                    data_random=scenario.data_random,
                    perf_counter=scenario.perf_counter,
                    core_list=core_list
                )
                utils.write_rendered_content(test_path, rendered_scenario)
                testlist.append(testfile)

            else:
                if value:
                    core_list=[]

                    rendered_scenario = test_template.render(
                        tasklist=value,
                        data_check=scenario.data_check,
                        data_random=scenario.data_random,
                        perf_counter=scenario.perf_counter,
                        core_list=core_list
                    )
                    utils.write_rendered_content(test_path, rendered_scenario)
                    testlist.append(testfile)

        # Update the required size list for these scenarios
        for task in scenario.tasks:
            for size in task.src_xbytesize:
                data_size=f'DATA_SIZE_{size}B'
                if data_size not in data_size_list:
                    data_size_list.append(data_size)


    # Generate reference data for the transfer sizes indicated in the scenarios if these do not
    # exist on the list
    hfile_path = f"{trex_drv_dir}generated_data.h"
    existing_data_sizes=utils.grep_data_sizes(hfile_path)
    missing_data_sizes = [item for item in data_size_list if item not in existing_data_sizes]
    utils.append_generated_data_header(hfile_path,  missing_data_sizes)

    # Render the full testlist in the yaml file
    rendered_testlist = testlist_template.render(
        scenarios=scenarios,
    )
    testlist_filepath= f"{default_testlistdir}tests_{filename}.yaml"
    utils.write_rendered_content(testlist_filepath, rendered_testlist)



    return testlist

def gen_results_df(label,test_list, test_path):
    # Define the regular expression to extract the desired fields
    regex_pattern = r"Task:\s*(?P<Task>\S+),\s*DMA:\s*(?P<DMA>\S+),\s*channel\s*(?P<channel>\d+),\s*SRC:\s*(?P<SRC>\S+),\s*DST:\s*(?P<DST>\S+),\s*Size:\s*(?P<Size>\d+),\s*Init cycles:\s*(?P<Init_cycles>\d+),\s*config cycles:\s*(?P<config_cycles>\d+),\s*transfer cycles:\s*(?P<transfer_cycles>\d+),\s*expected cycles:\s*(?P<expected_cycles>\d+)"

    # Create an empty DataFrame to store the results
    df = pd.DataFrame(columns=["Label","Task", "DMA", "channel", "SRC", "DST", "Size", "Init_cycles", "config_cycles", "transfer_cycles", "expected_cycles"])

    # Iterate through the list of log files
    for test in test_list:
        file_path = f"{test_path}/sw_build/{test}/sim.log"
        with open(file_path, 'r') as file:
            for line in file:
                # Search for lines matching the regex pattern
                match = re.search(regex_pattern, line)
                if match:
                    # Extract the matched groups and add them as a new row in the DataFrame
                    row = match.groupdict()
                    row['Label']=label
                    df = pd.concat([df, pd.DataFrame([row])], ignore_index=True)

    # Convert numeric columns to integers
    numeric_columns = ["channel", "Size", "Init_cycles", "config_cycles", "transfer_cycles", "expected_cycles"]
    df[numeric_columns] = df[numeric_columns].astype(int)

    # Write the DataFrame to a CSV file
    output_file = os.path.join(test_path, "trex_regression_results.csv")
    df.to_csv(output_file, index=False)
    print(f"Regression results df for {label} written to {output_file}.")

    return df
