#!/usr/bin/env python3
"""
Script to update a regress YAML file with test data from a testlist YAML file.

Author: Abhilash Chadhar
"""

import yaml
import argparse
import os

def update_regress_yaml(regress_yaml_path, testlist_yaml_path, output_path):
    # Load the testlist YAML file
    with open(testlist_yaml_path, 'r') as f:
        testlist_data = yaml.safe_load(f)

    # Extract the base name of the testlist file without the extension
    testlist_name = os.path.splitext(os.path.basename(testlist_yaml_path))[0]

    # Load the regress YAML file
    with open(regress_yaml_path, 'r') as f:
        regress_data = yaml.safe_load(f)

    # Create an empty list to hold updated tests
    updated_tests = []

    # Process each test in the testlist
    for tl_test in testlist_data:
        test_name = tl_test['test']
        new_test_name = f"{testlist_name}.{test_name}"

        # Find matching test in the regress data
        matching_test = next((test for test in regress_data['tests'] if test['name'].endswith(test_name)), None)
        
        if matching_test:
            # Update the name
            matching_test['name'] = new_test_name
        else:
            # If no matching test found, create a new entry
            matching_test = {
                'name': new_test_name,
                'description': 'TODO',
                'labels': ['CVA6V_DV_SIM_SPIKE'],
                'requirement_ids': [],
                'platforms': ['uvm.CVA6V_DV_SIM_SPIKE'],
                'owner': 'Abhilash Chadhar'
            }
        
        updated_tests.append(matching_test)

    # Update the tests in the regress data
    regress_data['tests'] = updated_tests

    # Define a custom dumper to handle indentation and inline lists
    class MyDumper(yaml.Dumper):
        def increase_indent(self, flow=False, indentless=False):
            return super(MyDumper, self).increase_indent(flow, False)

    def str_presenter(dumper, data):
        """Custom presenter to handle multi-line strings."""
        if '\n' in data:
            return dumper.represent_scalar('tag:yaml.org,2002:str', data, style='|')
        return dumper.represent_scalar('tag:yaml.org,2002:str', data)

    def list_representer(dumper, data):
        """Custom presenter to handle lists as inline if they contain only one element."""
        if len(data) == 1:
            return dumper.represent_sequence('tag:yaml.org,2002:seq', data, flow_style=True)
        return dumper.represent_sequence('tag:yaml.org,2002:seq', data, flow_style=False)

    yaml.add_representer(str, str_presenter, Dumper=MyDumper)
    yaml.add_representer(list, list_representer, Dumper=MyDumper)

    # Save the updated regress YAML file with correct formatting
    with open(output_path, 'w') as f:
        yaml.dump(regress_data, f, Dumper=MyDumper, default_flow_style=False, sort_keys=False, width=80, indent=2)

if __name__ == "__main__":
    # Define command-line arguments
    parser = argparse.ArgumentParser(description="Update regress YAML with testlist data.")
    parser.add_argument("-regress_yaml", required=True, help="Path to the regress YAML file.")
    parser.add_argument("-testlist_yaml", required=True, help="Path to the testlist YAML file.")
    parser.add_argument("-output_yaml", required=True, help="Path to save the updated regress YAML file.")

    # Parse command-line arguments
    args = parser.parse_args()

    # Update the regress YAML file with the testlist data
    update_regress_yaml(args.regress_yaml, args.testlist_yaml, args.output_yaml)
