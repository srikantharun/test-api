from pathlib import Path
import yaml
import csv
import os
import sys

KEYS = {
    "category": str,
    "optional_description": str,
    "index": int,
    "description": str,
    "criticality": str,
}

def main():
    if len(sys.argv) > 1:
        block = sys.argv[1]
    else:
        block = "AICORE"
    if len(sys.argv) > 2:
        path = Path(sys.argv[2])
    else:
        path = Path(os.getcwd())
    data = []
    with (path / "architectural_requirements.csv").open("r") as csv_file:
        csv_reader = csv.DictReader(csv_file, delimiter=",")
        for row in csv_reader:
            filtered_row = {}
            filtered_row["block"] = block
            filtered_row .update({key: KEYS[key](value) for key, value in row.items() if key in KEYS})
            filtered_row["owner"] = "Gua Hao Khov"
            data.append(filtered_row)
    with (path / "architectural_requirements.yaml").open("w") as yml_file:
        yaml.safe_dump({"requirements": data}, yml_file, width=1000, sort_keys=False, default_style=None)

if __name__ == '__main__':
    main()
