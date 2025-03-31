#!/usr/bin/env python3

# Check for mismatched path on ROM macro code file
# - This path is set manually after the macro generation
# - In case of faulty path, we could test wrong code silently


import argparse
import logging
import pathlib
import os
import yaml

from utils import extract_yaml_content_with_includes


files_to_scan = [ ".v", "_emulation.v" ]
parameter_to_check = "PreloadFilename"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Utility script to check if romcode file is set correctly")
    parser.add_argument(
        "--tcl-cfg",
        help="Path to the tech cell library configuration",
        type=pathlib.Path,
        default=os.getenv("REPO_ROOT", "REPO_ROOT_not_set") + "/hw/ip/tech_cell_library/default/data/axe_tcl_config.yml"
    )
    parser.add_argument(
        "--log-level",
        default="info",
        help="Verbosity of the script.",
        type=str,
        choices=["critical", "error", "warning", "info", "debug", "notset"],
    )

    args = parser.parse_args()
    logging.basicConfig(level=args.log_level.upper())

    logging.info(f"scanning {args.tcl_cfg}")
    cfg = yaml.safe_load(extract_yaml_content_with_includes(args.tcl_cfg))

    macros_to_scan = list()

    ips = cfg["ips"]
    for ip in ips:
        macros = cfg["ips"][ip]["macros"]
        for macro in macros:
            # filter absolute path macros
            if not isinstance(macro, str):
                # lookup for rom macros
                if "_vromp_" in macro["macro"]:
                    logging.info(f"found {macro}")
                    macros_to_scan.append(macro)

    logging.info(f"found {len(macros_to_scan)} ROM macro(s)")
    paths = cfg["paths"]
    base_macro_path = pathlib.Path(paths["MEMORIES_HOME"].replace("${TECH_HOME}", paths["TECH_HOME"]))
    error_count = 0

    for macro in macros_to_scan:
        macro_dir_path = base_macro_path.joinpath(macro["path"]).joinpath(macro["macro"])
        logging.debug(f"{macro_dir_path}")

        expected_romcode_path = macro_dir_path.joinpath(f"{macro['macro']}.romcode")
        logging.debug(f"{expected_romcode_path}")

        for f in files_to_scan:
            file_path = macro_dir_path.joinpath(f"{macro['macro']}{f}")
            logging.debug(f"{file_path}")

            with open(file_path, "r") as macro_file:
                for line in macro_file:
                    if line.strip().startswith("parameter") and parameter_to_check in line:
                        logging.debug("found parameter line")
                        romcode_path = pathlib.Path(line.split('"')[1])
                        if romcode_path != expected_romcode_path:
                            logging.error(f"romcode path is not matching:\nexpected: {expected_romcode_path}\nfound: {romcode_path}")
                            error_count += 1
                        else:
                            logging.debug(f"romcode path ok for {macro}")
                        break

    if error_count != 0:
        logging.error(f"{error_count} fail(s) detected (out of {len(macros_to_scan)} ROM macro(s))")
        exit(1)
    else:
        logging.info(f"all {len(macros_to_scan)} ROM macro(s) checked successfully")
