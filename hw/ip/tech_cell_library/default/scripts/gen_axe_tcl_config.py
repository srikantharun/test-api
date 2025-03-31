#!/usr/bin/env python3

# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

import argparse
import pathlib
import logging
import yaml

from typing import NoReturn

from axe_tcl_tech_lib_tcl_config_generator import TclConfigGenerator
from axe_tcl_mbist_tcl_config_generator import TclMbistConfigGenerator
from axe_tcl_bender_config_generator import BenderConfigGenerator
from utils import Logger

logger = Logger()

def setup_logging(level: str):
    levels = {
        'debug': logging.DEBUG,
        'info': logging.INFO,
        'warning': logging.WARNING,
        'error': logging.ERROR,
        'critical': logging.CRITICAL
    }
    logger.set_level(levels.get(level.lower(), logging.INFO))
    
def main(
    yaml_path: pathlib.Path, 
    tcl_output_path: pathlib.Path, 
    tcl_mbist_output_path: pathlib.Path, 
    bender_output_path: pathlib.Path, 
    debug_level: str,
) -> NoReturn:
    """Main function to generate TCL file and Bender file from specified YAML configuration path.
    
    Args:
        yaml_path (pathlib.Path): Path to the YAML configuration file.
        tcl_output_path (pathlib.Path): Path to the output TCL file.
        tcl_mbist_output_path (pathlib.Path): Path to the output TCL file.
        bender_output_path (str): Path to the output bender file.
        debug_level (str): The debug level for logging.
    """
    logger.info("##### Started Generating files ######")
    logger.debug(f"YAML config path: {yaml_path}, TCL output path: {tcl_output_path}, MBIST TCL output path: {tcl_mbist_output_path}, Bender output path: {bender_output_path}")

    try:
        # Create an instance of the bender generator, and call the generator
        logger.info("Initializing Bender Generator")
        bender_generator = BenderConfigGenerator(yaml_path, bender_output_path)
        bender_generator.generate()
        logger.info("Bender file generation completed")
    
        # Create an instance of the tcl generator, and call the generator
        logger.info("Initializing TCL Generator")
        tcl_generator = TclConfigGenerator(yaml_path, tcl_output_path)
        tcl_generator.generate()
        logger.info("TCL file generation completed")
    
        # Create an instance of the MBIST tcl generator, and call the generator
        logger.info("Initializing MBIST TCL Generator")
        tcl_generator = TclMbistConfigGenerator(yaml_path, tcl_mbist_output_path)
        tcl_generator.generate()
        logger.info("MBIST TCL file generation completed")
    
    except FileNotFoundError as e:
        logger.error(f"File not found: {e}")
        if debug_level == 'debug':
            raise
    
    except yaml.YAMLError as e:
        logger.error(f"Error parsing YAML: {e}")
        if debug_level == 'debug':
            raise
        
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate techlib and bender files from YAML configuration.")
    parser.add_argument("-y",
                        "--yaml_path",
                        type=pathlib.Path, 
                        default="axe_tcl_config.yml", 
                        help="Path to the YAML configuration file.")
    parser.add_argument("-t",
                        "--tcl_output_path", 
                        type=pathlib.Path, 
                        default="tc_techlib.tcl", 
                        help="Path to output the TCL file.")
    parser.add_argument("-m",
                        "--tcl_mbist_output_path", 
                        type=pathlib.Path, 
                        default="tc_mbist_techlib.tcl", 
                        help="Path to output the TCL file.")
    parser.add_argument("-b",
                        "--bender_output_path", 
                        type=pathlib.Path, 
                        default="bender.yml", 
                        help="Path to output the Bender file.")
    parser.add_argument("-d",
                        "--debug_level",
                        type=str,
                        choices=['debug', 'info', 'warning', 'error', 'critical'],
                        default='info',
                        help="Set the logging level (debug, info, warning, error, critical).")

    args = parser.parse_args()
    
    setup_logging(args.debug_level)
    logger.debug(f"Arguments: {args}")
    
    main(yaml_path=args.yaml_path,
         tcl_output_path=args.tcl_output_path,
         tcl_mbist_output_path=args.tcl_mbist_output_path,
         bender_output_path=args.bender_output_path,
         debug_level=args.debug_level)
