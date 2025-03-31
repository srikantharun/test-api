# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

import os

from typing import Dict, TextIO
from abc import ABC, abstractmethod

from axe_tcl_base_config_generator import ConfigFileGenerator
from utils import Logger
from pathlib import Path

logger = Logger()

class BenderConfigGenerator(ConfigFileGenerator):
    """
    A class designed to generate and manage the creation of Bender configuration files based on YAML inputs. 
    This class extends the ConfigFileGenerator superclass, utilizing its foundational functionalities such as loading YAML configurations,
    writing standardized headers, and resolving path variables, while adding specific functionalities needed for Bender files.

    Attributes:
        yaml_path (str): The file path to the YAML configuration file from which configurations are loaded.
        bender_output_path (str): The file path where the Bender configuration file will be written.
        config (dict): A dictionary containing the loaded YAML configuration, which includes details necessary for generating the Bender file.

    Usage:
        This class should be instantiated with paths to the relevant YAML and Bender files. After instantiation, calling the
        'generate' method will produce a Bender configuration file according to the settings specified in the YAML file.
    """

    def __init__(self, yaml_path: str, output_path: str):
        super().__init__(yaml_path)
        self.output_path = output_path

    def write_package_info(self, file: TextIO) -> None:
        """
        Writes the package information section to the given file based on the metadata provided in the data dictionary.

        Parameters:
        - file (TextIO): A file object to which the package information will be written.
        Returns:
        - None: This function performs a write operation and does not return a value.
        """
        try:
            file.write(f"package:\n")
            file.write(f"  name: {self.config['meta']['name']}\n")
            file.write(f"  description: \"{self.config['meta']['description']}\"\n")
            file.write(f"  authors:\n")
            
            for author in self.config['meta']['authors']:
                file.write(f"    - \"{author}\"\n")
            
            logger.debug("Package info written successfully.")
        
        except KeyError as e:
            logger.error(f"Error writing package info: {e}")
            raise

        file.write("\n")

    def write_dependencies(self, file: TextIO) -> None:
        """
        Writes the dependencies section to the given file, listing each dependency and its associated path.

        Parameters:
        - file (TextIO): A file object to which the dependencies will be written.
        Returns:
        - None: This function performs a write operation and does not return a value.
        """ 
        try:
            file.write("dependencies:\n")
            
            for key, value in self.config['dependencies'].items():
                file.write(f"  {key}: {{ path: \"{value['path']}\" }}\n")
            
            file.write("\n")
            logger.debug("Dependencies written successfully.")
        
        except KeyError as e:
            logger.error(f"Error writing dependencies: {e}")
            raise

    def write_sources_info(self, file: TextIO) -> None:
        """
        Writes the source files information to the given file, organizing them by levels of dependencies.

        Parameters:
        - file (TextIO): A file object to which the source files information will be written.
        Returns:
        - None: This function performs a write operation and does not return a value.
        """
        try:
            file.write("# Source files grouped in levels.\n")
            file.write("# Files in level 0 have no dependencies on files in this package.\n")
            file.write("# Files in level 1 only depend on files in level 0, files in level 2 on files in levels 1 and 0, etc.\n")
            file.write("# Files within a level are ordered alphabetically.\n")
            file.write("sources:\n")
            
            for source in self.config['sources']:
                file.write(f"  - target: {source['target']}\n")
                file.write(f"    files:\n")
                
                # Default suffix for source files is .v
                file_suffix = '.v'
                # Check if file suffix is overriden in the config
                if 'file_suffix' in source:
                    file_suffix = source['file_suffix']
                # Check if the 'files' key exists in the source dictionary
                if 'files' in source:
                    for entry in source['files']:
                        # Check if the entry is a string, indicating a filename
                        if isinstance(entry, str):
                            file.write(f"      - {entry}\n")            
                        # Check if the entry is a list, indicating a list of resolved macros
                        elif isinstance(entry, list):
                            for ent in entry:
                                resolved_path = self.resolve_path_variables(
                                            os.path.join(
                                            "${MEMORIES_HOME}",
                                            ent['path'],
                                            ent['macro'],
                                            ent['macro']  + file_suffix
                                            ), self.config['paths'])

                                file.write(f"      - {resolved_path}\n")
                                if not Path(resolved_path).exists():
                                    logger.warning(f"Resolved Bender source path does not exist on disk: {resolved_path}")
                        # Handle unrecognized entry types
                        else:
                            #print("Unrecognized entry type:", entry)
                            file.write("Unrecognized entry type: " + str(entry) + "\n")
                else:
                    # Log and write an error message if 'files' key is not found
                    logger.warning("No 'files' section found.")

                # newline at end of target
                file.write("\n")
            logger.debug("Source files info written successfully.")
        
        except KeyError as e:
            logger.error(f"Error writing source files info: {e}")
            raise

    def generate(self) -> None:
        """
        Generates a Bender configuration file by writing all necessary sections to the specified output file.
        
        Parameters:
        - None
        Returns:
        - None: This function opens the output file, writes content to it, and does not return a value.
        """
        with open(self.output_path, 'w') as bender_file:
            self.write_header(bender_file, self.config['meta'])
            self.write_package_info(bender_file)
            self.write_dependencies(bender_file)
            self.write_sources_info(bender_file)
