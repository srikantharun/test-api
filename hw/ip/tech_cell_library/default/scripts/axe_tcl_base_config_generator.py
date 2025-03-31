# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

import pathlib
import re
import datetime
from abc import ABC, abstractmethod

import yaml

from typing import Dict, TextIO

from utils import Logger, extract_yaml_content_with_includes, parse_and_load_yaml

logger = Logger()

class ConfigFileGenerator(ABC):
    """
    An abstract class providing common functionalities for generating configuration files from YAML settings. 
    This class includes methods to load YAML configurations, write standardized headers, and resolve path variables 
    based on configurations.

    Attributes:
        yaml_path (str): The file path to the YAML configuration file that will be loaded.
        config (dict): A dictionary holding the loaded YAML configuration.

    Usage:
        This class should be inherited by specific configuration generator classes that need to produce configuration files
        for different applications. The inheriting class can utilize the provided methods to standardize header
        writing and path resolution.
    """

    def __init__(self, yaml_path: pathlib.Path) -> None:
        """Initialise the config generator.
        
        Parameters:
            yaml_path (str): The path to the YAML configuration file.
        Returns:
            None
        """
        logger.debug(f"Initializing ConfigFileGenerator with YAML path: {yaml_path}")

        self.yaml_path = yaml_path
        self.config    = self.load_yaml_config()

    def load_yaml_config(self) -> Dict:
        """Load a YAML configuration file.
        
        Parameters:
            yaml_path (str): The path to the YAML configuration file.
        Returns:
            dict: The loaded YAML configuration.
        """
        if not self.yaml_path.exists():
            logger.error(f"FileNotFoundError: The YAML file at {self.yaml_path} was not found.")
            raise FileNotFoundError(f"The YAML file at {self.yaml_path} was not found.")
        
        with self.yaml_path.open('r') as yaml_file:
            try:
                yaml_content = extract_yaml_content_with_includes(self.yaml_path)
                config = parse_and_load_yaml(yaml_content)
                logger.debug(f"YAML configuration loaded successfully from {self.yaml_path}")
                return config
            
            except yaml.YAMLError as e:
                logger.error(f"Error parsing YAML file: {e}")
                raise

    def write_copyright_header(self, file: TextIO) -> None:
        """Writes the Copyright header section of the file.
        
        Parameters:
            file (TextIO): The file object to write in.
        Returns:
            None: This function does not return anything. It writes directly to the file provided.
        """
        current_year = datetime.datetime.now().year
        file.write(f"# (C) Copyright Axelera AI {current_year}\n")
        file.write(f"# All Rights Reserved\n")
        file.write(f"# *** Axelera AI Confidential ***\n")
        logger.debug("Copyright header written.")

    def write_header(self, file: TextIO, meta_data: Dict[str, any]) -> None:
        """Writes the header section of the file.
        
        Parameters:
            file (TextIO): The file object for the output file.
            meta_data (Dict[str, any]): Metadata for the header.
        Returns:
            None: This function does not return anything. It writes directly to the file provided.
        """
        self.write_copyright_header(file)
        file.write(f"#\n")
        file.write(f"# Description: {meta_data.get('description', 'No description provided')}\n")
        file.write(f"# Authors: ")
        authors = meta_data.get('authors', [])
        file.write(f", ".join(authors))
        file.write(f"\n#\n")
        file.write(f"# This file is auto-generated\n\n")
        logger.debug("Header written with metadata.")

    def resolve_path_variables(self, path: pathlib.Path, config_paths: Dict[str, str]) -> str:
        """Resolve placeholders in the path using the provided path configurations.
        
        Parameters:
            path (str): The path string with placeholders.
            config_paths (Dict[str, str]): The dictionary of paths for placeholder replacement.
        Returns:
            str: The resolved path.
        """
        # specifying search pattern to find variable references
        # These references typically look like ${variable_name}.
        pattern = re.compile(r'\$\{([^}]+)\}')
        logger.debug(f"Resolving path: {path}")        

        # recursive function to resolve references
        def resolve(path: str) -> str:
            while True:
                match = pattern.search(path)
                if not match:
                    return path
                
                key = match.group(1)
                if key in config_paths:
                    path = path.replace(f'${{{key}}}', resolve(config_paths[key]))
                    logger.debug(f"Resolved path variable {key} to {config_paths[key]}")
                else:
                    logger.warning(f"Unresolved path variable: {key}")
                    return path
        
        resolved_path = resolve(path)
        logger.debug(f"Fully Resolved path: {resolved_path}")        
        return resolved_path

    @abstractmethod
    def generate(self) -> None:
        """
        Generates a TCL configuration file by writing all necessary sections to the specified output file.
        To be implemented by concrete implementation.
        
        Parameters:
        - None: 
        Returns:
        - None: This function should open the output file, writes content to it, and should not return a value.
        """
        pass


# Example usage within another class that inherits from ConfigFileGenerator
class ExampleConfigGenerator(ConfigFileGenerator):
    def __init__(self, yaml_path: str, output_path: str) -> None:
        super().__init__(yaml_path)
        self.output_path = output_path
        logger.debug(f"ExampleConfigGenerator initialized with output path: {self.output_path}")

    def generate(self) -> None:
        with open(self.output_path, 'w') as file:
            # Additional configuration generation logic here, example:
            # self.write_header(file, self.config.get('meta', {}))
            pass
