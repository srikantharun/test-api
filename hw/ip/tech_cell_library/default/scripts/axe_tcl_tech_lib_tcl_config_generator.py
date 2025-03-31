# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

import os

from typing import Dict, TextIO, List
from abc import ABC, abstractmethod

from axe_tcl_base_config_generator import ConfigFileGenerator
from utils import Logger
from pathlib import Path

logger = Logger()

class TclConfigGenerator(ConfigFileGenerator):
    """
    A class designed to generate and write TCL configuration files based on YAML input. 
    This class extends the ConfigFileGenerator superclass, utilizing its common functionalities such as loading YAML configurations,
    writing standardized headers, and resolving path variables, while adding specific functionalities needed for TCL files.

    Attributes:
        yaml_path (str): The file path to the YAML configuration file.
        tcl_output_path (str): The file path where the TCL configuration will be written.
        config (dict): A dictionary containing the loaded YAML configuration, used to generate the TCL file.

    Usage:
        This class should be instantiated with paths to the relevant YAML and TCL files. After instantiation, calling the
        'generate' method will produce a TCL file configured according to the settings specified in the YAML file.
    """

    def __init__(self, yaml_path: str, output_path: str):
        super().__init__(yaml_path)
        self.output_path = output_path
        logger.debug(f"TclConfigGenerator initialized with YAML path: {yaml_path} and output path: {output_path}")

    def write_library_setup(self, tcl_file: TextIO) -> None:
        """
        Writes library setup paths to a TCL file based on a provided configuration dictionary.

        Parameters:
            tcl_file (TextIO): The file object for the output TCL file. 
        Returns:
            None: This function does not return anything. It writes directly to the file provided.
        """
        try:
            tcl_file.write("#########################\n## Library Setup Paths ##\n#########################\n\n")
            for key, value in self.config['paths'].items():
                resolved_value = self.resolve_path_variables(value, self.config['paths'])
                
                #TODO remove this TLUP_FILES special handling
                if 'TLUP_FILES' in key:
                    tcl_file.write(f"set tlup_files [glob -nocomplain -type f [file join $PARASITICS_HOME *nominal*.tlup]]\n")
                    tcl_file.write(f"set TLUP_LIB [join $tlup_files \" \"]\n")
                else:
                    tcl_file.write(f"set {key} \"{resolved_value}\"\n")
            
            logger.debug("Library setup paths written successfully.")
        
        except KeyError as e:
            logger.error(f"KeyError accessing config paths: {e}")
            raise

    def flat_subvalues(self, subvalues_p, depth=0):
        if depth > 30:
            logger.error(f"Possible loop detected in referencing IP's!  Please check the configuration.")
            return -1
        if type(subvalues_p) is list:
            l = []
            for sub_i in subvalues_p:
                if type(sub_i) is list:
                    flat = self.flat_subvalues(sub_i, depth+1)
                    if type(flat) is list:
                        for ii in flat:
                            l.append(self.flat_subvalues(ii, depth+1))
                elif sub_i != "": # get rid of empties
                    l.append(sub_i)
            # uniqify list:
            r = []
            for i in l:
                if i not in r:
                    r.append(i)
            return r
        else:
            return subvalues_p

    def format_memory_configuration(self, mem_ip_values):
        configuration_lines = []
        
        for subkey, subvalues_t in mem_ip_values.items():
            subvalues = self.flat_subvalues(subvalues_t)

            # Resolve all references
            resolved_values = self.resolve_memory_values(subvalues, self.config['paths'])
            
            if not resolved_values:  # Check if the list is empty
                resolved_values_string = " "
            else:
                indent = " \\\n" + " " * (10 + len(subkey))  # can be adjusted based on the context in the TCL file formatting
                resolved_values_string = indent.join(resolved_values)

            configuration_lines.append(f"    set {subkey} \"{resolved_values_string} \"")
        
        return "\n".join(configuration_lines)

    def write_memory_configuration(self, tcl_file: TextIO) -> None:
        """
        Writes memory configurations to a TCL file, detailing specific settings for memory IPs based on the provided configuration dictionary.
        
        Parameters:
            tcl_file (TextIO): The file object for the output TCL file.
        Returns:
            None: This function does not return anything. It writes directly to the file provided.
        """
        try:
            tcl_file.write("\n# Memory configuration based on $MEM_IP\n")
            tcl_file.write("switch -glob $MEM_IP {\n")
            
            for mem_ip_key, mem_ip_values in self.config['mem_ip'].items():
                tcl_file.write(f"  \"{mem_ip_key}\"")
                if mem_ip_values == "INHERIT_NEXT":
                    tcl_file.write(f" -\n")
                else:
                    tcl_file.write(f" {{\n")
                    configuration_lines = self.format_memory_configuration(mem_ip_values)
                    tcl_file.write(configuration_lines)
                    tcl_file.write(f"\n  }}\n")
            
            tcl_file.write("  default {\n    set MEM_LIBS \" \"\n    set REG_FILES \" \"\n  }\n\n}\n")
            logger.debug("Memory configuration written successfully.")
        
        except Exception as e:
            logger.error(f"Error writing memory configurations: {e}")
            raise
        
    def write_eda_tool_configuration(self, tcl_file: TextIO) -> None:
        """
        Writes the EDA tool specific configurations to a TCL file.

        Parameters:
            tcl_file (TextIO): The file object for the output TCL file.
        Returns:
            None: This function does not return anything. It writes directly to the file provided.
        """
        try:
            tcl_file.write(f"\nswitch $eda_tool {{\n")

            if 'eda_tool' in self.config:
                for tool, settings in self.config['eda_tool'].items():
                    tcl_file.write(f"    \"{tool}\" {{\n")
                    if settings:  # Check if there are settings to write
                        for key, value in settings.items():
                            resolved_value = self.resolve_path_variables(value, self.config['paths'])
                            tcl_file.write(f"        set {key} \"{resolved_value}\"\n")
                    tcl_file.write(f"    }}\n")
            else:
                tcl_file.write("    default {\n")
                tcl_file.write("        error \"'eda_tool' must be one of: {self.config['eda_tool'].items()}\"\n")
                tcl_file.write("    }\n}")
            tcl_file.write(f"\n  }}\n")

            logger.debug("EDA tool configuration written successfully.")

        except KeyError as e:
            logger.error(f"KeyError accessing config eda_tool: {e}")
            raise

    def resolve_memory_values(self, values: List[Dict[str, str]], paths_config: Dict[str, str]) -> List[str]:
        """
        Resolves the full paths for memory values based on a configuration dictionary and a list of memory items.

        Parameters:
            values (List[Dict[str, str]]): A list of dictionaries where each dictionary represents a memory configuration.
                                        Each dictionary should contain keys and values where the values may include placeholders
                                        that need resolution based on the paths configuration.
            paths_config (Dict[str, str]): A dictionary containing path keys and their corresponding fully resolved paths.
                                        This is used to replace placeholders in the memory configurations.
        Returns:
            List[str]: A list of strings where each string is a fully resolved path for a memory configuration.
        """
        resolved_values = []
        # standardise suffixes and remove the default value
        default_path_suffix = '_c_lvf_dth'
        
        try:
            for value in values:
                if type(value) == dict:
                    # check if suffix is overriden in config
                    path_suffix = default_path_suffix
                    if 'suffix' in value:
                        path_suffix = value['suffix']
                    
                    resolved_path = self.resolve_path_variables(
                                                                os.path.join(
                                                                "${MEMORIES_HOME}",
                                                                value['path'],
                                                                value['macro'],
                                                                "${FUSION_REF_LIBRARY_DIR}",
                                                                value['macro'] + path_suffix
                                                                ), paths_config)
                    resolved_values.append(resolved_path)
                    
                    # Log a warning if the resolved path does not exist
                    if not Path(resolved_path).exists():
                        logger.warning(f"Resolved TCL path does not exist on disk: {resolved_path}")
                else:
                    resolved_values.append(str(value))
        
            logger.debug("Memory values resolved.")
        
        except KeyError as e:
            logger.error(f"Error resolving memory values: {e}")
            raise

        return resolved_values

    def generate(self) -> None:
        """
        Generates a TCL configuration file by writing all necessary sections to the specified output file.
        
        Parameters:
        - None 
        Returns:
        - None: This function opens the output file, writes content to it, and does not return a value.
        """
        with open(self.output_path, 'w') as tcl_file:
            self.write_header(tcl_file, self.config['meta'])
            self.write_library_setup(tcl_file)
            self.write_memory_configuration(tcl_file)
            self.write_eda_tool_configuration(tcl_file)
