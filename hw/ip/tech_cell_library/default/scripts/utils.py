# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***

import logging
import yaml
import os
from pathlib import Path

class SingletonType(type):
    _instances = {}
    def __call__(cls, *args, **kwargs):
        if cls not in cls._instances:
            instance = super().__call__(*args, **kwargs)
            cls._instances[cls] = instance
        return cls._instances[cls]

class Logger(metaclass=SingletonType):
    def __init__(self, name='gen-axe-tcl', log_file='gen-axe-tcl.log', level=logging.DEBUG):
        # Prevent re-initialization if instance already exists
        if not hasattr(self, 'logger'):            
            self.logger = logging.getLogger(name)
            self.logger.setLevel(level)

            # Create handlers for the file and console
            file_handler = logging.FileHandler(log_file, mode='w')  # Set mode to 'w' to overwrite
            console_handler = logging.StreamHandler()

            # Set levels for handlers
            file_handler.setLevel(logging.DEBUG)  # File handler logs everything debug and above
            console_handler.setLevel(logging.DEBUG)  # Console handler logs everything debug and above

            # Create formatters and add it to handlers based on level
            if self.logger.level == logging.DEBUG:
                log_format = logging.Formatter('%(asctime)s - %(levelname)s: %(message)s', datefmt='%m/%d %H:%M')
            else:
                # Simpler format for higher levels (INFO, WARNING, ERROR)
                log_format = logging.Formatter('%(levelname)s: %(message)s')


            file_handler.setFormatter(log_format)
            console_handler.setFormatter(log_format)

            # Add handlers to the logger
            self.logger.addHandler(file_handler)
            self.logger.addHandler(console_handler)

    def set_level(self, level):
        self.logger.setLevel(level)
        for handler in self.logger.handlers:
            handler.setLevel(level)
            
    def debug(self, message):
        self.logger.debug(message)

    def info(self, message):
        self.logger.info(message)

    def warning(self, message):
        self.logger.warning(message)

    def error(self, message):
        self.logger.error(message)

def read_yaml_file(file_path):
    """Read the YAML file and return its contents as a string."""
    with open(file_path, 'r') as file:
        return file.read()

def extract_yaml_content_with_includes(main_file, base_path=None, seen_files=None):
    """Handle '!include' directives in YAML files by replacing them with the file contents,
       allowing for recursive includes and detecting circular dependencies."""
    if base_path is None:
        base_path = main_file.parent
    
    if seen_files is None:
        seen_files = set()

    # Check for circular dependency
    if main_file in seen_files:
        raise Exception(f"Circular dependency detected! File {main_file} is already included.")
    
    seen_files.add(main_file)

    expanded_content = []
    with open(main_file, 'r') as file:
        content = file.readlines()

    for line in content:
        if line.strip().startswith('!include'):
            # Extract the filename from the include directive
            include_file = line.strip().split()[1]
            full_include_path = base_path / include_file

            # Recursively process the included file
            if full_include_path.exists():
                included_content = extract_yaml_content_with_includes(full_include_path, base_path, seen_files)
                expanded_content.append(included_content)
            else:
                raise FileNotFoundError(f"Included file not found: {full_include_path}")
        else:
            expanded_content.append(line)

    seen_files.remove(main_file)  # Remove the file from the set after processing
    return ''.join(expanded_content)

def parse_and_load_yaml(content):
    """Load YAML content from a string."""
    return yaml.safe_load(content)
