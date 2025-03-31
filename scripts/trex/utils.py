
# --------------------------------------------------------------------------------------------------
# (C) Copyright 2024 Axelera AI B.V.
# All rights reserved.
# *** Axelera AI Confidential ***
# --------------------------------------------------------------------------------------------------

"""TREX utilities file.
"""

# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------
import os
import logging
from typing import Dict, List, Set
import random
import hashlib
import re
# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)


# --------------------------------------------------------------------------------------------------
# Functions
# --------------------------------------------------------------------------------------------------
def ensure_directory_exists(directory: str) -> None:
    """
    Ensure that the given directory exists. If not, create it.

    Args:
        directory (str): Path to the directory.
    """
    if not os.path.exists(directory):
        os.makedirs(directory)

def write_rendered_content(test_path: str, rendered_content: str) -> None:
    """
    Write the rendered content to the specified file path.

    Args:
        test_path (str): Path to the output file where the content will be written.
        rendered_content (str): The content to be written to the file.
    """
    with open(test_path, 'w') as file:
        file.write(rendered_content)


def append_generated_data_header(hfile_path: str,  size_list: List[int]) -> None:
    """
    Write a header file that contains C defines for the data sizes.

    Args:
        hfile_path (str): Path to the header file to be written.
        size_list (Set[int]): Set of transfer sizes for which to generate data defines.
    """
    with open(hfile_path, 'a') as file:
        for size in size_list:
            size=int(size.split('_')[2].replace('B', ''))
            random_data = gen_random_data('trex', size)
            init_data = gen_init_data(size)
            file.write(f'#define DATA_SIZE_{size}B {size}\n')
            file.write(f'char __attribute__((aligned(4096), section(".sys_spm"))) INIT_DATA_{size}B [DATA_SIZE_{size}B]= {init_data}\n\n')
            file.write(f'char __attribute__((aligned(4096), section(".sys_spm"))) RANDOM_DATA_{size}B [DATA_SIZE_{size}B]= {random_data}\n\n')


def extract_unit_union(arch: Dict[str, str]
                       ) -> tuple:
    """
    Extract all allowed values for the field Task.instance of the Trex Scenario Model

    Args:
    ----
        arch: The Dict indicating the CPUs and DMAs in their control in the system

    Returns:
    -------
        A tuple of the superset of DMA units in the system.

    """
    # Create a superset (union) of all values
    superset = set()

    # Iterate over each list of values and add them to the superset
    for values in arch.values():
        superset.update(values)
    return tuple(superset)


# Generate random data, convert to hex and remove trailing commas
def gen_random_data(seed_name: str, n_bytes: int) -> str:
    """
    Generate pseudo-random data for the tests, based on the test name.
    - Hashes the test name to create a seed.
    - Uses the seed to generate pseudo-random bytes.
    - Converts them to hex and joins as a comma-separated string.

    Args:
    ----
        seed_name: The name of the test, which is used to seed the random generator.
        n_bytes: Number of bytes that need to be generated. Each byte
                 gets a pseudo-random value.

    Returns:
    -------
        A comma-separated string with each of the random n_bytes in hex format.

    """
    # Create a seed based on the seed_name  hash
    seed = int(hashlib.sha256(seed_name.encode()).hexdigest(), 16)

    # Seed the random generator
    random.seed(seed)

    # Generate pseudo-random bytes
    random_data = [random.randint(0, 255) for _ in range(n_bytes)]

    # Convert to hex and return as a comma-separated string
    return '{'+', '.join(f"0x{byte:02X}" for byte in random_data)+'};'


# Generate zero-initialized data and replace 0x00 with 0x55
def gen_init_data(n_bytes
                  )-> str:
    """
    Generate initialization data for the tests.
    - generates fixed value data
    - converts them to hex
    - removes the trailing commas

    Args:
    ----
        n_bytes: Number of bytes that need to be generated. Each byte
                 gets a fixed value.

    Returns:
    -------
        A comma separated string with each of the init n_bytes

    """
    zero_data = bytes(n_bytes)  # Equivalent to /dev/zero
    init_data = zero_data.replace(b'\x00', b'\x55')
    return '{'+', '.join(f"0x{byte:02X}" for byte in init_data) +'};'


# Function to grep through the file
def grep_data_sizes(file_path: str):
    """
    Search for the data sizes already defined in the file in file path.

    Args:
    ----
        file_path: Path to the file that needs to be searched

    Returns:
    -------
        A list of data sizes that were found in the
    """


    define_pattern = r"#define\s+(\w+)"
    data_size_pattern = r"DATA_SIZE_\d+[A-Z]+"

    data_sizes = set()

    with open(file_path, 'r') as file:
        for line in file:
            match = re.search(define_pattern, line)
            if match:
                define_value = match.group(1)
                if re.match(data_size_pattern, define_value):
                    data_sizes.add(define_value)

    return list(data_sizes)

def hex(
    integer: int | str,
    length: int = 12,
    prefix: str = None,
) -> str:
    """
    Converts an integer to a hexadecimal string.

    Args:
    ----
        integer: An integer to convert to hexadecimal.
        length: The length of the resulting string (default 8).

    Returns:
    -------
        A hexadecimal string.

    Raises:
    ------
        ValueError: If the integer is negative or too wide to be displayed in the specified number of hex characters.

    Examples:
    --------
        >>> hex(255)
        '000000FF'
        >>> hex(255, 2)
        'FF'

    """
    integer = int(integer)

    if integer < 0:
        message = "Negative integer cannot be displayed in hex!"
        _logger.error(message)
        raise ValueError(message)

    if integer > 2 ** 64:
        _logger.debug(f"Filtered integer '{integer}' suspiciously large!")

    hex_string = f'{{:0>{length}X}}'.format(int(integer))

    if len(hex_string) > length:
        message = f"Number '{integer}' is too wide to be displayed in '{length}' hex characters."
        _logger.error(message)
        raise ValueError(message)

    if prefix:
        hex_string=prefix+hex_string

    return hex_string


def indent(text, width=4, char=' '):
    """
    Indent for the jinja2 templates.

    Args:
    ----
        text: The text line that needs to be intended
        width: the number of indent characters
        char: The character with which to pad the intended lines

    Returns:
    -------
        A string.

    """

    padding = char * width
    return '\n'.join(padding + line for line in text.splitlines())

def contains_strings(item, *strings):
    """
    Checks if the input item contains any of the strings provided in the list of strings.

    Args:
    ----
        item: The string that needs to be checked.
        *strings: List of strings that we need to iterate over.

    Returns:
    -------
        Bool: True/False if the item contains any of the strings defined in the list of strings.

    """
    for s in strings:
        if s in item:
            return True
    return False
