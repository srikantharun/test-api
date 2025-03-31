
# --------------------------------------------------------------------------------------------------
# Imports
# --------------------------------------------------------------------------------------------------
import logging


# --------------------------------------------------------------------------------------------------
# Module Variables
# --------------------------------------------------------------------------------------------------

_logger = logging.getLogger(__name__)



# --------------------------------------------------------------------------------------------------
# Functions
# --------------------------------------------------------------------------------------------------

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
