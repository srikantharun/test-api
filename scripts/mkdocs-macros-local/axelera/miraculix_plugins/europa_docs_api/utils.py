import pathlib
import typing

import axelera.miraculix as miraculix
import mkdocs_macros_helper

import package_lib.utils as _pkg_utils


# --------------------------------------------------------------------------------------------------
# Globals
# --------------------------------------------------------------------------------------------------

ROOT_PATH = pathlib.Path(__file__).parents[5]

# --------------------------------------------------------------------------------------------------
# Macros
# --------------------------------------------------------------------------------------------------

@miraculix.function(
    pass_environment=True,
)
def link_repo_file(
    path: pathlib.Path,
    *,
    environment: mkdocs_macros_helper.MacrosPlugin,
) -> str:
    """
    Handles links to files located in the repo. Relative links to repository files are not linked correctly on the
    MkDocs page. Use this function to handle correct linking for you.

    Examples:
        The following example creates a link to the bender file located at `src/Bender.yml` relative to the repository
        root:
        >>> [Bender File]({{ link_repo_file('src/Bender.yml') }})

    Args:
        env: The macros environment, which is automatically inserted by the API.
        path: The path to the file. Has to be stated relative to the repository root.

    Returns:
        The URL pointing to the file in the repository.
    """
    path = pathlib.Path(path)

    file_path = ROOT_PATH / path
    assert not path.is_absolute(), f"Repo file path '{path}' cannot be an absolute path!"
    assert file_path.exists(), f"Repo file '{path}' doesn't exist!"

    return f"{environment.conf.repo_url}/-/blob/main/{path}"



@miraculix.function()
def load_data(
    path: str,
) -> dict[str, typing.Any] | list[typing.Any] | typing.Any:
    """
    Load data from a file. The function automatically detects the file type based on the file extension.

    Supported file types:
    - TOML
    - YAML
    - JSON

    Args:
    ----
    path: The path to the file.

    Returns:
    -------
    The loaded data from the file.

    """
    return _pkg_utils.load_data(path)
