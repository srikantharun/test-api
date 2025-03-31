#!/user/bin/python3
# (C) Copyright 2024 Axelera AI B.V.
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: PD release Cleanup script

import os
import re
import shutil
import argparse
from datetime import datetime, timedelta
from pathlib import Path
from typing import List, NoReturn
import logging
import stat
import getpass

# NOTE: The directory deletion approach implemented in this script is quite aggressive. 
# It modifies permissions to make all directories writable before proceeding to delete them. 

def setup_logging(log_dir: Path = None) -> NoReturn:
    """
    Set up logging configuration to save logs to a timestamped file in the specified directory.
    If no directory is provided, logs will be saved in the current directory.
    """
    if log_dir is None:
        log_dir = Path.cwd()
    else:
        log_dir.mkdir(parents=True, exist_ok=True)  # Ensure the directory exists

    timestamp    = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    log_filename = log_dir / f"pd_cleanup_{timestamp}.log"
    
    logging.basicConfig(
        level    = logging.INFO,
        format   = '%(asctime)s - %(levelname)s - %(message)s',
        filename = log_filename,
        filemode = 'w'
    )
    
    formatter       = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    console_handler = logging.StreamHandler()  # Also output to standard console
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)
    
    logging.getLogger().addHandler(console_handler)
    
    # Write log header
    username = getpass.getuser()
    hostname = os.uname()[1]
    header_border = "$" * 70
    log_header = (
        f"\n{header_border}\n"
        f"{header_border}\n"
        f"Executing PD Cleanup script\n"
        f"{header_border}\n"
        f"User: {username}\n"
        f"Host: {hostname}\n"
        f"Execution Time: {timestamp}\n"
        f"{header_border}\n"
        f"{header_border}\n\n"
   )
    
    logger = logging.getLogger()
    logger.handlers[0].setFormatter(logging.Formatter('%(message)s'))  # Change the formatter for the first log entry
    logging.info(log_header)
    logger.handlers[0].setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))  # Revert to the default formatter

    
def read_keep_file(filepath: Path) -> List[re.Pattern]:
    """
    Reads the specified keep file to get a list of directory paths that should not be deleted.
    Args:
        filepath (Path): The full path to the keep file.
    Returns:
        List[re.Pattern]: A list of compiled regex patterns from the keep file.
    """
    # IMP: Halt execution if there are regex parsing errors to prevent unintended deletions 
    # caused by a missing or incorrectly formatted keep file.
    try:
        with filepath.open('r') as file:
            keep_patterns = [re.compile(line.strip()) for line in file if line.strip()]
        logging.info(f"Keep file read successfully from {filepath}")
        return keep_patterns
    except FileNotFoundError:
        logging.warning(f"Keep file not found at {filepath}")
        raise
    except re.error as e:
        logging.error(f"Invalid regex in keep file: {e}")
        raise
    except Exception as e:
        logging.error(f"Failed to read keep file: {e}")
        raise


def make_writeable(dir: Path) -> NoReturn:
    # Add write permissions for owner
    # function might except as we dont want to proceed if user permissions are not adequate
    os.chmod(dir, dir.stat().st_mode | stat.S_IWUSR)


def make_read_only(dir: Path) -> NoReturn:
    # Remove write permissions for owner, group, and others
    # function might except as we dont want to proceed if user permissions are not adequate
    os.chmod(dir, dir.stat().st_mode & ~stat.S_IWUSR & ~stat.S_IWGRP & ~stat.S_IWOTH)


def should_keep(path            : Path, 
                keep_patterns   : List[re.Pattern]) -> bool:
    """
    Determines if the given directory path matches any of the entries in the keep file.
    Args:
        path (Path): The path of the directory to check.
        keep_patterns (List[re.Pattern]): A list of compiled regex patterns to check against.
    Returns:
        bool: True if the path should be kept, False otherwise.
    """
    path_str = str(path)
    return any(pattern.match(path_str) for pattern in keep_patterns)


def make_writeable_and_remove(path: Path) -> NoReturn:
    """
    Recursively changes the permissions of all subdirectories and files to be writable,
    then removes the directory and its contents.
    Args:
        path (Path): The path of the directory to modify and remove.
    """
    if not path.is_dir():
        return

    # Iterate over all directories and files within the path and update permissions
    make_writeable(path)
    for sub_path in path.rglob('*'):
        perms = sub_path.stat().st_mode
        if not perms & stat.S_IWRITE:
            make_writeable(sub_path)

    # Now try to remove the directory tree
    try:
        perms = path.stat().st_mode
        if not perms & stat.S_IWRITE:
            os.chmod(path, perms | stat.S_IWRITE)
        
        shutil.rmtree(path)
        logging.info(f"Successfully deleted: {path}")
    except Exception as e:
        logging.error(f"Failed to delete: {path}, Error: {e}")


def attempt_to_delete_directory(release_subdir  : Path,
                                confirm_deletion: bool) -> bool:
    """
    Attempts to delete a directory after making it writable. Logs the outcome.
    Returns True if deletion is successful, False otherwise.
    Args:
        release_subdir (Path): The directory to delete.
    """
    if confirm_deletion:
        confirm = input(f"Confirm deletion of {release_subdir} (y/n): ")
        if confirm.lower() != 'y':
            logging.info(f"Deletion cancelled by user for: {release_subdir}")
            return False

    logging.info(f"Deleting directory: {release_subdir}")
    try:
        make_writeable_and_remove(release_subdir)
        return True
    except Exception as e:
        logging.error(f"Failed to delete {release_subdir}: {e}")
        return False


def finalize_directory_status(ip_dir: Path) -> NoReturn:
    """
    Finalizes the status of an IP directory, make it read-only after deletion
    Removes the directory if it is empty.
    Args:
        ip_dir (Path): The IP directory to finalize.
    """
    if not any(ip_dir.iterdir()):  # Check if the directory is empty
        try:
            ip_dir.rmdir()  # Attempt to remove an empty directory
            logging.info(f"Removed empty IP directory: {ip_dir}")
        except OSError as e:
            logging.error(f"Failed to remove IP directory {ip_dir}: {e}")


def process_release_subdirectory(release_subdir     : Path, 
                                 keep_patterns      : List[re.Pattern], 
                                 cutoff_date        : datetime,
                                 confirm_deletion   : bool) -> bool:
    """
    Decides whether a subdirectory can be deleted based on its modification time and whether it matches any keep patterns.
    Returns True if the directory is kept, False if an attempt to delete it is made.
    Args:
        release_subdir (Path): Subdirectory of the IP directory to evaluate.
        keep_patterns (List[re.Pattern]): Patterns that signify directories to keep.
        cutoff_date (datetime): The date before which directories are considered for deletion if not protected.
    """
    mtime = datetime.fromtimestamp(release_subdir.stat().st_mtime)
    if mtime < cutoff_date:
        if should_keep(release_subdir, keep_patterns):
            logging.info(f"Directory kept (matches keep entry): {release_subdir}")
            return True
        else:
            return attempt_to_delete_directory(release_subdir, confirm_deletion)
    else:
        logging.info(f"Directory kept (newer than {cutoff_date}): {release_subdir}")
        return True


def process_ip_directory(ip_dir             : Path, 
                         keep_patterns      : List[re.Pattern], 
                         cutoff_date        : datetime,
                         confirm_deletion   : bool) -> NoReturn:
    """
    Processes each IP directory: makes the directory writable, checks each subdirectory against deletion criteria,
    and then finalizes the status of the directory based on whether all deletions were successful.
    Skips directories with matching expression in keep file.
    Args:
        ip_dir (Path): The individual IP directory to process.
        keep_patterns (List[re.Pattern]): Patterns that signify directories to keep.
        cutoff_date (datetime): The date before which directories are considered for deletion if not protected.
    """
    #Check if we need to keep all the releases for an IP 
    if should_keep(ip_dir, keep_patterns):
        logging.info(f"Directory kept (matches keep entry): {ip_dir}")
        return
    
    for release_subdir in ip_dir.iterdir():
        if release_subdir.is_dir():  # Continue processing directories
            process_release_subdirectory(release_subdir, keep_patterns, cutoff_date, confirm_deletion)

    finalize_directory_status(ip_dir)
  
  
def clean_releases(release_dir  : Path, 
                   keep_patterns: List[re.Pattern], 
                   weeks_old    : int,
                   force        : bool) -> NoReturn:
    """
    Top level function that orchestrates the deletion of directories in the specified release directory 
    that are older than the specified number of weeks, unless they match an entry in the keep file. 
    It skips the top-level IP directories and checks only the directories inside them.
    Args:
        release_dir (Path): The root directory where IP releases are stored.
        keep_patterns (List[re.Pattern]): A list of compiled regex patterns that should not be deleted.
        weeks_old (int): The age threshold in weeks; directories older than this and not protected are deleted.
    """
    cutoff_date = datetime.now() - timedelta(weeks=weeks_old)
    # Iterate over each IP directory
    for ip_dir in release_dir.iterdir():
        if ip_dir.is_dir():  # Skip files
            process_ip_directory(ip_dir, keep_patterns, cutoff_date, not force)


def parse_arguments() -> argparse.Namespace:
    """
    Parses command line arguments to configure the cleanup operation.
    Returns:
        argparse.Namespace: An object containing the parsed command line arguments.
    """
    parser = argparse.ArgumentParser(description="Clean up old releases based on specified criteria.")
    parser.add_argument("-d",
                        "--dir",
                        type=Path,
                        default=".",
                        help="The root directory where releases are stored (default: current working directory)")
    
    parser.add_argument("-k", 
                        "--keep-file", 
                        type=Path,
                        default="hw/scripts/pd_release/pd_release.keep", 
                        help="Path to the keep file that lists directories not to delete (default: hw/scripts/pd_release/pd_release.keep)")
    
    parser.add_argument("-w", 
                        "--weeks-old", 
                        type=int, 
                        default=52, 
                        help="Age in weeks beyond which releases should be deleted if not protected by the keep file (default: 52 weeks)")
    
    parser.add_argument("-l", 
                        "--log-dir", 
                        type=Path,
                        help="Directory to save log files. If not specified, logs are saved in the current directory.")
    
    parser.add_argument("-f", 
                        "--force", 
                        action="store_true", 
                        help="Skip confirmation before deleting each directory.")

    return parser.parse_args()


def main() -> NoReturn:
    """
    Main function to execute the cleanup process.
    """
    args = parse_arguments()
    setup_logging(args.log_dir)
    keep_patterns = read_keep_file(args.keep_file)
    clean_releases(args.dir, keep_patterns, args.weeks_old, args.force)


if __name__ == "__main__":
    main()
