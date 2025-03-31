#!/bin/env bash

# Function to display help menu
function display_help() {
    echo "Usage: $0 [options] <source> <destination>"
    echo
    echo "Options:"
    echo "-f    Force copy, ignore differences"
    echo "-h    Display this help menu"
    echo
    echo "This script copies the source file to the destination only if the destination file does not exist or differs from the source."
}

# Parse options
while getopts "fh" opt; do
    case ${opt} in
        f)
            FORCE_COPY=true
            ;;
        h)
            display_help
            exit 0
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done
shift $((OPTIND -1))

# Check if source and destination are provided
if [ $# -ne 2 ]; then
    echo "Error: Source and destination files must be provided."
    exit 1
fi

SOURCE=$1
DESTINATION=$2

# Check if source file exists
if [ ! -f "$SOURCE" ]; then
    echo "Error: Source file does not exist."
    exit 1
fi

# If force copy is enabled or destination file does not exist or files are different, then copy
if [ "$FORCE_COPY" = true ] || [ ! -f "$DESTINATION" ] || ! cmp -s -- "$SOURCE" "$DESTINATION"; then
    cp -- "$SOURCE" "$DESTINATION"
fi
