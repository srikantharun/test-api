#!/usr/bin/env bash
# install python virtual env in a thread safe way

set -e

VENV="$1"
REQUIREMENTS="$2"

mkdir -p $VENV

# Use python3.10 (the Python version provided from module) explicitly, as the
# Silverlight machines may not have python3 point to python3.10.
(
flock ${file_descriptor}
echo "$VENV: Updating virtual environment based on '$REQUIREMENTS'."
python3.10 -m venv $VENV
$VENV/bin/pip install -r $REQUIREMENTS
) {file_descriptor}>$VENV.lock
