#!/usr/bin/env bash

# The Flow makefiles need to be linked to force that everyone uses the same one
echo 'Executing Flow link creation:'

# Set the variables
GIT_TOPLEVEL=$(git rev-parse --show-toplevel)
# Destination folders
ATPG_DIR=$PWD
# Source folders
PROJECT_DFT_DIR=$GIT_TOPLEVEL/hw/impl/{{ cookiecutter.project }}/dft

ln -srv $PROJECT_DFT_DIR/scripts/run_atpg.sh $ATPG_DIR/run.sh
