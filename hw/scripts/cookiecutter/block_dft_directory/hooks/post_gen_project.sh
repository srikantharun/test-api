#!/usr/bin/env bash

# The Flow makefiles need to be linked to force that everyone uses the same one
echo 'Executing Flow link creation:'

# Set the variables
GIT_TOPLEVEL=$(git rev-parse --show-toplevel)
# Destination folders
DFT_DIR=$PWD
INSERTION_DIR=$DFT_DIR/insertion
# Source folders
FLOW_MAKEFILES_DIR=$GIT_TOPLEVEL/hw/scripts/flow_makefiles
PROJECT_DFT_DIR=$GIT_TOPLEVEL/hw/impl/{{ cookiecutter.project }}/dft

# DFT makefile
ln -srv $FLOW_MAKEFILES_DIR/dft.mk $DFT_DIR/Makefile
# Release script
ln -srv $PROJECT_DFT_DIR/scripts/release.sh $DFT_DIR
# Tessent common dofiles
ln -srv $PROJECT_DFT_DIR/dofiles/tessent_setup.tcl $DFT_DIR
# Tessent run script
for dir in $(find $INSERTION_DIR/* -maxdepth 0 -type d); do
    ln -srv $PROJECT_DFT_DIR/scripts/run.sh $dir
done
