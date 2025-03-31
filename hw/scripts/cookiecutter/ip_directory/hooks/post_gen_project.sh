#!/usr/bin/env bash

# The Flow makefiles need to be linked to force that everyone uses the same one
echo 'Executing Flow link creation:'

# Set the variables
GIT_TOPLEVEL=$(git rev-parse --show-toplevel)
IP_DIR=$PWD/default
FLOW_MAKEFILES_DIR=$GIT_TOPLEVEL/hw/scripts/flow_makefiles

# Sanity Lint
ln -srv $FLOW_MAKEFILES_DIR/lint_sanity.mk $IP_DIR/lint-sanity/Makefile

# Questasim Basic setup
ln -srv $FLOW_MAKEFILES_DIR/simulation.mk $IP_DIR/sim-questa/Makefile
