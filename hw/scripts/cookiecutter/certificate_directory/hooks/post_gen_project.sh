#!/usr/bin/env bash

# The Flow makefiles need to be linked to force that everyone uses the same one
echo 'Executing Certificate Flow link creation:'

# Set the variables
GIT_TOPLEVEL=$(git rev-parse --show-toplevel)
DIR=$PWD
FLOW_MAKEFILES_DIR=$GIT_TOPLEVEL/hw/scripts/flow_makefiles

# VCF flow
ln -srv $FLOW_MAKEFILES_DIR/certificate.mk $DIR/Makefile
