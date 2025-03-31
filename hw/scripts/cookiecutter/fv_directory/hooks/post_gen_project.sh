#!/usr/bin/env bash

# The Flow makefiles need to be linked to force that everyone uses the same one
echo 'Executing Formal Verification Flow link creation:'

# Set the variables
GIT_TOPLEVEL=$(git rev-parse --show-toplevel)
DIR=$PWD
FLOW_MAKEFILES_DIR=$GIT_TOPLEVEL/hw/scripts/flow_makefiles
VCF_TCL_DIR=$GIT_TOPLEVEL/hw/scripts/fv

# VCF flow
ln -srv $FLOW_MAKEFILES_DIR/vcf.mk $DIR/Makefile

# FPV tcl file
ln -srv $VCF_TCL_DIR/fpv/run.tcl $DIR/fpv

# FPV tcl file
ln -srv $VCF_TCL_DIR/cc/run.tcl $DIR/cc

# DPV tcl file
ln -srv $VCF_TCL_DIR/dpv/run.tcl $DIR/dpv

# FRV tcl file
ln -srv $VCF_TCL_DIR/frv/run.tcl $DIR/frv

# SEQ tcl file
ln -srv $VCF_TCL_DIR/seq/run.tcl $DIR/seq
