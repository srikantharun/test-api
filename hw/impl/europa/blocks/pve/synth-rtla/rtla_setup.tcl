# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

set DESIGN     pve_p
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a } 
set BBOX_MODULES   { pve_l1_p pve_cva6v_p } 

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
