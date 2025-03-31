# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Tiago Campos <tiago.campos@axelera.ai>

# /// TODO:__one_line_summary_of_dpu__

set DESIGN     dpu
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a } 
set BBOX_MODULES   { }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
