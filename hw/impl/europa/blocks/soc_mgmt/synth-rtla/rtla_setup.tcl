# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Matt Morris <matt.morris@axelera.ai>

# // SOC_MGMT RTL-A elaboration check

set DESIGN     soc_mgmt_p
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a synthesis }
set BBOX_MODULES   { }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
