# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

# /// TODO:__one_line_summary_of_lpddr__

set DESIGN     lpddr_p
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a } 
set BBOX_MODULES   { dwc_lpddr5xphyzcal_top dwc_lpddr5xphycmosx2_top dwc_lpddr5xphymaster_top dwc_lpddr5xphyacx2_top dwc_lpddr5xphycsx2_top dwc_lpddr5xphyckx2_top dwc_lpddr5xphydx4_top dwc_lpddr5xphydx5_top }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl


