# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

set DESIGN     pcie_p
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { synthesis rtl asic sf5a }
set BBOX_MODULES   { dwc_c20pcie4_pma_x4_ns }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl


