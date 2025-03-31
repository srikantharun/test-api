# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: Luyi <yi.lu@axelera.ai>

set DESIGN          europa
set IP_DIR          $env(MAKEFILE_DIR)/../
set GIT_REPO        [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a synthesis }
set BBOX_MODULES   { ai_core_p apu_p dcd_p l2_p lpddr_p noc_top pcie_p pve_p soc_mgmt_p soc_periph_p sys_spm_p ddr_west_clock_gen_p }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
