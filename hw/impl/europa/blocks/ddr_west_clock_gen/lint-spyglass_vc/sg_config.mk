# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Spyglass run config setup
# Owner: Sander Geursen <sander.geursen@axelera.ai>

# Configuration
IP_NAME            ?= ddr_west_clock_gen_p
BENDER_MANI_LOC_RTL?= $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS 	   += -t rtl -t asic -t sf5a
