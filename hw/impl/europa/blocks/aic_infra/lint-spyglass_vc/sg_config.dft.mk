# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Spyglass run config setup
# Owner: Luyi <yi.lu@axelera.ai>

# Configuration
IP_NAME            ?= aic_infra_p
BENDER_MANI_LOC_RTL?= $(MAKEFILE_DIR)/../rtl/dft
BENDER_TARGETS  += -t rtl -t asic -t sf5a -t dft
