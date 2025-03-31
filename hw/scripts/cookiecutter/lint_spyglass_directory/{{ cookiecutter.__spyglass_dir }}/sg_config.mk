# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Spyglass run config setup
# Owner: {{ cookiecutter.author_full_name }} <{{ cookiecutter.author_email }}>

# Configuration
IP_NAME            ?= {{ cookiecutter.top_level_name }}
BENDER_MANI_LOC_RTL?= $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS 	   += -t rtl -t asic -t sf5a
