# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Samsung SF5A 5nm RTL-Architect flat setup script
# Owner: {{ cookiecutter.author_full_name }} <{{ cookiecutter.author_email }}>

# /// TODO:__one_line_summary_of_{{ cookiecutter.design_name }}__

set DESIGN     {{ cookiecutter.design_name }}
set IP_DIR     $env(MAKEFILE_DIR)/../
set GIT_REPO   [exec git -C $IP_DIR rev-parse --show-toplevel]

set BENDER_TARGETS { rtl asic sf5a } 
set BBOX_MODULES   { }

source ${GIT_REPO}/hw/scripts/rtla/rtla_setup.tcl
