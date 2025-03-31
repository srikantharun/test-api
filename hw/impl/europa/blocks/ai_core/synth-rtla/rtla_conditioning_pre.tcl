# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Early conditioning specialisation for AI Core
# Owner: Matt Morris <sander.geursen@axelera.ai>

# Change the size of the ce1 cell (macro created for the empty_logic_module compute_engine) from
# the default (based on the average standard cell size and the module pin count).
echo "AI Core Specialization for Conditioning"
set_attribute -objects [get_cell -hier *aic_did_p]   -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
set_attribute -objects [get_cell -hier *aic_infra_p] -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
set_attribute -objects [get_cell -hier *aic_ls_p]    -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
set_attribute -objects [get_cell -hier *aic_mid_p]   -name boundary -value {{0 0} {0 500} {500 500} {500 0}}
