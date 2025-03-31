# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Early setup specialisation for AI Core
# Owner: Matt Morris <sander.geursen@axelera.ai>


set_app_options -name hdlin.sverilog.interface_only_modules -value {aic_did_p aic_infra_p aic_ls_p aic_mid_p}
set_attribute -objects [get_mismatch_types empty_logic_module] -name action(default) -value repair
