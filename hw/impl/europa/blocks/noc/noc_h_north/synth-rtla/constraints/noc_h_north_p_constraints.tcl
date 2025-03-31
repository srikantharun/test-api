# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owners: Joao Martins <joao.martins@axelera.ai>
#         Tasos Psarras <anastasios.psarras@axelera.ai>

# CDC skew budgets
set CDC_MAX_SKEW_GRAY 0.1
set CDC_EXTRA_SKEW_DATA 0.2
set CDC_EXTRA_SKEW_PWR 0.1
set CDC_MAX_SKEW_DATA [expr $CDC_MAX_SKEW_GRAY + $CDC_EXTRA_SKEW_DATA]
set CDC_MAX_SKEW_PWR [expr $CDC_MAX_SKEW_GRAY + $CDC_EXTRA_SKEW_PWR]

source -echo -verbose ${CONSTR_DIR}/sdcTop.sdc
source -echo -verbose ${CONSTR_DIR}/internalConstraints.sdc
# FIXME(psarras; https://git.axelera.ai/prod/europa/-/work_items/1743)
# source -echo -verbose ${CONSTR_DIR}/internalConstraints_token.sdc
source -echo -verbose ${CONSTR_DIR}/externalConstraints.sdc
# FIXME(psarras; https://git.axelera.ai/prod/europa/-/work_items/1743)
# source -echo -verbose ${CONSTR_DIR}/externalConstraints_token.sdc
source -echo -verbose ${CONSTR_DIR}/placement_guidance.tcl
# Reset constraints
set_input_delay -clock "aic_4_aon_clk" [expr ${aic_4_aon_clk_P}*0.7] [get_ports "i_aic_4_aon_rst_n"]
set_input_delay -clock "aic_4_clk" [expr ${aic_4_clk_P}*0.7] [get_ports "i_aic_4_rst_n"]
set_input_delay -clock "aic_5_aon_clk" [expr ${aic_5_aon_clk_P}*0.7] [get_ports "i_aic_5_aon_rst_n"]
set_input_delay -clock "aic_5_clk" [expr ${aic_5_clk_P}*0.7] [get_ports "i_aic_5_rst_n"]
set_input_delay -clock "aic_6_aon_clk" [expr ${aic_6_aon_clk_P}*0.7] [get_ports "i_aic_6_aon_rst_n"]
set_input_delay -clock "aic_6_clk" [expr ${aic_6_clk_P}*0.7] [get_ports "i_aic_6_rst_n"]
set_input_delay -clock "aic_7_aon_clk" [expr ${aic_7_aon_clk_P}*0.7] [get_ports "i_aic_7_aon_rst_n"]
set_input_delay -clock "aic_7_clk" [expr ${aic_7_clk_P}*0.7] [get_ports "i_aic_7_rst_n"]
set_input_delay -clock "l2_4_aon_clk" [expr ${l2_4_aon_clk_P}*0.7] [get_ports "i_l2_4_aon_rst_n"]
set_input_delay -clock "l2_4_clk" [expr ${l2_4_clk_P}*0.7] [get_ports "i_l2_4_rst_n"]
set_input_delay -clock "l2_5_aon_clk" [expr ${l2_5_aon_clk_P}*0.7] [get_ports "i_l2_5_aon_rst_n"]
set_input_delay -clock "l2_5_clk" [expr ${l2_5_clk_P}*0.7] [get_ports "i_l2_5_rst_n"]
set_input_delay -clock "l2_6_aon_clk" [expr ${l2_6_aon_clk_P}*0.7] [get_ports "i_l2_6_aon_rst_n"]
set_input_delay -clock "l2_6_clk" [expr ${l2_6_clk_P}*0.7] [get_ports "i_l2_6_rst_n"]
set_input_delay -clock "l2_7_aon_clk" [expr ${l2_7_aon_clk_P}*0.7] [get_ports "i_l2_7_aon_rst_n"]
set_input_delay -clock "l2_7_clk" [expr ${l2_7_clk_P}*0.7] [get_ports "i_l2_7_rst_n"]
set_input_delay -clock "noc_clk" [expr ${noc_clk_P}*0.7] [get_ports "i_noc_rst_n"]
