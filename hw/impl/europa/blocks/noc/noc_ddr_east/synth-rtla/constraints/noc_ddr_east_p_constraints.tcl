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
set_input_delay -clock "lpddr_ppp_0_aon_clk" [expr ${lpddr_ppp_0_aon_clk_P}*0.7] [get_ports "i_lpddr_ppp_0_aon_rst_n"]
set_input_delay -clock "lpddr_ppp_0_clk" [expr ${lpddr_ppp_0_clk_P}*0.7] [get_ports "i_lpddr_ppp_0_rst_n"]
set_input_delay -clock "lpddr_ppp_1_aon_clk" [expr ${lpddr_ppp_1_aon_clk_P}*0.7] [get_ports "i_lpddr_ppp_1_aon_rst_n"]
set_input_delay -clock "lpddr_ppp_1_clk" [expr ${lpddr_ppp_1_clk_P}*0.7] [get_ports "i_lpddr_ppp_1_rst_n"]
set_input_delay -clock "lpddr_ppp_2_aon_clk" [expr ${lpddr_ppp_2_aon_clk_P}*0.7] [get_ports "i_lpddr_ppp_2_aon_rst_n"]
set_input_delay -clock "lpddr_ppp_2_clk" [expr ${lpddr_ppp_2_clk_P}*0.7] [get_ports "i_lpddr_ppp_2_rst_n"]
set_input_delay -clock "lpddr_ppp_3_aon_clk" [expr ${lpddr_ppp_3_aon_clk_P}*0.7] [get_ports "i_lpddr_ppp_3_aon_rst_n"]
set_input_delay -clock "lpddr_ppp_3_clk" [expr ${lpddr_ppp_3_clk_P}*0.7] [get_ports "i_lpddr_ppp_3_rst_n"]
set_input_delay -clock "soc_periph_aon_clk" [expr ${soc_periph_aon_clk_P}*0.7] [get_ports "i_soc_periph_aon_rst_n"]
set_input_delay -clock "soc_periph_clk" [expr ${soc_periph_clk_P}*0.7] [get_ports "i_soc_periph_rst_n"]
set_input_delay -clock "noc_clk" [expr ${noc_clk_P}*0.7] [get_ports "i_noc_rst_n"]
