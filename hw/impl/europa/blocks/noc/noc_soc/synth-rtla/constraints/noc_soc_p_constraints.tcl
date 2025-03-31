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
set_input_delay -clock "sys_spm_aon_clk" [expr ${sys_spm_aon_clk_P}*0.7] [get_ports "i_sys_spm_aon_rst_n"]
set_input_delay -clock "sys_spm_clk" [expr ${sys_spm_clk_P}*0.7] [get_ports "i_sys_spm_rst_n"]
set_input_delay -clock "soc_mgmt_aon_clk" [expr ${soc_mgmt_aon_clk_P}*0.7] [get_ports "i_soc_mgmt_aon_rst_n"]
set_input_delay -clock "soc_mgmt_clk" [expr ${soc_mgmt_clk_P}*0.7] [get_ports "i_soc_mgmt_rst_n"]
set_input_delay -clock "pve_1_aon_clk" [expr ${pve_1_aon_clk_P}*0.7] [get_ports "i_pve_1_aon_rst_n"]
set_input_delay -clock "pve_1_clk" [expr ${pve_1_clk_P}*0.7] [get_ports "i_pve_1_rst_n"]
set_input_delay -clock "pve_0_aon_clk" [expr ${pve_0_aon_clk_P}*0.7] [get_ports "i_pve_0_aon_rst_n"]
set_input_delay -clock "pve_0_clk" [expr ${pve_0_clk_P}*0.7] [get_ports "i_pve_0_rst_n"]
set_input_delay -clock "pcie_aon_clk" [expr ${pcie_aon_clk_P}*0.7] [get_ports "i_pcie_aon_rst_n"]
set_input_delay -clock "pcie_init_mt_clk" [expr ${pcie_init_mt_clk_P}*0.7] [get_ports "i_pcie_init_mt_rst_n"]
set_input_delay -clock "pcie_targ_mt_clk" [expr ${pcie_targ_mt_clk_P}*0.7] [get_ports "i_pcie_targ_mt_rst_n"]
set_input_delay -clock "pcie_targ_cfg_clk" [expr ${pcie_targ_cfg_clk_P}*0.7] [get_ports "i_pcie_targ_cfg_rst_n"]
set_input_delay -clock "pcie_targ_cfg_dbi_clk" [expr ${pcie_targ_cfg_dbi_clk_P}*0.7] [get_ports "i_pcie_targ_cfg_dbi_rst_n"]
set_input_delay -clock "dcd_aon_clk" [expr ${dcd_aon_clk_P}*0.7] [get_ports "i_dcd_aon_rst_n"]
set_input_delay -clock "dcd_codec_clk" [expr ${dcd_codec_clk_P}*0.7] [get_ports "i_dcd_codec_rst_n"]
set_input_delay -clock "dcd_mcu_clk" [expr ${dcd_mcu_clk_P}*0.7] [get_ports "i_dcd_mcu_rst_n"]
set_input_delay -clock "apu_aon_clk" [expr ${apu_aon_clk_P}*0.7] [get_ports "i_apu_aon_rst_n"]
set_input_delay -clock "apu_x_clk" [expr ${apu_x_clk_P}*0.7] [get_ports "i_apu_x_rst_n"]
set_input_delay -clock "noc_clk" [expr ${noc_clk_P}*0.7] [get_ports "i_noc_rst_n"]
