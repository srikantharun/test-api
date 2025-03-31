# Initial mbist sequence. Trigger resets and enable pctl reset and clock bypass
iProcsForModule ${DESIGN}

iTopProc pulse_resets { } {
    global DESIGN
    iWrite ${DESIGN}_rtl1_tessent_tdr_sri_ctrl_inst.all_test 1
    iApply
    iForcePort i_global_rst_n 0;
    iForcePort i_ao_rst_n 0;
    iRunLoop 10
    iForcePort i_global_rst_n 1;
    iForcePort i_ao_rst_n 1;
    iRunLoop 10
}

iTopProc pulse_resets_noc_soc { } {
    iForcePort i_apu_aon_rst_n 0;
    iForcePort i_apu_x_rst_n 0;
    iForcePort i_dcd_aon_rst_n 0;
    iForcePort i_dcd_codec_rst_n 0;
    iForcePort i_dcd_mcu_rst_n 0;
    iForcePort i_noc_rst_n 0;
    iForcePort i_pcie_aon_rst_n 0;
    iForcePort i_pcie_init_mt_rst_n 0;
    iForcePort i_pcie_targ_cfg_dbi_rst_n 0;
    iForcePort i_pcie_targ_cfg_rst_n 0;
    iForcePort i_pcie_targ_mt_rst_n 0;
    iForcePort i_pve_0_aon_rst_n 0;
    iForcePort i_pve_0_rst_n 0;
    iForcePort i_pve_1_aon_rst_n 0;
    iForcePort i_pve_1_rst_n 0;
    iForcePort i_soc_mgmt_aon_rst_n 0;
    iForcePort i_soc_mgmt_rst_n 0;
    iForcePort i_sys_spm_aon_rst_n 0;
    iForcePort i_sys_spm_rst_n 0;
    iRunLoop 10
    iForcePort i_apu_aon_rst_n 1;
    iForcePort i_apu_x_rst_n 1;
    iForcePort i_dcd_aon_rst_n 1;
    iForcePort i_dcd_codec_rst_n 1;
    iForcePort i_dcd_mcu_rst_n 1;
    iForcePort i_noc_rst_n 1;
    iForcePort i_pcie_aon_rst_n 1;
    iForcePort i_pcie_init_mt_rst_n 1;
    iForcePort i_pcie_targ_cfg_dbi_rst_n 1;
    iForcePort i_pcie_targ_cfg_rst_n 1;
    iForcePort i_pcie_targ_mt_rst_n 1;
    iForcePort i_pve_0_aon_rst_n 1;
    iForcePort i_pve_0_rst_n 1;
    iForcePort i_pve_1_aon_rst_n 1;
    iForcePort i_pve_1_rst_n 1;
    iForcePort i_soc_mgmt_aon_rst_n 1;
    iForcePort i_soc_mgmt_rst_n 1;
    iForcePort i_sys_spm_aon_rst_n 1;
    iForcePort i_sys_spm_rst_n 1;
    iRunLoop 10
}

iTopProc pulse_resets_noc_h_west { } {
    iForcePort i_noc_rst_n 0;
    iRunLoop 10
    iForcePort i_noc_rst_n 1;
    iRunLoop 10
}
