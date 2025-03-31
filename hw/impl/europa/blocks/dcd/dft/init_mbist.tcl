# Initial mbist sequence. Trigger resets and enable pctl reset and clock bypass
iProcsForModule ${DESIGN}

iTopProc pulse_resets { } {
    global DESIGN
    iWrite ${DESIGN}_rtl1_tessent_tdr_sri_ctrl_inst.all_test 1
    iApply
    iForcePort i_global_rst_n 0
    iForcePort i_ao_rst_n 0;
    iRunLoop 10
    iForcePort i_global_rst_n 1
    iForcePort i_ao_rst_n 1;
    iRunLoop 10
}
