onerror resume
wave tags F0 
wave update off
wave zoom range 0 523259375000
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_init_ddr_fsm.phy_dfi_init_complete} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_init_ddr_fsm.dh_gs_dfi_init_complete_en} -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_apb_slvtop.coreif.reg_ddrc_dfi_init_start -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.dfi_reset_n[0]} -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.u_CMOSX2_TOP.u_PWROK.PwrOkDly -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.ddrc_reg_operating_mode -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_phymstr.dh_gs_phymstr_en} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.rank_constraints[0].gs_rank_constraints0.auto_refresh_disable_pulse} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.end_init_ddr} -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.reg_arb_port_en_port0 -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_MEMRESET_L -tag F0 -radix hexadecimal -select
wave group MRR -backgroundcolor #004466 -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.dh_gs_zq_resistor_shared} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.zq_reset_detected} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.zq_calib_curr_state} -tag F0 -radix mnemonic
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.zq_detected} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.auto_zq_request} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.timer_pulse_x1024_dram} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.zqcs_timer_started} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_zq_calib.auto_zq_timer_x1024} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.sr_mrrw_en} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_bs_zq_calib_short_required} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.mr_wr_busy} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.mrrw_req_hold} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.clear_mrrw_req} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.hwffc_load_mr_req} -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.pub_top.tub.dfi_init_complete_ff -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.clear_mrrw_req} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.mr_wr_detect} -tag F0 -radix hexadecimal
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_load_mr.dh_gs_mr_wr} -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group APB0 -backgroundcolor #226600 -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_paddr -tag F0 -radix decimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_apb_decoder.ddrphy_paddr -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pwdata -tag F0 -radix decimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_pwrite -tag F0 -radix hexadecimal
wave add hdl_top.top_signals_intf.apb_master_0_prdata -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_apb_decoder.ddrctl0_addr_range_det -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_apb_decoder.ddrphy_addr_range_det -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_penable -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_cfg_apb4_s_psel -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_cfg_apb4_s_pready -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_cfg_apb4_s_pslverr -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group reset_apb -backgroundcolor #004466 -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_paddr -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pwdata -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pwrite -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_psel -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_penable -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pstrb -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.i_lpddr_syscfg_apb4_s_pprot -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_pready -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_prdata -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.o_lpddr_syscfg_apb4_s_pslverr -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group Bump_dec -backgroundcolor #004466 -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_A -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_ATO -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_ATO_PLL -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D -tag F0 -radix hexadecimal -subitemconfig { {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[12]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[11]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[10]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[9]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[8]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[7]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[6]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[5]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[4]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[3]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[2]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[1]} {-radix hexadecimal} {hdl_top.LPDDR_P_SUBSYSTEM.BP_B0_D[0]} {-radix hexadecimal} }
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_B1_D -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_B2_D -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_B3_D -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_CK0_C -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_CK0_T -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_CK1_C -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_CK1_T -tag F0 -radix hexadecimal
wave add hdl_top.LPDDR_P_SUBSYSTEM.BP_ZN -tag F0 -radix hexadecimal
wave add {hdl_top.ddr_if.CS_[0]} -tag F0 -radix hexadecimal
wave add hdl_top.ddr_if.CA -tag F0 -radix hexadecimal
wave add hdl_top.ddr_if.CA_B -tag F0 -radix hexadecimal
wave add {hdl_top.ddr_if.CS_[1]} -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group AXI -backgroundcolor #006666 -select
wave group {AXI:write addr} -backgroundcolor #004466
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ACLK -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWVALID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWREADY -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWADDR -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWPROT -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWREGION -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWLEN -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWSIZE -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWLOCK -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWCACHE -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWQOS -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWID -tag F0 -radix hexadecimal
wave add {hdl_top.generate_active_axi4_master_0.axi4_master_0.AWUSER[0]} -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.WVALID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.AWID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.WREADY -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.WDATA -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.WSTRB -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.WLAST -tag F0 -radix hexadecimal
wave add {hdl_top.generate_active_axi4_master_0.axi4_master_0.WUSER[0]} -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.BVALID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.BRESP -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RVALID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RREADY -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RDATA -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RRESP -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RLAST -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.RID -tag F0 -radix hexadecimal
wave add {hdl_top.generate_active_axi4_master_0.axi4_master_0.RUSER[0]} -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARVALID -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARESETn -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARREADY -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARADDR -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARLEN -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARSIZE -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARBURST -tag F0 -radix hexadecimal
wave add hdl_top.generate_active_axi4_master_0.axi4_master_0.ARID -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {FSM States} -backgroundcolor #006666 -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.ddrc_reg_operating_mode -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.gs_global_fsm_sr_hw_lp.sr_st_nxt} -tag F0 -radix mnemonic -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.gs_global_fsm_sr_hw_lp.i_phymstr_e} -tag F0 -radix hexadecimal -select
wave add hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_DWC_lpddr5x_phy.pub_top.dfi0_phyupd_type -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.current_state} -tag F0 -radix mnemonic -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.reg_ddrc_lpddr5} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.next_state} -tag F0 -radix mnemonic -backgroundcolor Salmon -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.lpddr_dev} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.reg_ddrc_lpddr5} -tag F0 -radix hexadecimal -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_global_fsm.gs_global_fsm_sr_hw_lp.sr_st_nxt} -tag F0 -radix mnemonic -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_phymstr.next_state} -tag F0 -radix mnemonic -select
wave add {hdl_top.LPDDR_P_SUBSYSTEM.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.U_ddrc.U_ddrc_cp_top.ddrc_ctrl_inst[0].U_ddrc_cp.GEN_DDRC_CPE_EN.U_ddrc_cpe.ts.gs.gs_init_ddr_fsm.reg_ddrc_dfi_reset_n} -tag F0 -radix hexadecimal -select
wave add hdl_top.top_signals_intf.i_global_rst_n -tag F0 -radix hexadecimal -select
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI:write addr} -collapse
wave group AXI -collapse
wave group Bump_dec -collapse
wave group reset_apb -collapse
wave group APB0 -collapse
wave group MRR -collapse
wave update on
wave top 0
wave bio set 2010208 Blue
wave bio set 20090 Blue
wave bio set 7 Blue
