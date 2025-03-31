// Performance logging signals 
// TODO Kunal: modify; rename this file to defines and move all macros here 
`define perf_signal_assignment(INTF,DUT) \
					assign INTF.perf_bank=DUT.perf_bank;\
					assign INTF.perf_bg=DUT.perf_bg;\
					assign INTF.perf_dfi_rd_data_cycles=DUT.perf_dfi_rd_data_cycles;\
					assign INTF.perf_dfi_wr_data_cycles=DUT.perf_dfi_wr_data_cycles;\
					assign INTF.perf_hif_hi_pri_rd=DUT.perf_hif_hi_pri_rd;\
					assign INTF.perf_hif_rd=DUT.perf_hif_rd;\
					assign INTF.perf_hif_rd_or_wr=DUT.perf_hif_rd_or_wr;\
					assign INTF.perf_hif_rmw=DUT.perf_hif_rmw;\
					assign INTF.perf_hif_wr=DUT.perf_hif_wr;\
					assign INTF.perf_hpr_req_with_nocredit=DUT.perf_hpr_req_with_nocredit;\
					assign INTF.perf_hpr_xact_when_critical=DUT.perf_hpr_xact_when_critical;\
					assign INTF.perf_ie_blk_hazard=DUT.perf_ie_blk_hazard;\
					assign INTF.perf_lpr_req_with_nocredit=DUT.perf_lpr_req_with_nocredit;\
					assign INTF.perf_lpr_xact_when_critical=DUT.perf_lpr_xact_when_critical;\
					assign INTF.perf_op_is_activate=DUT.perf_op_is_activate;\
					assign INTF.perf_op_is_cas=DUT.perf_op_is_cas;\
					assign INTF.perf_op_is_cas_wck_sus=DUT.perf_op_is_cas_wck_sus;\
					assign INTF.perf_op_is_cas_ws=DUT.perf_op_is_cas_ws;\
					assign INTF.perf_op_is_cas_ws_off=DUT.perf_op_is_cas_ws_off;\
					assign INTF.perf_op_is_crit_ref=DUT.perf_op_is_crit_ref;\
					assign INTF.perf_op_is_dqsosc_mpc=DUT.perf_op_is_dqsosc_mpc;\
					assign INTF.perf_op_is_dqsosc_mrr=DUT.perf_op_is_dqsosc_mrr;\
					assign INTF.perf_op_is_enter_dsm=DUT.perf_op_is_enter_dsm;\
					//TODO Kunal: uncomment; can't find in dut\
					//assign INTF.perf_op_is_enter_powerdown=DUT.perf_op_is_enter_powerdown;\
					//assign INTF.perf_op_is_enter_selfref=DUT.perf_op_is_enter_selfref;\
					assign INTF.perf_op_is_enter_powerdown=DUT.u_lpddr_subsys_wrapper.o_perf_op_is_enter_powerdown;\
					assign INTF.perf_op_is_enter_selfref=DUT.u_lpddr_subsys_wrapper.o_perf_op_is_enter_selfref;\
					assign INTF.perf_op_is_load_mode=DUT.perf_op_is_load_mode;\
					assign INTF.perf_op_is_mwr=DUT.perf_op_is_mwr;\
					assign INTF.perf_op_is_precharge=DUT.perf_op_is_precharge;\
					assign INTF.perf_op_is_rd=DUT.perf_op_is_rd;\
					assign INTF.perf_op_is_rd_activate=DUT.perf_op_is_rd_activate;\
					assign INTF.perf_op_is_rd_or_wr=DUT.perf_op_is_rd_or_wr;\
					assign INTF.perf_op_is_refresh=DUT.perf_op_is_refresh;\
					assign INTF.perf_op_is_rfm=DUT.perf_op_is_rfm;\
					assign INTF.perf_op_is_spec_ref=DUT.perf_op_is_spec_ref;\
					assign INTF.perf_op_is_tcr_mrr=DUT.perf_op_is_tcr_mrr;\
					assign INTF.perf_op_is_wr=DUT.perf_op_is_wr;\
					assign INTF.perf_op_is_zqlatch=DUT.perf_op_is_zqlatch;\
					assign INTF.perf_op_is_zqstart=DUT.perf_op_is_zqstart;\
					assign INTF.perf_precharge_for_other=DUT.perf_precharge_for_other;\
					assign INTF.perf_precharge_for_rdwr=DUT.perf_precharge_for_rdwr;\
					assign INTF.perf_rank=DUT.perf_rank;\
					assign INTF.perf_raw_hazard=DUT.perf_raw_hazard;\
					assign INTF.perf_rdwr_transitions=DUT.perf_rdwr_transitions;\
					//TODO Kunal: modify; can't find in directly in dut (probed from )\
					//assign INTF.perf_selfref_mode=DUT.perf_selfref_mode;\
					assign INTF.perf_selfref_mode=DUT.u_lpddr_subsys_wrapper.o_perf_op_is_enter_powerdown;\
					assign INTF.perf_visible_window_limit_reached_rd=DUT.perf_visible_window_limit_reached_rd;\
					assign INTF.perf_visible_window_limit_reached_wr=DUT.perf_visible_window_limit_reached_wr;\
					assign INTF.perf_war_hazard=DUT.perf_war_hazard;\
					assign INTF.perf_waw_hazard=DUT.perf_waw_hazard;\
					assign INTF.perf_wr_xact_when_critical=DUT.perf_wr_xact_when_critical;\
					assign INTF.perf_write_combine=DUT.perf_write_combine;\
					assign INTF.perf_write_combine_noecc=DUT.perf_write_combine_noecc;\
					assign INTF.perf_write_combine_wrecc=DUT.perf_write_combine_wrecc;\
