



  property check_reset(reset , signal);
(@(posedge clk) $rose(reset)|-> ((signal !== 'x) && (signal !== 'z) ));
endproperty




OUT_s_CID_O_X_AND_Z : assert property(check_reset(rst_n , dut.cid_o))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion is success ..................",UVM_LOW)
else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_CID_O output signal is either X or Z is failure")



OUT_s_iau_dpu_iid_o_X_AND_Z : assert property(check_reset(rst_n , dut.iau_dpu_iid_o))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion is success ..................",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_iau_dpu_iid_o  signal is either X or Z is failure")

 
OUT_s_RESERVED_O_X_AND_Z : assert property(check_reset(rst_n , dut.reserved_o))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion is success ..................",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_RESERVED_O  signal is either X or Z is failure")


OUT_s_AI_CORE_OBS_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_obs))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n5 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_iau_dpu_0_obs_i  signal is either X or Z is failure")


//OUT_s_AI_CORE_MVM_RST_N_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_rst_n))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n7 is success ...................@%0t",UVM_LOW)

//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_MVM_RST_N  signal is either X or Z is failure")
//
//OUT_s_AI_CORE_DWPU_RST_N_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_rst_n))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n8 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_DWPU_RST_N  signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_RST_N_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_rst_n))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n8 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_RST_N  signal is either X or Z is failure")
//
//
//
//
//
//
//OUT_s_AI_CORE_IAU_DPU_1_RST_N_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_rst_n))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n9 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_RST_N  signal is either X or Z is failure")
//
//OUT_s_AI_CORE_LS_RST_N_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_rst_n))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n10 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_RST_N  signal is either X or Z is failure")
//
OUT_s_LS_MEM_LS_X_AND_Z : assert property(check_reset(rst_n , dut.l1_mem_ls))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n11 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_LS_MEM_LS  signal is either X or Z is failure")


 OUT_s_LS_L1_MEM_DS_X_AND_Z : assert property(check_reset(rst_n , dut.l1_mem_ds))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n12 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_LS_MEM_DS  signal is either X or Z is failure")

OUT_s_LS_MEM_SD_X_AND_Z : assert property(check_reset(rst_n , dut.l1_mem_sd))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n13 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_LS_MEM_SD  signal is either X or Z is failure")


OUT_s_LS_MEM_DAISY_CHAIN_BYPASS_SD_X_AND_Z : assert property(check_reset(rst_n , dut.l1_mem_daisy_chain_bypass_sd))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n15 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_LS_MEM_DAISY_CHAIN_BYPASS_SD  signal is either X or Z is failure")

OUT_s_LS_MEM_DAISY_CHAIN_BYPASS_DS_X_AND_Z : assert property(check_reset(rst_n , dut.l1_mem_daisy_chain_bypass_ds))
`uvm_info("OUT_ASSERTION PASS","assertion_n16 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_LS_MEM_DAISY_CHAIN_BYPASS_DS  signal is either X or Z is failure")

OUT_s_TOPCTRL_L1_MEM_PWR_MODE_X_AND_Z : assert property(check_reset(rst_n , dut.topctrl_l1_mem_pwr_mode))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n17 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_TOPCTRL_L1_MEM_PWR_MODE  signal is either X or Z is failure")


OUT_s_TOPCTRL_L1_MEM_ROP_X_AND_Z : assert property(check_reset(rst_n , dut.topctrl_l1_mem_rop))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n18 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_TOPCTRL_L1_MEM_ROP signal is either X or Z is failure")

OUT_s_HART_UNAVAIL_ASYNC_I_X_AND_Z : assert property(check_reset(rst_n , dut.hart_unavail_async_o))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n20 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_GART_UNAVAIL_ASYNC_I signal is either X or Z is failure")

OUT_s_HART_under_reset_ASYNC_I_X_AND_Z : assert property(check_reset(rst_n , dut.hart_under_reset_async_o))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n21 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_GART_UNAVAIL_ASYNC_I signal is either X or Z is failure")

OUT_s_STOPTIME_ASYNC_I_X_AND_Z : assert property(check_reset(rst_n , dut.stoptime_async_o))
`uvm_info("OUT_ASSERTION PASS","assertion_n22 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_STOPTIME_ASYNC_O  signal is either X or Z is failure")


OUT_s_L1_SW_CFG_FABRIC_SEL_X_AND_Z : assert property(check_reset(rst_n , dut.l1_sw_cfg_fabric_sel))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n30 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_L1_SW_CFG_FABRIC_SEL signal is either X or Z is failure")


OUT_s_SRAM_SW_TEST1_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_test1))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n31 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_TEST1  signal is either X or Z is failure")

OUT_s_SRAM_SW_TEST_RNM_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_test_rnm))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n32 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_TEST_RNM  signal is either X or Z is failure")



OUT_s_SRAM_SW_RME_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_rme))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n33 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_RME  signal is either X or Z is failure")



OUT_s_SRAM_SW_RM_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_rm))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n34 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_RM  signal is either X or Z is failure")



OUT_s_SRAM_SW_WA_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_wa))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n35 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_WA  signal is either X or Z is failure")



OUT_s_SRAM_SW_WPULSE_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_wpulse))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n36 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_WPULSE  signal is either X or Z is failure")



OUT_s_SRAM_SW_FISO_X_AND_Z : assert property(check_reset(rst_n , dut.sram_sw_fiso))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n37 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_SRAM_SW_FISO  signal is either X or Z is failure")



  //////////  assertions for NOC_HP_AXI_S   \\\\\\\\\\\\\

OUT_s_NOC_HP_AXI_S_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n37 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWVALID_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n38 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWADDR_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n39 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWID_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n40 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWLEN_ signal is either X or Z is failure")





OUT_s_NOC_HP_AXI_S_AWBURST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n41 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWBURST_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n42 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWSIZE_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_AWCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n43 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWCACHE_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_AWPROT_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n44 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWPROT_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_AWLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_awlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n45 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_AWLOCK_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS"," OUT_s_assertion_n47 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_WVALID_ signal is either X or Z is failure")

 OUT_s_NOC_HP_AXI_S_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n48 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_WLAST_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n49 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_WSTRB_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n50 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_WDATA_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n54 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_BREADY_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n55 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARVALID_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n56 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARADDR_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n57 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARID_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n58 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARLEN_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n59 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARSIZE_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n60 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARBURST_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n61 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARCACHE_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARPROT_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n62 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARPROT_ signal is either X or Z is failure")


OUT_s_NOC_HP_AXI_S_ARLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_arlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n63 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_ARLOCK_ signal is either X or Z is failure")

OUT_s_NOC_HP_AXI_S_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_hp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n70 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_HP_AXI_S_RREADY_ signal is either X or Z is failure")





     ////////// assertions for AI_CORE_LS_HP_AXI_S   \\\\\\\\\\\\\\\\\




OUT_s_AI_CORE_LS_HP_AXI_S_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n71 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWVALID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n72 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWADDR_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n73 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n74 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWLEN_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n75 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWSIZE_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWburst_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n76 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWBURST_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n77 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWCACHE_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWPROT_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n78 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWPROT_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_AWLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_awlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n79 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_AWLOCK_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n81 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_WVALID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n82 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_WLAST_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n83 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_WSTRB_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n84 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_WDATA_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n89 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_BREADY_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n90 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARVALID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n91 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARADDR_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n92 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n93 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARLEN_ signal is either X or Z is failure")


OUT_s_AI_CORE_LS_HP_AXI_S_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n94 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARSIZE_ signal is either X or Z is failure")



OUT_s_AI_CORE_LS_HP_AXI_S_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n95 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARLEN_ signal is either X or Z is failure")



OUT_s_AI_CORE_LS_HP_AXI_S_ARCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n96 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARCHCHE_ signal is either X or Z is failure")



OUT_s_AI_CORE_LS_HP_AXI_S_ARPORT_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n97 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARPROT_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_ARLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_arlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n98 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_ARLOCK_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_S_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n167 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_S_RREADY_ signal is either X or Z is failure")



     ///       ASSERTIONS FOR AI_CORE_LS_HP_AXI_M       \\\\


OUT_s_AI_CORE_LS_HP_AXI_M_AWREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_awready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n115 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_AWREADY_ signal is either X or Z is failure")


OUT_s_AI_CORE_LS_HP_AXI_M_BVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_bvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n121 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_BVALID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_BID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_bid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n122 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_BID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_BRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_bresp))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n123 is success ...................@%0t",UVM_LOW)

      
else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_BRESP_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_ARREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_arready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n132 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_ARREADY_ signal is either X or Z is failure")


OUT_s_AI_CORE_LS_HP_AXI_M_RVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_rvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n133 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_RVALID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_RLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_rlast))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n134 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_RLAST_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_RID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_rid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n135 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_RID_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_RDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_rdata))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n136 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_RDATA_ signal is either X or Z is failure")

OUT_s_AI_CORE_LS_HP_AXI_M_RRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_hp_axi_m_rresp))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n137 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_LS_HP_AXI_M_RRESP_ signal is either X or Z is failure")



////////////////////////     ASSERTIONS FOR AI_CORE_IAU_DPU_0_HP_AXI_M            \\\\\\\\\\\\\\\\\\\\\\\
//
//commented as DPU_0/1 ports got removed in omega project
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_AWREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_awready))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n145 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_AWREADY_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_WREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_wready))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n150 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_WREADY_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_bvalid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n151 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BVALID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_bid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n152 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_bresp))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n153 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_BRESP_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_ARREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_arready))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n161 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_ARREADY_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_rvalid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n162 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RVALID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_rlast))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n163 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RLAST_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_rid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n164 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_rdata))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n165 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RDATA_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_hp_axi_m_rresp))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n166 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_0_HP_AXI_M_RRESP_ signal is either X or Z is failure")
//
//                 //////////////////      ASSERTIONS FOR AI_CORE_IAU_DPU_1_HP_AXI_M_READY          \\\\\\\\\\\\\\\\\\\\\\\\
//
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_WREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_wready))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n179 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_WREADY_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_bvalid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n180 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BVALID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_bid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n181 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_bresp))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n182 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_BRESP_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_ARREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_arready))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n190 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_ARREADY_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_rvalid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n191 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RVALID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_rlast))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n192 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RLAST_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_rid))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n193 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RID_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_rdata))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n194 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RDATA_ signal is either X or Z is failure")
//
//OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RRESP_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_hp_axi_m_rresp))
//`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n195 is success ...................@%0t",UVM_LOW)
//
//else
//`uvm_error("OUT_ASSERTION FAIL","OUT_s_AI_CORE_IAU_DPU_1_HP_AXI_M_RRESP_ signal is either X or Z is failure")

                 //////////////////      ASSERTIONS FOR NOC_LP_AXI_M_          \\\\\\\\\\\\\\\\\\\\\\\\


OUT_s_NOC_lP_AXI_m_AWREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_awready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n206 is success ...................@%0t",UVM_LOW)

else
`uvm_info("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_AWREADY_ signal is either X or Z is failure",UVM_LOW)


OUT_s_NOC_lP_AXI_m_WREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_wready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n211 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_WREADY_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_BVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_bvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n212 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_BVALID_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_BID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_bid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n213 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_BID_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_BRESP_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_bresp))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n214 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_BRESP_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_ARREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_arready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n225 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_ARREADY_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_m_RVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_rvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n226 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_RVALID_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_RLAST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_rlast))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n227 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_RLAST_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_m_RID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_rid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n228 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_RID_ signal is either X or Z is failure")




OUT_s_NOC_lP_AXI_m_RDATA_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_rdata))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n229 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_RDATA_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_m_RRESP_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_m_rresp))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n230 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_RRESP_ signal is either X or Z is failure")


    //////////////  assertions for NOC_LP_AXI_S         \\\\\\\\\\\\\








OUT_s_NOC_LP_AXI_s_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n232 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWVALID_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n233 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_m_AWADDR_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n234 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWID_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_235 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWLEN_ signal is either X or Z is failure")





OUT_s_NOC_lP_AXI_s_AWBURST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n236 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWBURST_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n237 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWSIZE_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_AWCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n238 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWCACHE_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_AWPROT_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n239 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWPROT_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_AWLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_awlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n240 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_AWLOCK_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n242 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_WVALID_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n243 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_WLAST_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n244 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_WSTRB_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n245 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_WDATA_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n250 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_BREADY_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n251 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARVALID_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n252 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARADDR_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n253 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARID_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n254 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARLEN_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n255 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARSIZE_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n256 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARBURST_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arcache))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n257 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARCACHE_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARPROT_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arprot))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n258 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARPROT_ signal is either X or Z is failure")


OUT_s_NOC_lP_AXI_s_ARLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_arlock))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n259 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_ARLOCK_ signal is either X or Z is failure")

OUT_s_NOC_lP_AXI_s_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.noc_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_s_assertion_n266 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_s_NOC_lP_AXI_s_RREADY_ signal is either X or Z is failure")



         ////////////////////////   assertions for AI_CORE_MVM_LP_AXI_S




OUT_AI_CORE_mvm_lP_AXI_S_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n267 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_sAI_CORE_mvm_lP_AXI_S_AWVALID_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n268 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_AWADDR_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n269 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_AWID_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n270 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_AWLEN_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n271 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_AWSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_AWburst_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n272 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_AWBURST_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n277 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_WVALID_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n278 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_WLAST_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n279 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_WSTRB_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n280 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_WDATA_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n285 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_BREADY_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n286 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARVALID_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n287 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARADDR_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n288 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARID_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n289 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARLEN_ signal is either X or Z is failure")


OUT_AI_CORE_mvm_lP_AXI_S_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n290 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARSIZE_ signal is either X or Z is failure")



OUT_AI_CORE_mvm_lP_AXI_S_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n291 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_mvm_lP_AXI_S_RRESDY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_mvm_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n302 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_mvm_lP_AXI_S_RREADY_ signal is either X or Z is failure")



    ////////////// assertions for AI_CORE_DWPU_LP_AXI_S



OUT_AI_CORE_dwpu_lP_AXI_S_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n303 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWVALID_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n304 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWADDR_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n305 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWID_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n306 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWLEN_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n307 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_AWburst_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n308 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_AWLOCK_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n313 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_WVALID_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n314 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_WLAST_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n315 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_WSTRB_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n316 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_WDATA_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n321 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_BREADY_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n322 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARVALID_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n323 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARADDR_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n324 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARID_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n325 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n326 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n327 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_dwpu_lP_AXI_S_RRESDY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_dwpu_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n338 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_dwpu_lP_AXI_S_RREADY_ signal is either X or Z is failure")




    /////////////   AI_CORE_IAU_DPU_0_LP_AXI_s



OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n339 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWVALID_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n340 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWADDR_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n341 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n342 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWLEN_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n343 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n344 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AWBURST_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n346 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WVALID_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n347 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WLAST_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n348 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WSTRB_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n349 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_WDATA_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n354 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_BREADY_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_AR_VALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n355 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARVALID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n356 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARADDR_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n357 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n358 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n359 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n360 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_ARBURST_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_0_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n367 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_0_lP_AXI_s_RREADY_ signal is either X or Z is failure")




                 //////////////////      ASSERTIONS FOR AI_CORE_IAU_DPU_1_HP_AXI_M_READY          \\\\\\\\\\\\\\\\\\\\\\\\



OUT_AI_CORE_IAU_DPU_1_LP_AXI_s_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n368 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWVALID_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n369 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWADDR_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n370 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n371 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWLEN_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n372 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n373 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AWBURST_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n375 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_WVALID_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n376 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lp_AXI_s_WLAST_ signal is either X or Z is failure")


OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n377 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_WSTRB_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n383 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_BREADY_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_AR_VALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n384 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARVALID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n385 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARADDR_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n386 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARID_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n387 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n388 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n389 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_ARBURST_ signal is either X or Z is failure")

OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_iau_dpu_1_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n396 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_IAU_DPU_1_lP_AXI_s_RREADY_ signal is either X or Z is failure")



   //////////////   assertions for ai_core_lp_ls_s    \\\\\\\\\\\\\\



OUT_AI_CORE_LS_lP_AXI_S_AWVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n397 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWVALID_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awaddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n398 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWADDR_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n399 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWID_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n400 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWLEN_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n401 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWburst_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n402 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWBURST_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awcache))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n403 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWCACHE_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWPROT_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awprot))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n404 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWPROT_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_AWLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_awlock))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n405 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_AWLOCK_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_WVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_wvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n407 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_WVALID_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_WLAST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_wlast))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n408 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_WLAST_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_WSTRB_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_wstrb))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n410 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_WSTRB_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_WDATA_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_wdata))
`uvm_info("OUT_ASSERTION PASS","assertion_n411 is success ...................@%0t",UVM_LOW)

else
`uvm_error("ASSERTION FAIL", "AI_CORE_LS_lP_AXI_S_WDATA_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_BREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_bready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n416 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_BREADY_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARVALID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arvalid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n417 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARVALID_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARADDR_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_araddr))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n418 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARADDR_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARID_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arid))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n419 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARID_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARLEN_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arlen))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n420 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARSIZE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arsize))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n421 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARSIZE_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARBURST_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arburst))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n422 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARLEN_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARCACHE_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arcache))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n423 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARCHCHE_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARPORT_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arprot))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n424 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARPROT_ signal is either X or Z is failure")

OUT_AI_CORE_LS_lP_AXI_S_ARLOCK_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_arlock))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n425 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_ARLOCK_ signal is either X or Z is failure")


OUT_AI_CORE_LS_lP_AXI_S_RREADY_X_AND_Z : assert property(check_reset(rst_n , dut.ai_core_ls_lp_axi_s_rready))
`uvm_info("OUT_ASSERTION PASS","OUT_assertion_n428 is success ...................@%0t",UVM_LOW)

else
`uvm_error("OUT_ASSERTION FAIL","OUT_AI_CORE_LS_lP_AXI_S_RREADY_ signal is either X or Z is failure")
