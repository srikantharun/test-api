onerror resume
wave tags  F0
wave update off
wave zoom range 0 8161007624000
wave group {AXI Address Write} -backgroundcolor #004466
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_aclk -tag F0 -radix hexadecimal -select
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awaddr -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awburst -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awcache -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awid -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awlen -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awlock -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awprot -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awqos -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awregion -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awsize -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_awready -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_awurgent -tag F0 -radix hexadecimal
wave add -group {AXI Address Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_awvalid -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {AXI Write} -backgroundcolor #006666
wave add -group {AXI Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_wdata -tag F0 -radix hexadecimal
wave add -group {AXI Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_wlast -tag F0 -radix hexadecimal
wave add -group {AXI Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_wstrb -tag F0 -radix hexadecimal
wave add -group {AXI Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_wvalid -tag F0 -radix hexadecimal
wave add -group {AXI Write} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_wready -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {AXI Bresp} -backgroundcolor #226600
wave add -group {AXI Bresp} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_bready -tag F0 -radix hexadecimal
wave add -group {AXI Bresp} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_bid -tag F0 -radix hexadecimal
wave add -group {AXI Bresp} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_bresp -tag F0 -radix hexadecimal
wave add -group {AXI Bresp} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_bvalid -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {AXI Address Read} -backgroundcolor #666600
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_aclk -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_araddr -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arburst -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arcache -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arid -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arlen -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arlock -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arprot -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arqos -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arregion -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arsize -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_arurgentb -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_arurgentr -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_arvalid -tag F0 -radix hexadecimal
wave add -group {AXI Address Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_arready -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {AXI Read} -backgroundcolor #664400
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_rdata -tag F0 -radix hexadecimal
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_rid -tag F0 -radix hexadecimal
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_rlast -tag F0 -radix hexadecimal
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_rresp -tag F0 -radix hexadecimal
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.o_lpddr_axi_m_rvalid -tag F0 -radix hexadecimal
wave add -group {AXI Read} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.i_lpddr_axi_m_rready -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Command Interface} -backgroundcolor #004466
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_address_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_address_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_address_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_address_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_cke_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_cke_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_cke_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_cke_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_dram_clk_disable_P0[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_dram_clk_disable_P1[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_dram_clk_disable_P2[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_dram_clk_disable_P3[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_address_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_address_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_address_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_address_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_cke_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_cke_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_cke_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_cke_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_dram_clk_disable_P0[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_dram_clk_disable_P1[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_dram_clk_disable_P2[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_dram_clk_disable_P3[0]} -tag F0 -radix hexadecimal
wave add -group {DFI Command Interface} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi_reset_n[0]} -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Write Data Interface} -backgroundcolor #006666
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0 -tag F0 -radix hexadecimal -subitemconfig { {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[31]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[30]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[29]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[28]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[27]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[26]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[25]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[24]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[23]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[22]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[21]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[20]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[19]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[18]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[17]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[16]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[15]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[14]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[13]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[12]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[11]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[10]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[9]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[8]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[7]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[6]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[5]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[4]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[3]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[2]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[1]} {-radix hexadecimal} {sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P0[0]} {-radix hexadecimal} }
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_mask_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_mask_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_mask_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_mask_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wrdata_cs_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_mask_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_mask_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_mask_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_mask_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Write Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wrdata_cs_P3 -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Read Data Interface} -backgroundcolor #226600
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_W3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_cs_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_dbi_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_dbi_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_dbi_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_dbi_W3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_valid_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_valid_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_valid_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_rddata_valid_W3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_W3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_cs_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_dbi_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_dbi_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_dbi_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_dbi_W3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_valid_W0 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_valid_W1 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_valid_W2 -tag F0 -radix hexadecimal
wave add -group {DFI Read Data Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_rddata_valid_W3 -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Update Interface} -backgroundcolor #666600
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_ctrlupd_req -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_ctrlupd_ack -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_ctrlupd_type -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phyupd_req -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phyupd_type -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phyupd_ack -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_ctrlupd_req -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_ctrlupd_ack -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_ctrlupd_type -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phyupd_req -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phyupd_type -tag F0 -radix hexadecimal
wave add -group {DFI Update Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phyupd_ack -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Status Interface} -backgroundcolor #664400
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_freq_ratio -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_init_complete -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_init_start -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_frequency -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_freq_fsp -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_freq_ratio -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_init_complete -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_init_start -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_frequency -tag F0 -radix hexadecimal
wave add -group {DFI Status Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_freq_fsp -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI PHY Master Interface} -backgroundcolor #660000
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phymstr_req -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phymstr_cs_state -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phymstr_state_sel -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phymstr_type -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_phymstr_ack -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phymstr_req -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phymstr_cs_state -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phymstr_state_sel -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phymstr_type -tag F0 -radix hexadecimal
wave add -group {DFI PHY Master Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_phymstr_ack -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI Low Power Control} -backgroundcolor #660066
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_ctrl_req -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_ctrl_ack -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_ctrl_wakeup -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_data_req -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_data_ack -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_lp_data_wakeup -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_ctrl_req -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_ctrl_ack -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_ctrl_wakeup -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_data_req -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_data_ack -tag F0 -radix hexadecimal
wave add -group {DFI Low Power Control} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_lp_data_wakeup -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group {DFI WCK Control Interface} -backgroundcolor #440066
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_cs_P3 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_toggle_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_toggle_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_toggle_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi0_wck_toggle_P3 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_cs_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_cs_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_cs_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_cs_P3 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_en_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_en_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_en_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_en_P3 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_toggle_P0 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_toggle_P1 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_toggle_P2 -tag F0 -radix hexadecimal
wave add -group {DFI WCK Control Interface} sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_0.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.i_uddrctl.dfi1_wck_toggle_P3 -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {DFI WCK Control Interface} -collapse
wave group {DFI Low Power Control} -collapse
wave group {DFI PHY Master Interface} -collapse
wave group {DFI Status Interface} -collapse
wave group {DFI Update Interface} -collapse
wave group {DFI Read Data Interface} -collapse
wave group {DFI Write Data Interface} -collapse
wave group {DFI Command Interface} -collapse
wave group {AXI Read} -collapse
wave group {AXI Address Read} -collapse
wave group {AXI Bresp} -collapse
wave update on
wave top 0
