onerror resume
wave tags  tbx_stw
wave update off
wave zoom range 5990774000 1095453367584000
wave spacer {}
wave group {AXI AW} -backgroundcolor #660066
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awaddr -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awburst -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awid -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awlen -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awqos -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awregion -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awsize -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_awvalid -tag tbx_stw -radix hexadecimal
wave add -group {AXI AW} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_awready -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {AXI Write} -backgroundcolor #660000
wave add -group {AXI Write} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_wdata -tag tbx_stw -radix hexadecimal
wave add -group {AXI Write} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_wlast -tag tbx_stw -radix hexadecimal
wave add -group {AXI Write} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_wstrb -tag tbx_stw -radix hexadecimal
wave add -group {AXI Write} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_wvalid -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {AXI Bresp} -backgroundcolor #664400
wave add -group {AXI Bresp} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_bready -tag tbx_stw -radix hexadecimal
wave add -group {AXI Bresp} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_bid -tag tbx_stw -radix hexadecimal
wave add -group {AXI Bresp} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_bresp -tag tbx_stw -radix hexadecimal
wave add -group {AXI Bresp} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_bvalid -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {AXI AR} -backgroundcolor #666600
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_araddr -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arburst -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arid -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arlen -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arqos -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arregion -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arsize -tag tbx_stw -radix hexadecimal
wave add -group {AXI AR} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_arvalid -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {AXI read} -backgroundcolor #226600
wave add -group {AXI read} hdl_top/i_lpddr_ppp_0/i_lpddr_axi_m_rready -tag tbx_stw -radix hexadecimal
wave add -group {AXI read} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_rdata -tag tbx_stw -radix hexadecimal
wave add -group {AXI read} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_rid -tag tbx_stw -radix hexadecimal
wave add -group {AXI read} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_rlast -tag tbx_stw -radix hexadecimal
wave add -group {AXI read} hdl_top/i_lpddr_ppp_0/o_lpddr_axi_m_rvalid -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {DFI error} -backgroundcolor #660000
wave add -group {DFI error} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_error_info -tag tbx_stw -radix hexadecimal
wave add -group {DFI error} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_error[0]} -tag tbx_stw -radix hexadecimal
wave add -group {DFI error} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_error_info -tag tbx_stw -radix hexadecimal
wave add -group {DFI error} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_error[0]} -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {DFI0 Write} -backgroundcolor #664400
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_clk -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/lpddr5_wck -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_address_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_reset_n_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_p0 -tag tbx_stw -radix hexadecimal -select
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_en_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_en_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_en_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_en_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_cs_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_cs_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_cs_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_mask_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_mask_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_mask_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_wrdata_mask_p3 -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {DFI0 Read} -backgroundcolor #666600
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_en_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_en_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_en_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_en_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_cs_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_cs_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_cs_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_w0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_w1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_w2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_w3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_valid_w0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_valid_w1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_valid_w2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI0 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dfi_rddata_valid_w3 -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {DFI1 Write} -backgroundcolor #226600
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_clk -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/lpddr5_wck -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_address_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_reset_n_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_en_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_en_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_en_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_en_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_cs_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_cs_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_cs_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_mask_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_mask_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_mask_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Write} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_wrdata_mask_p3 -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {DFI1 Read} -backgroundcolor #006666
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_en_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_en_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_en_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_en_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_cs_p0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_cs_p1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_cs_p2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_cs_p3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_w0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_w1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_w2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_w3 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_valid_w0 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_valid_w1 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_valid_w2 -tag tbx_stw -radix hexadecimal
wave add -group {DFI1 Read} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dfi_rddata_valid_w3 -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {Indicator Settings} -backgroundcolor #006666
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/bl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_preamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_postamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wr_db_inversion} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_db_inversion} -tag tbx_stw -radix hexadecimal
wave spacer -group {Indicator Settings} {}
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/bl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_preamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_postamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wr_db_inversion} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_db_inversion} -tag tbx_stw -radix hexadecimal
wave spacer -group {Indicator Settings} {}
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting} -tag tbx_stw -radix hexadecimal -subitemconfig { {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting[3]} {-radix hexadecimal} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting[2]} {-radix hexadecimal} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting[1]} {-radix hexadecimal} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting[0]} {-radix hexadecimal} }
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/bl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_preamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_postamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wr_db_inversion} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_db_inversion} -tag tbx_stw -radix hexadecimal
wave spacer -group {Indicator Settings} {}
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/bl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wl_value} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_preamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_postamble_setting} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/wr_db_inversion} -tag tbx_stw -radix hexadecimal
wave add -group {Indicator Settings} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/dram_rank_loop[1]/dram_inst_loop[0]/lpddr5_sm/lpddr5_indicator_if/rd_db_inversion} -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave group {Timing parameters} -backgroundcolor #004466
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/t_phy_wrlat -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/t_phy_wrdata -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/t_rddata_en -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/t_phy_rdlat -tag tbx_stw -radix hexadecimal
wave spacer -group {Timing parameters} {}
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/t_phy_wrlat -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/t_phy_wrdata -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/t_rddata_en -tag tbx_stw -radix hexadecimal
wave add -group {Timing parameters} hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi1_lpddr5/t_phy_rdlat -tag tbx_stw -radix hexadecimal
wave insertion next
wave spacer {}
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/RESET_N} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/CK_t} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/CK_c} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/WCK_t} -tag tbx_stw -radix hexadecimal -subitemconfig { {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/WCK_t[1]} {-radix hexadecimal} {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/WCK_t[0]} {-radix hexadecimal} }
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/WCK_c} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/CS} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/CA} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/DQ} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/RDQS_t} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/RDQS_c} -tag tbx_stw -radix hexadecimal
wave add {hdl_top/i_lpddr_ppp_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/dfi0_lpddr5/dram_rank_loop[0]/dram_inst_loop[0]/lpddr5_sm/DMI} -tag tbx_stw -radix hexadecimal
wave group {Indicator Settings} -collapse
wave group {DFI1 Read} -collapse
wave group {DFI1 Write} -collapse
wave group {AXI read} -collapse
wave group {AXI AR} -collapse
wave group {AXI Bresp} -collapse
wave group {AXI Write} -collapse
wave group {AXI AW} -collapse
wave update on
wave top 0
