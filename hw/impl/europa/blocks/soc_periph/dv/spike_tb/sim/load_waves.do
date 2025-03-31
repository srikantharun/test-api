onerror resume
wave tags  F0
wave update off
wave zoom range 450743610 473517500
wave spacer -backgroundcolor Salmon {Write signals}
wave group GROUP1 -backgroundcolor #004466
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].aresetn} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awvalid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awaddr} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awlen} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awsize} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].awready} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wvalid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wlast} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wdata} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wstrb} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wready} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].wid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].bvalid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].bresp} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].bid} -tag F0 -radix hexadecimal
wave add -group GROUP1 {spike_top_tb.th.axi_if.master_if[0].bready} -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave spacer -backgroundcolor Salmon {Read signals}
wave group GROUP0 -backgroundcolor #004466
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arvalid} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].araddr} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arlen} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arsize} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arburst} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arlock} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arcache} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arprot} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arid} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].arready} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rvalid} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rlast} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rdata} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rresp} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rid} -tag F0 -radix hexadecimal
wave add -group GROUP0 {spike_top_tb.th.axi_if.master_if[0].rready} -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave spacer -backgroundcolor Salmon {EMMC APB signals}
wave group GROUP2 -backgroundcolor #004466
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_pclk -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_preset_n -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_s_paddr -tag F0 -radix hexadecimal
wave expr -group GROUP2  -alias access_srs12 -radix hexadecimal {(spike_top_tb.th.u_soc_periph.u_emmc.i_s_paddr[31:0] == 32'h03050230)}
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_s_pwrite -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_s_penable -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_s_psel -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.i_s_pwdata -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.o_s_prdata -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.o_s_pready -tag F0 -radix hexadecimal
wave add -group GROUP2 spike_top_tb.th.u_soc_periph.u_emmc.o_s_pslverr -tag F0 -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer -backgroundcolor Salmon {EMMC interface signals}
wave group GROUP3 -backgroundcolor #226600
wave add -group GROUP3 @emmc_card_cl@1.card_st -tag F0 -radix mnemonic
wave add -group GROUP3 @sd_xtor_cl@1.dat_bus_st -tag F0 -radix mnemonic
wave add -group GROUP3 @sd_xtor_cl@1.cmd_bit_cntr -tag F0 -radix decimal
wave add -group GROUP3 @sd_xtor_cl@1.cmd_bus_st -tag F0 -radix mnemonic
wave add -group GROUP3 @sd_xtor_cl@1.bus_speed -tag F0 -radix mnemonic
wave add -group GROUP3 spike_top_tb.th.sd_if.cmd -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.sd_if.clk -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.sd_if.dat -tag F0 -radix hexadecimal -subitemconfig { {spike_top_tb.th.sd_if.dat[7]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[6]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[5]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[4]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[3]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[2]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[1]} {-radix hexadecimal} {spike_top_tb.th.sd_if.dat[0]} {-radix hexadecimal} }
wave add -group GROUP3 spike_top_tb.th.sd_if.rst_n -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.sd_if.sdwp_n -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.sd_if.bus_pow -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.sd_if.bus_lvs -tag F0 -radix hexadecimal
wave spacer -group GROUP3 {}
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.cmd_fall -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.cmd_i -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.cmd_i_r -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.fsm_cmd_r -tag F0 -radix mnemonic
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.timeout_cnt -tag F0 -radix decimal
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_ciu.u_cdns_sdhc_ciu_cmd.cmd_err -tag F0 -radix hexadecimal
wave add -group GROUP3 spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.u_cdns_sdhc.u_cdns_sdhc_core.u_cdns_sdhc_biu.u_cdns_sdhc_biu_srs_0.srs12_full_s -tag F0 -radix hexadecimal -select
wave insertion [expr [wave index insertpoint] + 1]
wave spacer -backgroundcolor #ffaa7f {EMMC PHY interface}
wave add spike_top_tb.th.u_soc_periph.o_mem_webar_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_webar_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_webar_opad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_data_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_data_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_data_opad -tag F0 -radix hexadecimal -subitemconfig { {spike_top_tb.th.u_soc_periph.o_mem_data_opad[7]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[6]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[5]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[4]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[3]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[2]} {-radix hexadecimal -select} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[1]} {-radix hexadecimal} {spike_top_tb.th.u_soc_periph.o_mem_data_opad[0]} {-radix hexadecimal} }
wave add spike_top_tb.th.u_soc_periph.u_emmc.o_mem_cmd_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.cmd_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.o_mem_cmd_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.o_mem_cmd_opad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.pad_mem_cmd -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.i_mem_cmd_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.cmd_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.i_mem_cmd_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_ctrl_1_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.data_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_ctrl_1_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.o_mem_ctrl_1_opad -tag F0 -radix hexadecimal
wave spacer -backgroundcolor #ffaa00 {Read FIFO}
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.mem_cmd -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.clk -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.clk_dqs -tag F0 -radix hexadecimal
wave add {spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_dqs_in.mem_dqs[0]} -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dqs.lpbk_en_scan -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dqs.lpbk_rddqs -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dqs.dqs_mux_out -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dqs.dqs_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dqs.phony_lpbk_dqs_mux_out -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.rst_n -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.rst_clkn_n -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.dll_rst_n -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.scanmode -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.resync_dll -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.lpbk_en -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.rptr_upd -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.sync_method -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.rptr_upd_empty -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.dfi_read_cmdblk.read_cmdblk_fifo.underrun_suppress -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.clk_phy -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.reg_pclk -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.flash_dll_phy_nand.Inst_flash_databahn_dll_phy.dll_phy_slice_core.data_slice_0.mem_dqs -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.cdn_ip6185_1990_dll_phy_top_0.i_mem_lpbk_dqs_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.i_mem_rebar_ipad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.o_mem_rebar_oepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.o_mem_rebar_iepad -tag F0 -radix hexadecimal
wave add spike_top_tb.th.u_soc_periph.u_emmc.u_cdns_sdhc_top.o_mem_rebar_opad -tag F0 -radix hexadecimal
wave group GROUP1 -collapse
wave update on
wave top 19
