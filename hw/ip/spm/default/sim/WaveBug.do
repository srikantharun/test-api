onerror resume
wave tags sim 
wave update off
wave zoom range 83824 175499
wave add hdl_top.i_spm_dut.u_spm_control.i_clk -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.u_spm_control.i_rst_n -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.i_axi_s_awvalid -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.o_axi_s_awready -tag sim -radix hexadecimal
wave group {ctrl params} -backgroundcolor #666600
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.NB_READ_CYCLES -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_MEM_SIZE_KB -tag sim -radix decimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_MEM_WBE_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_MEM_ADDR_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_MEM_DATA_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.ECC_PROTECTION_EN -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.OOR_ERR_EN -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_AXI_DATA_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_AXI_ADDR_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.DATA_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.ADDR_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.WBE_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.AXI_SIZE_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.MEM_ADDR_LSB -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.MEM_ADDR_MSB -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.MEM_ADDR_WIDTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.MEM_SPACE_KB -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.SPM_CTRL_RSP_FIFO_DEPTH -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.WBE_ALL_ONES -tag sim -radix hexadecimal
wave add -group {ctrl params} hdl_top.i_spm_dut.u_spm_control.WBE_ALL_ZERO -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {axi2mem bridge} -backgroundcolor #004466
wave group {axi2mem bridge:AW Channel} -backgroundcolor #666600
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awready -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awvalid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awaddr -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awburst -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awlen -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AW Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.awsize -tag sim -radix hexadecimal
wave group {axi2mem bridge:W Channel} -backgroundcolor #664400
wave add -group {axi2mem bridge:W Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.wready -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:W Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.wvalid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:W Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.wdata -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:W Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.wlast -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:W Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.wstrb -tag sim -radix hexadecimal
wave group {axi2mem bridge:B Channel} -backgroundcolor #006666
wave add -group {axi2mem bridge:B Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.bid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:B Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.bresp -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:B Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.bvalid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:B Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.bready -tag sim -radix hexadecimal
wave group {axi2mem bridge:AR Channel} -backgroundcolor #226600
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arready -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arvalid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.araddr -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arburst -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arlen -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:AR Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.arsize -tag sim -radix hexadecimal
wave group {axi2mem bridge:R Channel} -backgroundcolor #660000
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rready -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rvalid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rdata -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rid -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rlast -tag sim -radix hexadecimal
wave add -group {axi2mem bridge:R Channel} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.rresp -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_raddr -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rresp_rdy -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rvld -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_waddr -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wdata -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wresp_rdy -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wstrb -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wvld -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rrdy -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rresp_data -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rresp_error -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_rresp_vld -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wrdy -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wresp_error -tag sim -radix hexadecimal
wave add -group {axi2mem bridge} hdl_top.i_spm_dut.u_spm_control.u_axi2mem.reg_wresp_vld -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI IO} -backgroundcolor #664400
wave group {AXI IO:AW Channel} -backgroundcolor #666600
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awvalid -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awaddr -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awid -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awlen -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awsize -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awburst -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awlock -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awcache -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_awprot -tag sim -radix hexadecimal
wave add -group {AXI IO:AW Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_awready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI IO:W Channel} -backgroundcolor #664400
wave add -group {AXI IO:W Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_wvalid -tag sim -radix hexadecimal
wave add -group {AXI IO:W Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_wlast -tag sim -radix hexadecimal
wave add -group {AXI IO:W Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_wdata -tag sim -radix hexadecimal
wave add -group {AXI IO:W Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_wstrb -tag sim -radix hexadecimal
wave add -group {AXI IO:W Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_wready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI IO:B Channel} -backgroundcolor #006666
wave add -group {AXI IO:B Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_bvalid -tag sim -radix hexadecimal
wave add -group {AXI IO:B Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_bid -tag sim -radix hexadecimal
wave add -group {AXI IO:B Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_bresp -tag sim -radix hexadecimal
wave add -group {AXI IO:B Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_bready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI IO:AR Channel} -backgroundcolor #226600
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arvalid -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_araddr -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arid -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arlen -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arsize -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arburst -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arlock -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arcache -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_arprot -tag sim -radix hexadecimal
wave add -group {AXI IO:AR Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_arready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {AXI IO:R Channel} -backgroundcolor #660000
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_rvalid -tag sim -radix hexadecimal
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_rlast -tag sim -radix hexadecimal
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_rid -tag sim -radix hexadecimal
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_rdata -tag sim -radix hexadecimal
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.o_axi_s_rresp -tag sim -radix hexadecimal
wave add -group {AXI IO:R Channel} hdl_top.i_spm_dut.u_spm_control.i_axi_s_rready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave group FSMs -backgroundcolor #660000
wave add -group FSMs {hdl_top.i_spm_dut.u_spm_control.state[0]} -tag sim -radix mnemonic
wave add -group FSMs {hdl_top.i_spm_dut.u_spm_control.next_state[0]} -tag sim -radix mnemonic
wave add -group FSMs {hdl_top.i_spm_dut.u_spm_control.rsp_state[0]} -tag sim -radix mnemonic
wave add -group FSMs {hdl_top.i_spm_dut.u_spm_control.rsp_next_state[0]} -tag sim -radix mnemonic
wave insertion [expr [wave index insertpoint] + 1]
wave group {axi2reg rsp interface} -backgroundcolor #004466
wave add -group {axi2reg rsp interface} hdl_top.i_spm_dut.u_spm_control.mem_rsp.wr_rsp -tag sim -radix hexadecimal
wave add -group {axi2reg rsp interface} hdl_top.i_spm_dut.u_spm_control.mem_rsp.wr_err -tag sim -radix hexadecimal
wave add -group {axi2reg rsp interface} hdl_top.i_spm_dut.u_spm_control.mem_rsp.rd_rsp -tag sim -radix hexadecimal
wave add -group {axi2reg rsp interface} hdl_top.i_spm_dut.u_spm_control.mem_rsp.rd_err -tag sim -radix hexadecimal
wave add -group {axi2reg rsp interface} hdl_top.i_spm_dut.u_spm_control.mem_rsp.data -tag sim -radix hexadecimal -subitemconfig { {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[63]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[62]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[61]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[60]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[59]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[58]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[57]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[56]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[55]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[54]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[53]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[52]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[51]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[50]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[49]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[48]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[47]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[46]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[45]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[44]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[43]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[42]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[41]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[40]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[39]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[38]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[37]} {-radix hexadecimal} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[36]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[35]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[34]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[33]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[32]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[31]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[30]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[29]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[28]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[27]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[26]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[25]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[24]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[23]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[22]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[21]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[20]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[19]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[18]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[17]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[16]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[15]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[14]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[13]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[12]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[11]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[10]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[9]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[8]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[7]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[6]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[5]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[4]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[3]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[2]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[1]} {-radix mnemonic} {hdl_top.i_spm_dut.u_spm_control.mem_rsp.data[0]} {-radix mnemonic} }
wave insertion [expr [wave index insertpoint] + 1]
wave group {Ctrl to Mem IO} -backgroundcolor #660066
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.o_mem_req -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.o_mem_we -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.o_mem_be -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.o_mem_addr -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.o_mem_wdata -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.i_mem_rdata -tag sim -radix hexadecimal
wave add -group {Ctrl to Mem IO} hdl_top.i_spm_dut.u_spm_control.i_mem_rvalid -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {RSP FIFO} -backgroundcolor #440066
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_i_data -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_i_valid -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_ready -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data -tag sim -radix hexadecimal -expand -subitemconfig { hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data.is_write {-radix hexadecimal} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data.is_rmw {-radix hexadecimal} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data.is_error {-radix hexadecimal} }
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data_q -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_valid -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_i_ready -tag sim -radix hexadecimal
wave add -group {RSP FIFO} {hdl_top.i_spm_dut.u_spm_control.rsp_state[0]} -tag sim -radix mnemonic
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_push -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_pop -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_push_q -tag sim -radix hexadecimal
wave add -group {RSP FIFO} hdl_top.i_spm_dut.u_spm_control.rsp_fifo_pop_q -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.i_spm_dut.u_spm_control -backgroundcolor #226600
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.o_irq -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.i_scp_ecc_disable -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.o_scp_error_status -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.err_status -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.write_req -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_req -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_rsp -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_web -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_rdata_q -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_rvalid_q -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_ready -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.new_req -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.addr_hit_mem -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.addr_invalid -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.addr_d -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.addr_q -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.mem_addr_all_bit -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.in_flight_rmw_addr -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.wdata_masked -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.wdata_masked_q -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.rdata_masked -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.rmw_data -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.wdata -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.state_en -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.rsp_state_en -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.rmw_needed -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.rmw_pushed -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.new_valid_req -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.write_partial -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.waiting_for_rmw -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.gen_ecc_dec.err -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.gen_ecc_dec.syndrome -tag sim -radix hexadecimal
wave add -group hdl_top.i_spm_dut.u_spm_control hdl_top.i_spm_dut.u_spm_control.gen_ecc_dec.mem_rdata_repaired -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave spacer {}
wave add hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data.is_write -tag sim -radix hexadecimal
wave expr -alias pop -radix hexadecimal {(sim.hdl_top.i_spm_dut.u_spm_control.rsp_fifo_i_ready & sim.hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_valid)}
wave spacer {}
wave spacer {}
wave add hdl_top.i_spm_dut.u_spm_control.mem_rvalid_q -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data_q.is_rmw -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data_q.is_write -tag sim -radix hexadecimal
wave add hdl_top.i_spm_dut.u_spm_control.mem_rsp.rd_rsp -tag sim -radix hexadecimal
wave expr -alias bug -radix hexadecimal {(sim.hdl_top.i_spm_dut.u_spm_control.mem_rvalid_q & sim.hdl_top.i_spm_dut.u_spm_control.rsp_fifo_o_data_q.is_write)}
wave spacer {}
wave spacer {} -select
wave group hdl_top.i_spm_dut.u_spm_control -collapse
wave group {RSP FIFO} -collapse
wave group FSMs -collapse
wave group {AXI IO:R Channel} -collapse
wave group {AXI IO:AR Channel} -collapse
wave group {AXI IO:B Channel} -collapse
wave group {AXI IO:W Channel} -collapse
wave group {AXI IO:AW Channel} -collapse
wave group {axi2mem bridge:R Channel} -collapse
wave group {axi2mem bridge:AR Channel} -collapse
wave group {axi2mem bridge:B Channel} -collapse
wave group {axi2mem bridge:W Channel} -collapse
wave group {axi2mem bridge:AW Channel} -collapse
wave group {axi2mem bridge} -collapse
wave group {ctrl params} -collapse
wave update on
wave top 0
