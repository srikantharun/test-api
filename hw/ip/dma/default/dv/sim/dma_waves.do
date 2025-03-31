onerror resume
wave tags sim 
wave update off
wave zoom range 0 489375
wave add hdl_top.clk_en -tag sim -radix hexadecimal
wave add hdl_top.sys_clk -tag sim -radix hexadecimal
wave add hdl_top.sys_rst_n -tag sim -radix hexadecimal
wave group {hdl_top.axi_if.master_if[0]} -backgroundcolor #006666
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].common_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].is_active} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].common_clock_mode} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].clock_enable} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].internal_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aresetn} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awvalid} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wlast} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bvalid} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].araddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arready} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rlast} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} hdl_top.dut_axi_s_awvalid -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} hdl_top.dut_axi_s_awvalid -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.master_if[0]} {}
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awstashnid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awstashlpid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awstashnid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awstashlpid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awatop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awmpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awtagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awdomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awcmo} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awunique} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].artagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].ardomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].artrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].armpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].araddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arctlchk3} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].ridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].ridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wtagupdate} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wstrbchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].btrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].btagmatch} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bcomp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bpersist} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].breadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].bidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].brespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].arqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].ruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].buser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].awuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].aruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].wuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].ruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].buserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acwakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].actrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acctlchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acvmidextchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].acwakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].crrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cddata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cddatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].cdlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tdest} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tkeep} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].tuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].archunken} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rchunkv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rchunknum} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].rchunkstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].mon_snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].param_check_flag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_addr_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_data_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_id_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_ace_snoop_addr_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_ace_snoop_data_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_max_tdest_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_max_tid_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_max_tuser_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_max_rchunknum_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].svt_axi_max_rchunkstrb_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} {hdl_top.axi_if.master_if[0].full_name} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.master_if[0]} hdl_top.dut_axi_s_awaddr -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave spacer {}
wave add hdl_top.dut_axi_s_awaddr -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_awid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_awready -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_s_wdata -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_wstrb -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_wvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_wready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_wlast -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_s_bresp -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_bid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_bready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_bvalid -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_s_araddr -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_arid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_arvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_arready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_arlen -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_arsize -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_s_rdata -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_rid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_rresp -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_rvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_rready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_s_rlast -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_awaddr -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awready -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_awlen -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awsize -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awburst -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awlock -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awcache -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_awprot -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_wdata -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_wstrb -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_wvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_wready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_wlast -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_bresp -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_bid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_bvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_bready -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_araddr -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arready -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_arlen -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arsize -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arburst -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arlock -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arcache -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_arprot -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut_axi_m_rdata -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_rid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_rresp -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_rvalid -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_rready -tag sim -radix hexadecimal
wave add hdl_top.dut_axi_m_rlast -tag sim -radix hexadecimal
wave spacer {}
wave group {DUT-Register AXI-IF} -backgroundcolor #004466
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_clk -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_rst_n -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awvalid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awaddr -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awlen -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awsize -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awburst -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awlock -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awcache -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_awprot -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_awready -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_wvalid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_wlast -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_wdata -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_wstrb -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_wready -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_bvalid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_bid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_bresp -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_bready -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arvalid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_araddr -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arlen -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arsize -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arburst -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arlock -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arcache -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_arprot -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_arready -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_rvalid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_rlast -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_rid -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_rdata -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.o_axi_s_rresp -tag sim -radix hexadecimal
wave add -group {DUT-Register AXI-IF} hdl_top.dut.i_axi_s_rready -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dut.u_progif.u_axi_demux -backgroundcolor #004466
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.NR_MASTERS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.MT_ST_ADDR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.MT_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.IDW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.AW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.DW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.BW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_WREQ_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_RREQ_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_WDATA_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_WRESP_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.SL_RRESP_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.OSR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.i_clk -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.i_rst_n -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awaddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_araddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_bid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_bresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_bvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.s_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awaddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_araddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_bid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_bresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_bvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.m_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux hdl_top.dut.u_progif.u_axi_demux.zero_array -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dut.u_progif.u_axi_demux.i_wr_path -backgroundcolor #006666
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.sel -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_q -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_rvld -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.sel -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_wrdy -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.req -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.req_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.req_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.req_vld -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_vld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_q -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_wready -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_q -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_rrdy -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path {}
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.NR_MASTERS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.SL_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.MT_ST_ADDR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.SL_WDATA_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.MT_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.IDW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.AW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.DW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.BW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.OSR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.SL_REQ_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.SL_RESP_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.WRITE -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.i_clk -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.i_rst_n -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_id -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_len -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_addr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_size -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_burst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_lock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_prot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_cache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_valid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_ready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.s_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_id -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_len -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_addr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_size -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_burst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_lock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_prot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_cache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_valid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_ready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.m_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.SelW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.RespDw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.sel -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_sel_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_sel_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_sel_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_sel_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.resp_sel_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_sel_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_last_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_last_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_last_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.wdata_last_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.addr_err -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.rd_err_cnt_rst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.rd_err_cnt_inc -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path hdl_top.dut.u_progif.u_axi_demux.i_wr_path.rd_err_cnt -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dut.u_progif.u_axi_demux.i_rd_path -backgroundcolor #226600
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.NR_MASTERS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.SL_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.MT_ST_ADDR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.MT_CAP -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.IDW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.AW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.DW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.BW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.OSR -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.SL_REQ_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.SL_WDATA_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.SL_RESP_SHIELD -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.WRITE -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.i_clk -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.i_rst_n -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_id -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_len -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_addr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_size -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_burst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_lock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_prot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_cache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_valid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_ready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.s_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_id -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_len -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_addr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_size -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_burst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_lock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_prot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_cache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_valid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_ready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.m_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.SelW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.RespDw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.req -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.req_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.req_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.req_vld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_vld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.sel -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_sel_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_sel_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_sel_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_sel_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.resp_sel_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_sel_q -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_sel_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_sel_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_sel_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_sel_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_last_wrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_last_wvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_last_rrdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.wdata_last_rvld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.addr_err -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.rd_err_cnt_rst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.rd_err_cnt_inc -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_rd_path hdl_top.dut.u_progif.u_axi_demux.i_rd_path.rd_err_cnt -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo -backgroundcolor #666600
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.i_rst_n -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.i_clk -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.DEPTH -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.DW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.USE_MACRO -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.wr_vld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.wr_data -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.wr_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.rd_rdy -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.rd_data -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.rd_vld -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.rd_req -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.rd_empty -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.wr_req -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo.wr_full -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dut.u_progif -backgroundcolor #664400
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_aw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_w -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_wready -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif {}
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_csr_axi_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_cmd_axi_awready -tag sim -radix hexadecimal
wave spacer -group hdl_top.dut.u_progif {}
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.NUM_PORTS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.NUM_CHNLS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_clk -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_rst_n -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awaddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_awprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_bvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_bid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_bresp -tag sim -radix mnemonic
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_araddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_arprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_axi_s_rresp -tag sim -radix mnemonic
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_axi_s_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_global_cfg -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_global_sts -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_aw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_ar -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_w -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_csr_axi_r -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_csr_axi_b -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_csr_axi_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_aw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_ar -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_w -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_cmd_axi_r -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.i_chnl_cmd_axi_b -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.o_chnl_cmd_axi_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.NR_MASTERS -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.BW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.IDW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.AW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.DW -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awaddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arlen -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_araddr -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arsize -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arburst -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arlock -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arprot -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arcache -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_wdata -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_wstrb -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_wlast -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_wvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_bid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_bresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_bvalid -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.m_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.axi_s_rresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.axi_s_bresp -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_aw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_ar -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_w -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_r -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_b -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.global_csr_axi_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_aw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_awready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_ar -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_arready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_w -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_wready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_r -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_rready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_b -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.mmu_csr_axi_bready -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.reg2hw -tag sim -radix hexadecimal
wave add -group hdl_top.dut.u_progif hdl_top.dut.u_progif.hw2reg -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.wr_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[1].u_chnl.u_csr.wr_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[2].u_chnl.u_csr.wr_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[3].u_chnl.u_csr.wr_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.rd_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[1].u_chnl.u_csr.rd_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[2].u_chnl.u_csr.rd_addr_hit} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[3].u_chnl.u_csr.rd_addr_hit} -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.m_wready -tag sim -radix hexadecimal -expand -subitemconfig { {hdl_top.dut.u_progif.m_wready[9]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[8]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[7]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[6]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[5]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[4]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[3]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[2]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[1]} {-radix hexadecimal} {hdl_top.dut.u_progif.m_wready[0]} {-radix hexadecimal} }
wave group {hdl_top.axi_if.slave_if[0]} -backgroundcolor #004466
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].common_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].is_active} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].common_clock_mode} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].clock_enable} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].internal_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aresetn} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awvalid} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wlast} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bvalid} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].araddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arvalid} -tag sim -radix hexadecimal
wave expr -group {hdl_top.axi_if.slave_if[0]}  -alias ARADDR_transfers -radix hexadecimal {((hdl_top.axi_if.slave_if[0].arvalid & hdl_top.axi_if.slave_if[0].arready) & hdl_top.axi_if.slave_if[0].aclk)}
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rlast} -tag sim -radix hexadecimal
wave expr -group {hdl_top.axi_if.slave_if[0]}  -alias Read_Transfers -radix hexadecimal {(((hdl_top.axi_if.slave_if[0].rlast & hdl_top.axi_if.slave_if[0].rready) & hdl_top.axi_if.slave_if[0].rvalid) & hdl_top.axi_if.slave_if[0].aclk)}
wave spacer -group {hdl_top.axi_if.slave_if[0]} {}
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awdomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awcmo} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awunique} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awstashnid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awstashlpid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awstashnid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awstashlpid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awatop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awmpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awtagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].artagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].ardomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].artrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].armpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].araddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arctlchk3} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].ridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].ridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wtagupdate} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wstrbchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].breadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].brespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].btrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].btagmatch} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bcomp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].bpersist} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].arqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].ruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].buser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].awuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].wuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].buserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].aruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].ruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acwakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].actrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acctlchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acvmidextchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].acwakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].crrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cddata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cddatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].cdlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tdest} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tkeep} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].tuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].archunken} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rchunkv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rchunknum} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].rchunkstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].mon_snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].param_check_flag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_addr_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_data_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_id_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_max_tdest_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_max_tid_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_max_tuser_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_max_rchunknum_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].svt_axi_max_rchunkstrb_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[0]} {hdl_top.axi_if.slave_if[0].full_name} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {hdl_top.axi_if.slave_if[1]} -backgroundcolor #006666
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].common_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].is_active} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].common_clock_mode} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].clock_enable} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].internal_aclk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aresetn} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[1]} {}
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].araddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arready} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[1]} {}
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rlast} -tag sim -radix hexadecimal
wave spacer -group {hdl_top.axi_if.slave_if[1]} {}
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awdomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awcmo} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awunique} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awstashnid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awstashlpid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awstashnid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awstashlpid_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awatop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awmpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awtagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arlock[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arcache} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arnsaid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].artagop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].ardomain} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arbar} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].artrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armmusecsid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armmusid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armmussidv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armmussid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armmuatst} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].armpam} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].araddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arlenchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arctlchk0} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arctlchk1} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arctlchk2} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arctlchk3} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].ridunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].ridchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wdatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wtag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wtagupdate} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wstrbchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bloop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].breadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].brespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bidunq} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wack} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wackchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].btrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].btagmatch} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bcomp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].bpersist} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arregion} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].arqos} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].ruser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].buser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].awuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].wuserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].buserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].aruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].ruserchk[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acwakeup} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acsnoop} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acprot} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acvmidext} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].actrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acaddrchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acctlchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acvmidextchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].acwakeupchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].crrespchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cddata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cddatachk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdtrace} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdpoison[0]} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdreadychk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdvalidchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].cdlastchk} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tready} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tdest} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tkeep} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tid} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].tuser} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].archunken} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rchunkv} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rchunknum} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].rchunkstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_read_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_read_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_read_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_write_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_write_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_write_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_write_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_snoop_addr_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_snoop_data_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_snoop_data_xfer_id} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].mon_snoop_resp_xact_num} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].param_check_flag} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_addr_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_data_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_id_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_max_tdest_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_max_tid_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_max_tuser_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_max_rchunknum_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].svt_axi_max_rchunkstrb_width_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.axi_if.slave_if[1]} {hdl_top.axi_if.slave_if[1].full_name} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group hdl_top.dma_irq_if -backgroundcolor #004466
wave add -group hdl_top.dma_irq_if hdl_top.dma_irq_if.clk -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if hdl_top.dma_irq_if.irq -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if hdl_top.dut.o_int -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if {hdl_top.dut.g_chnl[0].u_chnl.o_int} -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if {hdl_top.dut.g_chnl[1].u_chnl.o_int} -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if {hdl_top.dut.g_chnl[2].u_chnl.o_int} -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if {hdl_top.dut.g_chnl[3].u_chnl.o_int} -tag sim -radix hexadecimal
wave add -group hdl_top.dma_irq_if hdl_top.dut_channel_irqs -tag sim -radix hexadecimal -expand -subitemconfig { {hdl_top.dut_channel_irqs[3]} {-radix hexadecimal} {hdl_top.dut_channel_irqs[2]} {-radix hexadecimal} {hdl_top.dut_channel_irqs[1]} {-radix hexadecimal} {hdl_top.dut_channel_irqs[0]} {-radix hexadecimal} }
wave add -group hdl_top.dma_irq_if {hdl_top.dut.g_chnl[0].u_chnl.reg2hw.ch_ctrl.interrupt_en} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {hdl_top.dut.g_chnl[0].u_chnl} -backgroundcolor #004466
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.NUM_PORTS} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_clk} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_rst_n} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_global_cfg} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_global_sts} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_csr_axi_aw} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_csr_axi_awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_csr_axi_ar} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_csr_axi_arready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_csr_axi_w} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_csr_axi_wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_csr_axi_r} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_csr_axi_rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_csr_axi_b} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_csr_axi_bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_cmd_axi_aw} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_cmd_axi_awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_cmd_axi_ar} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_cmd_axi_arready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_cmd_axi_w} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_cmd_axi_wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_cmd_axi_r} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_cmd_axi_rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_chnl_cmd_axi_b} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_chnl_cmd_axi_bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_src_xfer_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_src_xfer_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_src_xfer} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_src_resp_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_src_resp_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_src_resp} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_dst_xfer_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_dst_xfer_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_dst_xfer} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_dst_resp_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_dst_resp_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.i_dst_resp} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.o_sts} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.channel_desc} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.channel_en} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.src_busy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.dst_busy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.alloc_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.alloc_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.alloc_tid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.alloc} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.buf_data_req} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.buf_data_gnt} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.buf_data} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.reg2hw} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.hw2reg} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.desc_src} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.desc_dst} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.desc} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.en_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.en_hus} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.clr_val} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl} {hdl_top.dut.g_chnl[0].u_chnl.clr_hus} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} -backgroundcolor #006666
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.StageNum} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.clk_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.rst_ni} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_aw_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_ar_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_arready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_w_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_b_o} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_r_o} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi_rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg2hw} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.hw2reg} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.devmode_i} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.AW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.DW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.DBW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_re} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_rd_addr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_wr_addr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_be} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_rd_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_wr_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.wr_addrmiss} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.wr_err} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.rd_addrmiss} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.rd_err} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_rdata_next} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_busy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wvld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wrdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_waddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wresp_vld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wresp_rdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_wresp_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rvld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rrdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_raddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rresp_data} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rresp_vld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rresp_rdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.axi2reg_rresp_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_clear_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_clear_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_interrupt_en_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_interrupt_en_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_interrupt_clr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_interrupt_clr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_src_osr_lmt_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_src_osr_lmt_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_dst_osr_lmt_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_dst_osr_lmt_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_src_ms_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_src_ms_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_dst_ms_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_dst_ms_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_ll_ms_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_ll_ms_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_mmu_en_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_mmu_en_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transize_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transize_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_xtype_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_xtype_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ytype_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ytype_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_mode_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_mode_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_src_burstlen_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_src_burstlen_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_dst_burstlen_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_dst_burstlen_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ll_en_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ll_en_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ll_mode_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ll_mode_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transform_en_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transform_en_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_src_addr_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_src_addr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_src_addr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_dst_addr_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_dst_addr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_dst_addr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_src_xbytesize_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_src_xbytesize_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_dst_xbytesize_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_dst_xbytesize_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_src_yrowsize_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_src_yrowsize_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_dst_yrowsize_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_dst_yrowsize_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcmemattrlo_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcmemattrlo_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcmemattrhi_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcmemattrhi_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srchareattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srchareattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcnonsecattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcnonsecattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcprivattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcprivattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcuserfield_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_srcuserfield_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstmemattrlo_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstmemattrlo_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstmemattrhi_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstmemattrhi_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dsthareattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dsthareattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstnonsecattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstnonsecattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstprivattr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstprivattr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstuserfield_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_tran_cfg_dstuserfield_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_src_xaddrinc_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_src_xaddrinc_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_dst_xaddrinc_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_dst_xaddrinc_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_src_yaddrstride_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_src_yaddrstride_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_dst_yaddrstride_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_dst_yaddrstride_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_ll_last_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_ll_last_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_ll_mode_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_ll_mode_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_link_addr_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_link_descr_link_addr_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_status_re} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_status_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_re} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_slv_err_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_dec_err_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_cfg_err_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_ecc_err_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_ecc_err_type_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_err_info_ecc_err_mem_loc_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_req_bus_ctrl_we} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_req_bus_ctrl_qs} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_req_bus_ctrl_wd} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.rd_addr_hit} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.wr_addr_hit} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.shadow_busy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.reg_busy_sel} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.unused_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.unused_be} -tag sim -radix hexadecimal
wave insertion [expr [wave index insertpoint] + 1]
wave group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} -backgroundcolor #226600
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.IDW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.AW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.DW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.BW} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.NR_WR_REQS} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.NR_RD_REQS} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.WBUF} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.RD_RESP_DEPTH} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.WR_RESP_DEPTH} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.OSR} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.i_clk} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.i_rst_n} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awaddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.awready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.araddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arlen} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arsize} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arburst} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.arready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.wlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.wvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.wready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rlast} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.rready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bresp} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bvalid} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bready} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wvld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wrdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_waddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wdata} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wstrb} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wresp_vld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wresp_rdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_wresp_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rvld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rrdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_raddr} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rresp_vld} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rresp_rdy} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rresp_error} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.reg_rresp_data} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.blast_int} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bvalid_int} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg.bready_int} -tag sim -radix hexadecimal
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} hdl_top.dut.u_progif.u_csr.ch_status_ch0_busy_qs -tag sim -radix mnemonic
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} hdl_top.dut.u_progif.u_csr.ch_status_ch1_busy_qs -tag sim -radix mnemonic
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} hdl_top.dut.u_progif.u_csr.ch_status_ch2_busy_qs -tag sim -radix mnemonic
wave add -group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} hdl_top.dut.u_progif.u_csr.ch_status_ch3_busy_qs -tag sim -radix mnemonic
wave insertion [expr [wave index insertpoint] + 1]
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch0_busy_qs -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch1_busy_qs -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch2_busy_qs -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch3_busy_qs -tag sim -radix hexadecimal -select
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_qs} -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut.u_progif.u_csr.rd_addr_hit -tag sim -radix hexadecimal -expand -subitemconfig { {hdl_top.dut.u_progif.u_csr.rd_addr_hit[1]} {-radix hexadecimal} {hdl_top.dut.u_progif.u_csr.rd_addr_hit[0]} {-radix hexadecimal} }
wave add hdl_top.dut.u_progif.u_csr.reg_rdata -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.reg_rdata_next -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut.u_progif.u_csr.axi2reg_raddr -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rvld -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rrdy -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rresp_data -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rresp_vld -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rresp_rdy -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.axi2reg_rresp_error -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut.u_progif.u_csr.axi_r_o -tag sim -radix hexadecimal -expand -subitemconfig { hdl_top.dut.u_progif.u_csr.axi_r_o.id {-radix hexadecimal} hdl_top.dut.u_progif.u_csr.axi_r_o.data {-radix hexadecimal} hdl_top.dut.u_progif.u_csr.axi_r_o.resp {-radix hexadecimal} hdl_top.dut.u_progif.u_csr.axi_r_o.last {-radix hexadecimal} hdl_top.dut.u_progif.u_csr.axi_r_o.valid {-radix hexadecimal} }
wave spacer {}
wave add hdl_top.dut.u_progif.global_csr_axi_r -tag sim -radix hexadecimal -expand -subitemconfig { hdl_top.dut.u_progif.global_csr_axi_r.id {-radix hexadecimal} hdl_top.dut.u_progif.global_csr_axi_r.data {-radix hexadecimal} hdl_top.dut.u_progif.global_csr_axi_r.resp {-radix hexadecimal} hdl_top.dut.u_progif.global_csr_axi_r.last {-radix hexadecimal} hdl_top.dut.u_progif.global_csr_axi_r.valid {-radix hexadecimal} }
wave spacer {}
wave spacer {}
wave add hdl_top.dut.u_progif.m_rdata -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut.u_progif.o_axi_s_rdata -tag sim -radix hexadecimal
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch0_busy_qs -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_qs} -tag sim -radix hexadecimal
wave spacer {}
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_src_addr_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_dst_addr_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transize_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_xtype_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_src_xbytesize_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xbytesize_dst_xbytesize_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_src_xaddrinc_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_xaddrinc_dst_xaddrinc_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_ytype_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_src_yrowsize_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yrowsize_dst_yrowsize_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_src_yaddrstride_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_yaddrstride_dst_yaddrstride_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_src_burstlen_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_dst_burstlen_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_fillval_mode_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transform_en_qs} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_cfg_transize_qs} -tag sim -radix hexadecimal
wave spacer {}
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.o_int} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.i_int_en} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.event_sts_q} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.event_pulse} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.i_int_clr} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.completion} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.busy_q} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.busy_dly_q} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.en_q} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.en_d} -tag sim -radix hexadecimal
wave spacer {}
wave spacer {}
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.i_en} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.en_d} -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_ctrl.en_dly_q} -tag sim -radix hexadecimal
wave spacer {}
wave add hdl_top.dut.u_progif.u_csr.ch_status_ch0_busy_qs -tag sim -radix hexadecimal
wave add {hdl_top.dut.g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_qs} -tag sim -radix hexadecimal
wave spacer {}
wave group {hdl_top.dut.g_chnl[0].u_chnl.u_csr.i_axi_reg} -collapse
wave group {hdl_top.dut.g_chnl[0].u_chnl.u_csr} -collapse
wave group {hdl_top.dut.g_chnl[0].u_chnl} -collapse
wave group {hdl_top.axi_if.slave_if[1]} -collapse
wave group hdl_top.dut.u_progif -collapse
wave group hdl_top.dut.u_progif.u_axi_demux.i_wr_path.g_wr.i_wdata_sel_fifo -collapse
wave group hdl_top.dut.u_progif.u_axi_demux.i_rd_path -collapse
wave group hdl_top.dut.u_progif.u_axi_demux.i_wr_path -collapse
wave group hdl_top.dut.u_progif.u_axi_demux -collapse
wave group {DUT-Register AXI-IF} -collapse
wave group {hdl_top.axi_if.master_if[0]} -collapse
wave update on
wave top 402
wave filter settings -pattern * -leaf_name_only 1 -history {*} -signal_type 255 
