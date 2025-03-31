set BS_CLK_PER          				[expr {1000.0*1/($BS_CLK_FREQ * $FREQ_MARGIN)}]

set JTAG_CLK_PER        				[expr {1000.0*1/($JTAG_CLK_FREQ * $FREQ_MARGIN)}]


# PHY input delays (not including scan inputs)
for {set phy 0} {$phy < $nphys} {incr phy} {

 set_input_delay  -add_delay -max [expr {0.50 * $ref_clk_period}]    [get_ports bisr_shift_en]   -clock bisr_clk
 set_input_delay  -add_delay -max [expr {0.50 * $ref_clk_period}]    [get_ports bisr_si]         -clock bisr_clk
 set_input_delay  -add_delay -min [expr {0.00 * $ref_clk_period}]    [get_ports bisr_shift_en]   -clock bisr_clk
 set_input_delay  -add_delay -min [expr {0.00 * $ref_clk_period}]    [get_ports bisr_si]         -clock bisr_clk

 set_input_delay  -add_delay -max [expr {0.50 * $JTAG_CLK_PER}]  [get_ports tdi]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk
 set_input_delay  -add_delay -max [expr {0.50 * $JTAG_CLK_PER}]  [get_ports tms]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk
 set_input_delay  -add_delay -min [expr {0.00 * $JTAG_CLK_PER}]  [get_ports tdi]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk
 set_input_delay  -add_delay -min [expr {0.00 * $JTAG_CLK_PER}]  [get_ports tms]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk
 set_output_delay -add_delay -max [expr {0.50 * $ref_clk_period}]    [get_ports bisr_so]         -clock bisr_clk
 set_output_delay -add_delay -min [expr {0.00 * $ref_clk_period}]    [get_ports bisr_so]         -clock bisr_clk

 set_output_delay -add_delay -max [expr {0.50 * $JTAG_CLK_PER}]  [get_ports tdo]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk -clock_fall
 set_output_delay -add_delay -max [expr {0.50 * $JTAG_CLK_PER}]  [get_ports tdo_en]          -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk -clock_fall
 set_output_delay -add_delay -min [expr {0.00 * $JTAG_CLK_PER}]  [get_ports tdo]             -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk -clock_fall
 set_output_delay -add_delay -min [expr {0.00 * $JTAG_CLK_PER}]  [get_ports tdo_en]          -clock ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk -clock_fall
}


###################################
#i_ref_clk related input ports
set aoapb_iports [list \
    i_pcie_targ_cfg_apb_paddr \
    i_pcie_targ_cfg_apb_pwdata \
    i_pcie_targ_cfg_apb_pwrite \
    i_pcie_targ_cfg_apb_psel \
    i_pcie_targ_cfg_apb_penable \
    i_pcie_targ_cfg_apb_pstrb \
]

#apb_pclk related input ports
set apbslv_iports [list \
    i_pcie_targ_syscfg_apb_paddr \
    i_pcie_targ_syscfg_apb_pwdata \
    i_pcie_targ_syscfg_apb_pwrite \
    i_pcie_targ_syscfg_apb_psel \
    i_pcie_targ_syscfg_apb_penable \
    i_pcie_targ_syscfg_apb_pstrb \
    i_pcie_targ_syscfg_apb_pprot \
]

set mstr_aclk_iports [list \
    i_pcie_init_mt_axi_awready \
    i_pcie_init_mt_axi_wready \
    i_pcie_init_mt_axi_bvalid \
    i_pcie_init_mt_axi_bid \
    i_pcie_init_mt_axi_bresp \
    i_pcie_init_mt_axi_arready \
    i_pcie_init_mt_axi_rvalid \
    i_pcie_init_mt_axi_rid \
    i_pcie_init_mt_axi_rdata \
    i_pcie_init_mt_axi_rresp \
    i_pcie_init_mt_axi_rlast \
]

set slv_aclk_iports [list \
    i_pcie_targ_mt_axi_awvalid \
    i_pcie_targ_mt_axi_awid \
    i_pcie_targ_mt_axi_awaddr \
    i_pcie_targ_mt_axi_awlen \
    i_pcie_targ_mt_axi_awsize \
    i_pcie_targ_mt_axi_awburst \
    i_pcie_targ_mt_axi_awlock \
    i_pcie_targ_mt_axi_awcache \
    i_pcie_targ_mt_axi_awprot \
    i_pcie_targ_mt_axi_awqos \
    i_pcie_targ_mt_axi_wvalid \
    i_pcie_targ_mt_axi_wdata \
    i_pcie_targ_mt_axi_wstrb \
    i_pcie_targ_mt_axi_wlast \
    i_pcie_targ_mt_axi_bready \
    i_pcie_targ_mt_axi_arvalid \
    i_pcie_targ_mt_axi_arid \
    i_pcie_targ_mt_axi_araddr \
    i_pcie_targ_mt_axi_arlen \
    i_pcie_targ_mt_axi_arsize \
    i_pcie_targ_mt_axi_arburst \
    i_pcie_targ_mt_axi_arlock \
    i_pcie_targ_mt_axi_arcache \
    i_pcie_targ_mt_axi_arprot \
    i_pcie_targ_mt_axi_arqos \
    i_pcie_targ_mt_axi_rready \
]

set dbi_aclk_iports [list \
    i_pcie_targ_cfg_dbi_axi_awvalid \
    i_pcie_targ_cfg_dbi_axi_awid \
    i_pcie_targ_cfg_dbi_axi_awaddr \
    i_pcie_targ_cfg_dbi_axi_awlen \
    i_pcie_targ_cfg_dbi_axi_awsize \
    i_pcie_targ_cfg_dbi_axi_awburst \
    i_pcie_targ_cfg_dbi_axi_awlock \
    i_pcie_targ_cfg_dbi_axi_awcache \
    i_pcie_targ_cfg_dbi_axi_awprot \
    i_pcie_targ_cfg_dbi_axi_awqos \
    i_pcie_targ_cfg_dbi_axi_wvalid \
    i_pcie_targ_cfg_dbi_axi_wdata \
    i_pcie_targ_cfg_dbi_axi_wstrb \
    i_pcie_targ_cfg_dbi_axi_wlast \
    i_pcie_targ_cfg_dbi_axi_bready \
    i_pcie_targ_cfg_dbi_axi_arvalid \
    i_pcie_targ_cfg_dbi_axi_arid \
    i_pcie_targ_cfg_dbi_axi_araddr \
    i_pcie_targ_cfg_dbi_axi_arlen \
    i_pcie_targ_cfg_dbi_axi_arsize \
    i_pcie_targ_cfg_dbi_axi_arburst \
    i_pcie_targ_cfg_dbi_axi_arlock \
    i_pcie_targ_cfg_dbi_axi_arcache \
    i_pcie_targ_cfg_dbi_axi_arprot \
    i_pcie_targ_cfg_dbi_axi_arqos \
    i_pcie_targ_cfg_dbi_axi_rready \
]

set clk_reset_misc_iports [list \
    i_ref_clk \
    i_ao_rst_n \
    i_global_rst_n \
    i_noc_async_idle_init_mt_axi_ack \
    i_noc_async_idle_targ_mt_axi_ack \
    i_noc_async_idle_targ_cfg_dbi_axi_ack \
    i_noc_async_idle_targ_cfg_apb_ack \
    i_noc_async_idle_init_mt_axi_val \
    i_noc_async_idle_targ_mt_axi_val \
    i_noc_async_idle_targ_cfg_dbi_axi_val \
    i_noc_async_idle_targ_cfg_apb_val \
    i_pcie_aux_clk \
    i_pcie_init_mt_axi_clk \
    i_pcie_targ_mt_axi_clk \
    i_pcie_targ_cfg_dbi_axi_clk \
    i_apb_pclk \
    tck \
    trst \
    tms \
    tdi \
    ssn_bus_clk \
    ssn_bus_data_in \
    bisr_clk \
    bisr_reset \
    bisr_shift_en \
    bisr_si \
]

set async_clk_virt_iports_rst [list \
    i_ao_rst_n \
    i_global_rst_n \
]

set_input_delay -add_delay  -max $ref_clk_idy_s  [get_ports $aoapb_iports]  -clock [get_clocks ref_clk_virt]
set_input_delay -add_delay  -min $ref_clk_idy_h  [get_ports $aoapb_iports]  -clock [get_clocks ref_clk_virt]

set_input_delay -add_delay  -max $apb_pclk_idy_s  [get_ports $apbslv_iports]  -clock [get_clocks apb_pclk_virt]
set_input_delay -add_delay  -min $apb_pclk_idy_h  [get_ports $apbslv_iports]  -clock [get_clocks apb_pclk_virt]

#relax input delay for these feedthrouth input ports to avoid infeasible_paths
remove_input_delay -max                       [get_ports i_pcie_targ_cfg_apb_psel]  -clock [get_clocks apb_pclk_virt]
set_input_delay    -max 0.60                  [get_ports i_pcie_targ_cfg_apb_psel]  -clock [get_clocks apb_pclk_virt]

set_input_delay -add_delay  -max $mstr_aclk_idy_s  [get_ports $mstr_aclk_iports]  -clock [get_clocks mstr_aclk_virt]
set_input_delay -add_delay  -min $mstr_aclk_idy_h  [get_ports $mstr_aclk_iports]  -clock [get_clocks mstr_aclk_virt]

set_input_delay -add_delay  -max $slv_aclk_idy_s  [get_ports $slv_aclk_iports]  -clock [get_clocks slv_aclk_virt]
set_input_delay -add_delay  -min $slv_aclk_idy_h  [get_ports $slv_aclk_iports]  -clock [get_clocks slv_aclk_virt]

set_input_delay -add_delay  -max $dbi_aclk_idy_s  [get_ports $dbi_aclk_iports]  -clock [get_clocks dbi_aclk_virt]
set_input_delay -add_delay  -min $dbi_aclk_idy_h  [get_ports $dbi_aclk_iports]  -clock [get_clocks dbi_aclk_virt]

#relax input delay(1.13) for some axi signals
remove_input_delay -max                  [get_ports i_pcie_init_mt_axi_awready]             -clock [get_clocks mstr_aclk_virt]
set_input_delay    -max 0.90             [get_ports i_pcie_init_mt_axi_awready]  -add_delay -clock [get_clocks mstr_aclk_virt]

remove_input_delay -max                  [get_ports i_pcie_targ_mt_axi_bready]                   -clock [get_clocks slv_aclk_virt]
set_input_delay    -max 0.50             [get_ports i_pcie_targ_mt_axi_bready]      -add_delay   -clock [get_clocks slv_aclk_virt]

set_input_delay  -max 1.5   [get_ports $async_clk_virt_iports_rst]  -add_delay -clock [get_clocks async_clk_virt]
set_input_delay  -min 0     [get_ports $async_clk_virt_iports_rst]  -add_delay -clock [get_clocks async_clk_virt]
# Assume the following drive cells for input ports.
# set_driving_cell
set i_ports [concat \
    $aoapb_iports \
    $apbslv_iports \
    $mstr_aclk_iports \
    $slv_aclk_iports \
    $dbi_aclk_iports \
    $async_clk_virt_iports_rst \
    $clk_reset_misc_iports \
]

foreach iport $i_ports {
    set_driving_cell [get_ports $iport]  -lib_cell DFFRPQRLV_D2_N_S6TR_C54L08 -pin Q -no_design_rule
}

#########################################
#i_ref_clk related output ports
set aoapb_oports [list \
    o_pcie_targ_syscfg_apb_pready \
    o_pcie_targ_syscfg_apb_prdata \
    o_pcie_targ_syscfg_apb_pslverr \
]

# apb_pclk related output ports
set apbslv_oports [list \
    o_pcie_targ_cfg_apb_pready \
    o_pcie_targ_cfg_apb_prdata \
    o_pcie_targ_cfg_apb_pslverr \
]

set mstr_aclk_oports [list \
    o_pcie_init_mt_axi_awvalid \
    o_pcie_init_mt_axi_awid \
    o_pcie_init_mt_axi_awaddr \
    o_pcie_init_mt_axi_awlen \
    o_pcie_init_mt_axi_awsize \
    o_pcie_init_mt_axi_awburst \
    o_pcie_init_mt_axi_awlock \
    o_pcie_init_mt_axi_awcache \
    o_pcie_init_mt_axi_awqos \
    o_pcie_init_mt_axi_wvalid \
    o_pcie_init_mt_axi_wdata \
    o_pcie_init_mt_axi_wstrb \
    o_pcie_init_mt_axi_wlast \
    o_pcie_init_mt_axi_bready \
    o_pcie_init_mt_axi_arvalid \
    o_pcie_init_mt_axi_arid \
    o_pcie_init_mt_axi_araddr \
    o_pcie_init_mt_axi_arlen \
    o_pcie_init_mt_axi_arsize \
    o_pcie_init_mt_axi_arburst \
    o_pcie_init_mt_axi_arlock \
    o_pcie_init_mt_axi_arcache \
    o_pcie_init_mt_axi_arqos \
    o_pcie_init_mt_axi_rready \
]

set slv_aclk_oports [list \
    o_pcie_targ_mt_axi_awready \
    o_pcie_targ_mt_axi_wready \
    o_pcie_targ_mt_axi_bvalid \
    o_pcie_targ_mt_axi_bid \
    o_pcie_targ_mt_axi_bresp \
    o_pcie_targ_mt_axi_arready \
    o_pcie_targ_mt_axi_rvalid \
    o_pcie_targ_mt_axi_rid \
    o_pcie_targ_mt_axi_rdata \
    o_pcie_targ_mt_axi_rresp \
    o_pcie_targ_mt_axi_rlast \
]

set dbi_aclk_oports [list \
    o_pcie_targ_cfg_dbi_axi_awready \
    o_pcie_targ_cfg_dbi_axi_wready \
    o_pcie_targ_cfg_dbi_axi_bvalid \
    o_pcie_targ_cfg_dbi_axi_bid \
    o_pcie_targ_cfg_dbi_axi_bresp \
    o_pcie_targ_cfg_dbi_axi_arready \
    o_pcie_targ_cfg_dbi_axi_rvalid \
    o_pcie_targ_cfg_dbi_axi_rid \
    o_pcie_targ_cfg_dbi_axi_rdata \
    o_pcie_targ_cfg_dbi_axi_rresp \
    o_pcie_targ_cfg_dbi_axi_rlast \
]

set core_clk_oports [list \
    o_pcie_int \
]

# other output ports
set clk_reset_misc_oports [list \
    o_noc_async_idle_init_mt_axi_req \
    o_noc_async_idle_targ_mt_axi_req \
    o_noc_async_idle_targ_cfg_dbi_axi_req \
    o_noc_async_idle_targ_cfg_apb_req \
    o_noc_init_mt_axi_clken \
    o_noc_targ_mt_axi_clken \
    o_noc_targ_cfg_dbi_axi_clken \
    o_noc_targ_cfg_apb_clken \
    o_noc_rst_n \
    io_pcie_resref \
    o_pcie_init_mt_axi_rst_n \
    o_pcie_targ_mt_axi_rst_n \
    o_pcie_targ_cfg_dbi_axi_rst_n \
    o_pcie_init_mt_axi_awprot \
    o_pcie_init_mt_axi_arprot \
]

set_output_delay -add_delay  -max $ref_clk_ody_s  [get_ports $aoapb_oports]  -clock [get_clocks ref_clk_virt]
set_output_delay -add_delay  -min $ref_clk_ody_h  [get_ports $aoapb_oports]  -clock [get_clocks ref_clk_virt]

set_output_delay -add_delay  -max $apb_pclk_ody_s  [get_ports $apbslv_oports]  -clock [get_clocks apb_pclk_virt]
set_output_delay -add_delay  -min $apb_pclk_ody_h  [get_ports $apbslv_oports]  -clock [get_clocks apb_pclk_virt]

set_output_delay -add_delay  -max $mstr_aclk_ody_s [get_ports $mstr_aclk_oports]  -clock [get_clocks mstr_aclk_virt]
set_output_delay -add_delay  -min $mstr_aclk_ody_h [get_ports $mstr_aclk_oports]  -clock [get_clocks mstr_aclk_virt]

set_output_delay -add_delay  -max $slv_aclk_ody_s [get_ports $slv_aclk_oports]  -clock [get_clocks slv_aclk_virt]
set_output_delay -add_delay  -min $slv_aclk_ody_h [get_ports $slv_aclk_oports]  -clock [get_clocks slv_aclk_virt]

set_output_delay -add_delay  -max $dbi_aclk_ody_s [get_ports $dbi_aclk_oports]  -clock [get_clocks dbi_aclk_virt]
set_output_delay -add_delay  -min $dbi_aclk_ody_h [get_ports $dbi_aclk_oports]  -clock [get_clocks dbi_aclk_virt]

set_output_delay -add_delay  -max $core_clk_ody_s  [get_ports $core_clk_oports]  -clock [get_clocks core_clk_virt]
set_output_delay -add_delay  -min $core_clk_ody_h  [get_ports $core_clk_oports]  -clock [get_clocks core_clk_virt]

#relax slv_awready for feedthrough path
remove_output_delay -max                  [get_ports o_pcie_targ_mt_axi_awready]             -clock [get_clocks slv_aclk_virt]
set_output_delay    -max 1.0              [get_ports o_pcie_targ_mt_axi_awready]  -add_delay -clock [get_clocks slv_aclk_virt]

# set_load and set_port_fanout_number
set o_ports [concat \
    $aoapb_oports \
    $apbslv_oports \
    $mstr_aclk_oports \
    $slv_aclk_oports \
    $dbi_aclk_oports \
    $core_clk_oports \
    $clk_reset_misc_oports \
]

#set load_val            [expr {3* [load_of ln05lpe_sc_s6t_flk_rvt_c54l08/DFFRPQRLV_D2_N_S6TR_C54L08/D]}]
set load_val            0.001078275

set fanout_num          3

foreach oport $o_ports {
    set_load -pin_load $load_val        [get_ports $oport]
    set_port_fanout_number $fanout_num  [get_ports $oport]
}

set_case_analysis 0 [get_pins -hierarchical */MCS[1]]
set_case_analysis 1 [get_pins -hierarchical */MCS[0]]
set_case_analysis 0 [get_pins -hierarchical */MCSW]
set_case_analysis 0 [get_pins -hierarchical */MCSWR[1]]
set_case_analysis 0 [get_pins -hierarchical */MCSRD[1]]
set_case_analysis 1 [get_pins -hierarchical */MCSWR[0]]
set_case_analysis 1 [get_pins -hierarchical */MCSRD[0]]
#this needs to be re-written
#set_case_analysis 0 [get_pins -hierarchical */SE]
set_case_analysis 0 [get_pins -hierarchical */PDE]
set_case_analysis 0 [get_pins -hierarchical */RET]
set_case_analysis 1 [get_pins -hierarchical */ADME[2]]
set_case_analysis 0 [get_pins -hierarchical */ADME[1]]
set_case_analysis 0 [get_pins -hierarchical */ADME[0]]
