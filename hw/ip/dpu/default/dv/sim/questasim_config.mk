#Supressible errors
# ** at /home/projects/lowrisc_opentitan_repo/dv_utils/dv_report_catcher.sv(19): (vlog-2897) Using non-standard foreach loop variable list syntax.
# ** Error (suppressible): /home/projects/lowrisc_opentitan_repo/dv_base_reg/csr_excl_item.sv(139): (vlog-2577) Enum type mismatch between operands of '!=' expression.
# ** at /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_gpio_driver_common.svp(113): (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
# ** at /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_err_check_stats_cov.svp(286): (vlog-2147) Expressions in 'bins' size, value or transition specification must
VSIM_VLOG_OPTS_EXT += -suppress 2897,2577,13262,2147,2388,13311,13272,13335,2542

# ** Error (suppressible): //home/projects/europa_vip/amba_system_env_svt/include/sverilog/svt_axi_master_if.svi(436): (vopt-3838) Variable 'tready' written by continuous and procedural assignments. 
# ** Error (suppressible): /home/projects/workspace/yokota/europa/hw/ip/iau/default/dv/rtl/hdl_top.sv(101): (vopt-7063) Failed to find 'genblk5' in hierarchical name 'dut.i_iau_cmd_gen.i_cmd_prg_mem.genblk5.genblk2[i].i_row.d_q'.
VSIM_VOPT_OPTS_EXT += -suppress 3838,7063

# ** Error (suppressible): (vsim-3838) Variable '/hdl_top/axi_if/master_if[1]/tready' written by continuous and procedural assignments. 
# ** Error (suppressible): (vsim-8451) /opt/synopsys/dware/eu001-1.0/vip/svt/common/T-2022.03/sverilog/src/mti/svt_gpio_driver_common.svp(113): Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
# ** Error (suppressible): (vsim-PLI-8760) $sformatf : Argument number 1 has an invalid format width.
#    Time: 0 ps  Iteration: 0  Region: /iau_seq_pkg::iau_cmd_descriptor_sequence::print_log File: /home/projects/workspace/yokota/europa/hw/ip/iau/default/dv/uvm/sequences/iau_cmd_descriptor_sequence.sv Line: 123
# ** Error (suppressible): (vsim-3839) Variable '/hdl_top/axi_if/master_if[0]/awready', driven via a port connection, is multiply driven. See /home/projects/workspace/yokota/europa/hw/ip/iau/default/dv/rtl/./dut_connections.svh(1).
VSIM_ELAB_OPTS_EXT += -suppress 3838,8451,8760,3839



#Waiting more cycles because in the parameter it only waits for 16 cycles
VSIM_VOPT_OPTS_EXT += -G dut/AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER/AWREADY_MAXWAITS=1000
VSIM_VOPT_OPTS_EXT += -G dut/AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER/ARREADY_MAXWAITS=1000
VSIM_VOPT_OPTS_EXT += -G dut/AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER/WREADY_MAXWAITS=1000
VSIM_VOPT_OPTS_EXT += -G dut/AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER/BREADY_MAXWAITS=1000
VSIM_VOPT_OPTS_EXT += -G dut/AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER/RREADY_MAXWAITS=1000

