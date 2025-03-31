## TEMPORARY: Deactivate svt amba vip errors

# (vlog-2577) Enum type mismatch between operands of '!=' expression.
# (vlog-2897) Using non-standard foreach loop variable list syntax.
# (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
# (vlog-2147) Expressions in 'bins' size, value or transition specification must be constant or covergroup constructor argument.
# (vlog-7034) Array assignment or comparison to type 'bit[7:0] $[]' from type 'reg[7:0] $[]':  Arg. 'packed_data' of 'pack_data_to_byte_stream':  Elements must both be 2-state or both be 4-state.
# (vlog-2897) Using non-standard foreach loop variable list syntax
override VSIM_VLOG_OPTS_EXT += -suppress 2577,2897,13262,2147,7034,2897

# TODO vopt-3838: Variable 'awsize[3]/arsize[3]' written by continuous and procedural assignments.
VSIM_VOPT_OPTS_EXT += -suppress 3838

# TODO Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.

VSIM_VLOG_OPTS += +nospecify
#TODO(vsim-8451)Virtual interface resolution cannot find a matching instance for 'virtual svt_apb_if.svt_apb_monitor_modport'.
#TODO vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
#TODO vsim-3839: driven via a port connection, is multiply driven.
#TODO vsim-8760: (vsim-PLI-8760) $sformatf : Argument number 1 has an invalid format width
#TODO(vsim-PLI-3069) <protected> : Argument number <protected> is invalid.
#TODO(vsim-8754) Actual output arg. of type 'bit[7:0]$[]' for formal '<protected>' of '<protected>' is not compatible with the formal's type 'reg[7:0]$[]'.
#    Time: 0 ps  Iteration: 0  Region: /svt_axi_uvm_pkg::svt_axi4_ordering_write_overlap_addr_same_id_normal_memory_ictest_sequence File: /opt/synopsys/dware/eu001-1.0/vip/svt/amba_s#vt/S-2021.12/axi_system_env_svt/sverilog/src/mti/svt_axi_3_4_interconnect_ts_ordering_sequence_collection.svp Line: 1682
VSIM_ELAB_OPTS_EXT += -suppress 3838,3839,8451,8760,3069,8754,7034

VSIM_VOPT_OPTS += -cellaccessfullread
VSIM_VOPT_OPTS += -cellaccess=rw+/.
