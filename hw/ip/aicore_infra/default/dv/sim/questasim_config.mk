## TEMPORARY: Deactivate svt amba vip errors

# (vlog-2577) Enum type mismatch between operands of '!=' expression.
# (vlog-2897) Using non-standard foreach loop variable list syntax.
# (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
# (vlog-2147) Expressions in 'bins' size, value or transition specification must be constant or covergroup constructor argument.
VSIM_VLOG_OPTS_EXT += -suppress 2577,2897,13262,2147

# TODO vopt-3838: Variable 'awsize[3]/arsize[3]' written by continuous and procedural assignments.
VSIM_VOPT_OPTS_EXT += -suppress 3838

# TODO Workaround for: Questa has encountered an unexpected internal error: ../../src/vlog/vgenexpr.c(21493).
VSIM_VOPT_OPTS_EXT += -access=rw+/.

#TODO(vsim-8451)Virtual interface resolution cannot find a matching instance for 'virtual svt_apb_if.svt_apb_monitor_modport'.
#TODO vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
#TODO vsim-3839: driven via a port connection, is multiply driven. 
#TODO vsim-8760: (vsim-PLI-8760) $sformatf : Argument number 1 has an invalid format width 
#(vsim-PLI-3069) <protected> : Argument number <protected> is invalid.
VSIM_ELAB_OPTS_EXT += -suppress 3838
VSIM_ELAB_OPTS_EXT += -suppress 3839
VSIM_ELAB_OPTS_EXT += -suppress 8451
VSIM_ELAB_OPTS_EXT += -suppress 8760
VSIM_ELAB_OPTS_EXT += -suppress 3069
