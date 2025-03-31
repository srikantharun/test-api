# TEMPORARY: Deactivate svt amba vip errors
#
# (vlog-7060) Virtual function svt_configuration::setup_pa_plusarg called from the constructor for class svt_uvm_pkg::svt_configuration.
# (vlog-7060) Virtual function svt_configuration::setup_cov_plusarg called from the constructor for class svt_uvm_pkg::svt_configuration.
# (vlog-7060) Virtual function svt_driver::get_suite_name called from the constructor for class svt_uvm_pkg::svt_driver.
# (vlog-7060) Virtual function svt_mem::get_aligned_addr called from the constructor for class svt_uvm_pkg::svt_mem.
# (vlog-7060) Virtual function svt_mem::clear called from the constructor for class svt_uvm_pkg::svt_mem.
# (vlog-2147) Expressions in 'bins' size, value or transition specification must be constant or covergroup constructor argument.
# (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
# (vlog-2577) Enum type mismatch between operands of '=='/'!='/'<'/'>'/... expression.
# (vlog-2240) Treating stand-alone use of function 'last' as an implicit VOID cast
# (vlog-2931) Invalid argument #1 for randomize() function.
# (vlog-2961) Argument #1 for std::randomize() function is non-LRM compliant.
VSIM_VLOG_OPTS_EXT += -suppress 7060,2147,13262,2577,2897,7070,2240,2931,2961

# vopt-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
VSIM_VOPT_OPTS_EXT += -suppress 3838

# (vsim-8451) Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
# vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
VSIM_ELAB_OPTS_EXT += -suppress 8451,3838

# Specify the debug access (necessary to read via backdoor):
VSIM_VOPT_OPTS_EXT += -access=rw+/.
