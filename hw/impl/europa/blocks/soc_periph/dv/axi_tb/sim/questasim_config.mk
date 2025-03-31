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
VSIM_VLOG_OPTS_EXT += -suppress 7060,2147,13262,2577

# vopt-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
VSIM_VOPT_OPTS_EXT += -suppress 3838

# (vsim-8451) Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
# vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
VSIM_ELAB_OPTS_EXT += -suppress 8451,3838 +nospecify

# Deactivate transaction recording
VSIM_ELAB_OPTS_EXT += -uvmcontrol=none

# Coverage config
VSIM_VOPT_OPTS_COVERAGE = +cover=t+axi_stress_top_tb/th/u_soc_periph_p+3 -access=rw+/.
VSIM_COVERAGE_MERGE_INPUT_FILES = $(REPO_ROOT)/hw/impl/europa/blocks/soc_periph/dv/axi_tb/sim/build_vsim_*/run_vsim_*/coverage.ucdb
