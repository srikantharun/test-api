# Deactivate svt amba vip errors
#
# (vlog-7060) Virtual function svt_configuration::setup_pa_plusarg called from the constructor for class svt_uvm_pkg::svt_configuration.
# (vlog-7060) Virtual function svt_configuration::setup_cov_plusarg called from the constructor for class svt_uvm_pkg::svt_configuration.
# (vlog-7060) Virtual function svt_driver::get_suite_name called from the constructor for class svt_uvm_pkg::svt_driver.
# (vlog-7060) Virtual function svt_mem::get_aligned_addr called from the constructor for class svt_uvm_pkg::svt_mem.
# (vlog-7060) Virtual function svt_mem::clear called from the constructor for class svt_uvm_pkg::svt_mem.
# (vlog-2147) Expressions in 'bins' size, value or transition specification must be constant or covergroup constructor argument.
# (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
# (vlog-2577) Enum type mismatch between operands of '=='/'!='/'<'/'>'/... expression.
# (vlog-2125) Associative array string index must be a string variable or literal.
# (vlog-2899) A compiler directive was found where only an identifier is allowed.
VSIM_VLOG_OPTS_EXT += -suppress 7060,2147,13262,2577,2125,2899

# (vsim-8451) Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
VSIM_ELAB_OPTS_EXT += -suppress 8451 +nospecify
# Turn off uvm recording
VSIM_ELAB_OPTS_EXT += -uvmcontrol=none

# Coverage config
VSIM_VOPT_OPTS_COVERAGE = +cover=t+spike_top_tb/th/u_soc_periph_p+3 -access=rw+/.
VSIM_COVERAGE_MERGE_INPUT_FILES = $(REPO_ROOT)/hw/impl/europa/blocks/soc_periph/dv/spike_tb/sim/build_sw/*/coverage.ucdb
