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
VSIM_VLOG_OPTS_EXT += -suppress 7060,2147,13262,2577,13305

# vopt-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
# 2986, spm_config localparam is not considered const, this is fine because it will be not be modified during the test
VSIM_VOPT_OPTS_EXT += -suppress 3838,7063,2986


# (vsim-8451) Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
# vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
# (vsim-PLI-3069) <protected> : Argument number <protected> is invalid.
VSIM_ELAB_OPTS_EXT += -suppress 8451,3838,3069



# UVM configuration defines
VSIM_VLOG_OPTS ?= +define+UVM_NO_DPI
VSIM_VLOG_OPTS += +define+UVM_NO_DEPRECATED
VSIM_VLOG_OPTS += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
VSIM_VLOG_OPTS += +define+UVM_DEPRECATED_STARTING_PHASE

# AXI VIP configuration defines
VSIM_VLOG_OPTS += +define+AXI_VIP
VSIM_VLOG_OPTS += +define+SYNOPSYS_SV

VSIM_VLOG_OPTS += +nospecify
# gives acces to hdl_force on the axi4pc reset
VSIM_VOPT_OPTS += -access=w+/hdl_top/i_spm_dut/spm_ip_axi_protocol_checker/.

# SVT configuration defines
VSIM_VLOG_OPTS += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
VSIM_VLOG_OPTS += +define+SVT_UVM_TECHNOLOGY
VSIM_VLOG_OPTS += +define+SVT_UVM_12_OR_HIGHER
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_ADDR_WIDTH=40
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_DATA_WIDTH=64
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_ID_WIDTH=9
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_RREADY_DELAY=1024
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_WRITE_RESP_DELAY=1024
VSIM_VLOG_OPTS += +define+SVT_AXI_ACE_SNPS_INTERNAL_SYSTEM_MONITOR_USE_MASTER_SLAVE_AGENT_CONNECTION
VSIM_VLOG_OPTS += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=262144
VSIM_VLOG_OPTS += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_MESSAGING
VSIM_VLOG_OPTS += +define+SVT_AMBA_DATA_UTIL_ENABLE_INTERNAL_DATA_MESSAGING
VSIM_VLOG_OPTS += +define+SVT_MEM_ENABLE_INTERNAL_MESSAGING
VSIM_ELAB_OPTS_EXT += -uvmcontrol=none

.PHONY: add_hdl_backdoor
add_hdl_backdoor:
	python3 $(MAKEFILE_DIR)/../dv/tb/add_hdl_backdoor.py

COMPILE_VSIM_PREREQUISITES += add_hdl_backdoor
CLEAN_PREREQUISITES += $(MAKEFILE_DIR)/../dv/tb/generated
REGRESS_VERIFSDK_PLATFORM=uvm.HW_IP_SPM_DEFAULT_DV_SIM
