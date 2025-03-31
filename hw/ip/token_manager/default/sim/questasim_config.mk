# vopt-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
VSIM_VOPT_OPTS_EXT += -suppress 3838,7063

# (vsim-8451) Virtual interface resolution cannot find a matching instance for 'virtual svt_gpio_if'.
# vsim-3838: Variable 'rvalid'/'bvalid' written by continuous and procedural assignments. (triggered by the VIPs being connected together)
# (vsim-PLI-3069) <protected> : Argument number <protected> is invalid.
VSIM_ELAB_OPTS_EXT += -suppress 8451,3838,3069

VSIM_VLOG_OPTS_EXT += -suppress 13262,2897



# UVM configuration defines
VSIM_VLOG_OPTS ?= +define+UVM_NO_DPI
VSIM_VLOG_OPTS += +define+UVM_NO_DEPRECATED
VSIM_VLOG_OPTS += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
VSIM_VLOG_OPTS += +define+UVM_DEPRECATED_STARTING_PHASE

# AXI VIP configuration defines
VSIM_VLOG_OPTS += +define+AXI_VIP
VSIM_VLOG_OPTS += +define+SYNOPSYS_SV

VSIM_VLOG_OPTS += +nospecify

VSIM_ELAB_OPTS_EXT += -uvmcontrol=none

REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_TKN_MNG_DEFAULT_DV_SIM
