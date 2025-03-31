#############################################
# Add VSIM Run and Elab options for cva6v
#############################################

VSIM_VOPT_OPTS_EXT += -access=rw+/. # needed by uvm_hdl_deposit/read
VSIM_VLOG_OPTS_EXT += -suppress 2121,2244,2696,2697,2986
VSIM_VLOG_OPTS_EXT += -suppress 2147,2577,3838,7034,7060,13262 # SVT VIP related
VSIM_ELAB_OPTS_EXT += -suppress 7034,8754,8760
VSIM_ELAB_OPTS_EXT += -suppress 3838,8451 # SVT VIP related

# Suppress errors in PCIE CTRL IP (non-fixable but suppresable):
# Enum type mismatch between operands of '==' expression.
VSIM_VLOG_OPTS_EXT += -suppress 2577
# An enum variable 'x' of type 'y' may only be assigned the same enum typed variable or one of its values.
VSIM_VLOG_OPTS_EXT += -suppress 8386
# Variable 'x' driven in an combinational block, may not be driven by any other process.
VSIM_VOPT_OPTS_EXT += -suppress 7033
# Variable 'x' driven in an always_ff block, may not be driven by any other process.
VSIM_VOPT_OPTS_EXT += -suppress 7061
# Suppress errors in PCIE PHY IP (non-fixable but suppresable):
# Illegal space between ` and compiler directive or macro name.
VSIM_VLOG_OPTS_EXT += -suppress 13483

VSIM_VOPT_OPTS_COVERAGE = +cover=t+sim_top/i_hdl_top/i_europa \
                          +cover=t+sim_top/i_hdl_top/i_europa/u_europa_io \
                          +cover=t+sim_top/i_hdl_top/i_europa/u_aipu+2 \
                          +cover=t+sim_top/i_hdl_top/i_europa/u_aipu/u_soc_periph_p+2 \
                          +cover=t+sim_top/i_hdl_top/i_europa/u_aipu/u_soc_periph_p/u_soc_periph/u_peripherals \
                          -toggleportsonly -access=rw+/. -inlineFactor=0
VSIM_COVERAGE_MERGE_INPUT_FILES = $(REPO_ROOT)/hw/impl/europa/dv/$(TOP_PLATFORM_NAME)/build_sw/*/coverage.ucdb

#########################################
# Decoder warnings
#########################################

# Remove this warning at t0
# ** Warning: There is an 'U'|'X'|'W'|'Z'|'-' in an arithmetic operand, the result will be 'X'(es).
VHDL_STD_NOWARNINGS = 1

# FOR EMMC ONLY (TOP_LIGHT)
override VSIM_RUN_OPTS_EXT += +CID_FILE=$(REPO_ROOT)/hw/dv/emmc_softmodel/preload_CID.hex
override VSIM_RUN_OPTS_EXT += +CSD_FILE=$(REPO_ROOT)/hw/dv/emmc_softmodel/preload_CSD.hex
override VSIM_RUN_OPTS_EXT += +OCR_FILE=$(REPO_ROOT)/hw/dv/emmc_softmodel/preload_OCR.hex
override VSIM_RUN_OPTS_EXT += +EXT_CSD_FILE=$(REPO_ROOT)/hw/dv/emmc_softmodel/preload_EXT_CSD.hex
