# Configuration for the IP
IP_NAME            = aic_dp_cmd_gen
TOP_LEVEL_MODULES  = aic_dp_cmd_gen_tb

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/design_tb


# In aic_common axi drivers, not used: (vlog-13262) A virtual interface element is not allowed in a sensitivity list.
VSIM_VLOG_OPTS += -suppress 13262

# For preloading the memory
VSIM_VOPT_OPTS_EXT += -access=w+/aic_dp_cmd_gen_tb/u_aic_dp_cmd_gen_dut/u_cmdblock_desc_mem/gen_ram/u_tc_ram/memory_q
