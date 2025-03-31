# Configuration for the IP
IP_NAME            = aic_dp_cmd_gen
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = .
UVM                = 1
TESTNAME           = ai_core_dp_cmd_gen_m1n0_test
SEED               = 1

XPROP_PATH        ?= hdl_top/u_dut.

REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_DP_CMD_GEN_DEFAULT_DV_SIM
REGRESS_VERIFSDK_LABEL   ?= HW_IP_DP_CMD_GEN_TEST

# Design Specific
override GLOBAL_DEFINES += +define+AIC_DP_CMD_GEN_COMMAND_DEPTH=1024

# SVT
override GLOBAL_DEFINES += +define+UVM_NO_DPI

override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
override GLOBAL_DEFINES += +define+AXI_VIP
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
override GLOBAL_DEFINES += +define+ASSERTIONS_ON
override GLOBAL_DEFINES += +define+UVM

# New for bender, as svt.uvm.pkg includes uvm pkg definition
override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=64
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=64
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
override GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
