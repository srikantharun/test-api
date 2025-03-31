###################################################################
# TB config
###################################################################
BENDER_MANI_LOC := .
IP_NAME := axi_stress_top_test
UVM_TESTNAME := axi_stress_top_test
TOP_LEVEL_MODULES := axi_stress_top_tb
UVM_VERBOSITY := UVM_LOW
UVM=1
GLOBAL_DEFINES += +define+NB_PERIPHS=7
GLOBAL_DEFINES += +define+UVM_NO_DPI
BENDER_TARGETS_EXT += simulation sf5a asic
REGRESS_VERIFSDK_PLATFORM := uvm.SIM_SOC_PERIPH_AXI
REGRESS_VERIFSDK_LABEL := SOC_PERIPH_NIGHTLY
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2 \
		  +define+SVT_AXI_LOCK_WIDTH=1 \
		  +define+SVT_AXI_LOCK_WIDTH_AS_ONE \
			+define+SVT_APB_DISCONNECT_TOP_LEVEL_APB_IF_SIGNALS \
			+define+SVT_APB_MAX_DATA_WIDTH=32 \
		  +define+UVM_NO_DPI
