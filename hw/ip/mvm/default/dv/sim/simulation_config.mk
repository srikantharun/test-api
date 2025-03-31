
# Configuration
IP_NAME            = mvm
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

TESTNAME     ?= ai_core_mvm_ral_base_test
SEED         ?= 1
UVM          ?= 1

REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_MVM_DEFAULT_DV_SIM

## Setting compilation time-out
SIM_COMPILE_TIME_MINUTES ?= 20



override GLOBAL_DEFINES += +define+UVM_NO_DPI

override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
# override GLOBAL_DEFINES += +define+UVM_DEPRECATED_STARTING_PHASE
override GLOBAL_DEFINES += +define+AXI_VIP
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
override GLOBAL_DEFINES += +define+ASSERTIONS_ON
override GLOBAL_DEFINES += +define+UVM

# New for bender, as svt.uvm.pkg includes uvm pkg definition
override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=32
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=64
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_TDATA_WIDTH=1664
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_CACHE_WIDTH=4
override GLOBAL_DEFINES += +define+SVT_AXI_CACHE_WIDTH=4
override GLOBAL_DEFINES += +define+SVT_AXI_LOCK_WIDTH=1
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_PROT_WIDTH=3
override GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=9999 #change because of tready_delay>10000; Its performanace degration
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY

override GLOBAL_DEFINES += +define+AI_MVM_CSR_RAL
