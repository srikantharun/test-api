
# Configuration
IP_NAME            = soc_mgmt
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

TESTNAME     ?= soc_mgmt_base_test
SEED         ?= 1
UVM          ?= 1

## Setting compilation time-out
SIM_COMPILE_TIME_MINUTES ?= 30

GLOBAL_DEFINES += +define+UVM_NO_DPI
GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING
# GLOBAL_DEFINES += +define+UVM_DEPRECATED_STARTING_PHASE
GLOBAL_DEFINES += +define+AXI_VIP
GLOBAL_DEFINES += +define+APB_VIP
GLOBAL_DEFINES += +define+SYNOPSYS_SV
GLOBAL_DEFINES += +define+ASSERTIONS_ON
GLOBAL_DEFINES += +define+UVM

# New for bender, as svt.uvm.pkg includes uvm pkg definition
GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=32
GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=64
GLOBAL_DEFINES += +define+SVT_AXI_MAX_TDATA_WIDTH=1664
GLOBAL_DEFINES += +define+SVT_AXI_MAX_BURST_LENGTH_WIDTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_ID_WIDTH=9
GLOBAL_DEFINES += +define+SVT_AXI_MAX_CACHE_WIDTH=4
GLOBAL_DEFINES += +define+SVT_AXI_CACHE_WIDTH=4
GLOBAL_DEFINES += +define+SVT_AXI_LOCK_WIDTH=1
GLOBAL_DEFINES += +define+SVT_AXI_MAX_PROT_WIDTH=3
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2
GLOBAL_DEFINES += +define+SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH=8
GLOBAL_DEFINES += +define+SVT_AXI_MAX_STREAM_BURST_LENGTH=9999 #change because of tready_delay>10000; Its performanace degration
GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
GLOBAL_DEFINES += +define+SVT_APB_MAX_ADDR_WIDTH=16
GLOBAL_DEFINES += +define+SVT_APB_MAX_DATA_WIDTH=32

GLOBAL_DEFINES += +define+SOTP_SET_PWR_ON=3
