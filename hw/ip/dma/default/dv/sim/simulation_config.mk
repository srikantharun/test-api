
# Configuration (IP_NAME must match name of DUT instance in TOP_LEVEL_MODULES : hdl_top) 
IP_NAME            = dma
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

TESTNAME     ?= dma_ip_basic_test
SEED         ?= 1
UVM          ?= 1

## Setting compilation time-out
SIM_COMPILE_TIME_MINUTES ?= 20

## Default settings for verifsdk
REGRESS_VERIFSDK_PLATFORM := uvm.HW_IP_DMA_DV
REGRESS_VERIFSDK_LABEL := DMA_DV_NIGHTLY

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
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_ADDR_WIDTH=40
override GLOBAL_DEFINES += +define+SVT_AXI_MAX_DATA_WIDTH=512
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

# Commented out as this leads to so many VIP errors : "Elements must both be 2-state or both be 4-state"
#
# This ensures data treated as logic (4-states) not bits (2-states) 
# override GLOBAL_DEFINES += +define+SVT_MEM_LOGIC_DATA

override GLOBAL_DEFINES += +define+AI_MVM_CSR_RAL
