###################################################################
# TB config
###################################################################
BENDER_MANI_LOC := .
IP_NAME := spike_top_test
TOP_LEVEL_MODULES := spike_top_tb
UVM_VERBOSITY := UVM_LOW
REGRESS_VERIFSDK_PLATFORM := top.SIM_SOC_PERIPH_SPIKE
REGRESS_VERIFSDK_LABEL := SOC_PERIPH_NIGHTLY
REGRESS_VERIFSDK_ARGS := -F printf.FESVR
SW_BUILD_DIR := $(MAKEFILE_DIR)/build_sw
REGRESS_SW_BUILD_DIR := $(SW_BUILD_DIR)
UVM=1
UVM_TESTNAME ?= spike_top_test
BENDER_TARGETS_EXT += simulation sf5a asic

# Add rw access for uvm_hdl_read/write functions
VSIM_VOPT_OPTS_EXT += -access=rw+/.

# FIXME: UVM_PACKER_MAX_BYTES is lower than the value requested by the VIPs. This is due to the fact we are using pre-built
# UVM binaries with VSIM. This might cause issues in the future.
GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2 \
                  +define+SVT_AXI_LOCK_WIDTH=1 \
                  +define+UVM_NO_DPI \
                  +define+SVT_AXI_LOCK_WIDTH_AS_ONE \
                  +define+UVM_DISABLE_AUTO_ITEM_RECORDING \
                  +define+UVM_PACKER_MAX_BYTES=4096 \
                  +define+SVT_SPI_DATA_WIDTH=8 \
                  +define+SVT_SPI_IO_WIDTH=4 \
                  +define+SVT_SPI_MAX_NUM_SLAVES=4 \
                  +define+DV_AXI_RAM_UNBOUNDED \
                  +define+SVT_MEM_ENABLE_DEPTH_INDEPENDENT_VALUES # For flash mode
#                  # TODO: Investigate if this is needed
                  # +incdir+$(DESIGNWARE_HOME)/vip/svt/common/latest/C/lib/linux/libmemserver.so

###################################################################
##@ Spike compilation
###################################################################
include spike_dpi.mk

DPI_C_SRC += ../cpp/spike_dpi.cpp

###################################################################
##@ Spike tb run targets
###################################################################
.PHONY: gen_memfile
gen_memfile:
	$(REPO_ROOT)/hw/impl/europa/blocks/soc_periph/dv/spike_tb/uvm/tb/gen_slave_mem.py

RUN_VSIM_PREREQUISITES      += gen_memfile
