###################################################################
# TB config
###################################################################
BENDER_MANI_LOC := .
IP_NAME := spike_top_test
TOP_LEVEL_MODULES := spike_top_tb
UVM_VERBOSITY := UVM_LOW
REGRESS_VERIFSDK_PLATFORM := top.SIM_SECURE_SPIKE
REGRESS_VERIFSDK_LABEL := SIM_TOP_SECURE_SPIKE_NIGHTLY
REGRESS_VERIFSDK_ARGS := -F printf.FESVR
SW_BUILD_DIR := $(MAKEFILE_DIR)/build_sw
REGRESS_SW_BUILD_DIR := $(SW_BUILD_DIR)
UVM=1
UVM_TESTNAME ?= spike_top_test

# Add rw access for uvm_hdl_read/write functions
VSIM_VOPT_OPTS_EXT += -access=rw+/.

GLOBAL_DEFINES += +define+SVT_AXI_RESP_WIDTH=2 \
									+define+SVT_AXI_LOCK_WIDTH=1 \
									+define+SVT_AXI_LOCK_WIDTH_AS_ONE \
									+define+UVM_DISABLE_AUTO_ITEM_RECORDING \
									+define+UVM_PACKER_MAX_BYTES=4096 \
									+define+DV_AXI_RAM_UNBOUNDED \
									+define+SVT_MEM_ENABLE_DEPTH_INDEPENDENT_VALUES # For flash mode

#allow the tests to take more that one hour
SIM_RUN_TIME_MINUTES=240

###################################################################
##@ Spike compilation
###################################################################

DPI_C_SRC += ../cpp/spike_dpi.cpp ../cpp/dpi_devices.cpp
DPI_C_INCDIR += $(SPIKE_HOME)/include/ \
								$(SPIKE_HOME)/include/riscv \
								../cpp/ \
								$(REPO_ROOT)/sw/src/lib/

DPI_C_OPTS += -Wl,-rpath=$(SPIKE_HOME)/lib \
							-L$(SPIKE_HOME)/lib \
							-lriscv \
							-DARCH=64

ifeq ($(DEBUG), 1)
DPI_C_OPTS += -DDUMP_INST
endif

###################################################################
##@ Spike tb run targets
###################################################################
.PHONY: gen_memfile
gen_memfile:
	$(REPO_ROOT)/hw/impl/europa/blocks/soc_periph/dv/spike_tb/uvm/tb/gen_slave_mem.py

RUN_VSIM_PREREQUISITES      += gen_memfile
