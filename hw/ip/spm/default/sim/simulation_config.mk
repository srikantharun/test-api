#############################################
# Add VCS analyse options for sys_ctrl
#############################################
# Configuration
IP_NAME            = spm
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../dv/tb
BENDER_TARGETS_EXT  = asic
BENDER_TARGETS_EXT += sf5a

TESTNAME     ?= spm_singles_wr_test
SEED         ?= 1
UVM          ?= 1
# UVM options
override GLOBAL_DEFINES += +define+UVM_NO_DPI
override GLOBAL_DEFINES += +define+UVM_NO_DEPRECATED
override GLOBAL_DEFINES += +define+UVM_DISABLE_AUTO_ITEM_RECORDING

# Include the AXI_VIP defines
override GLOBAL_DEFINES += +define+AXI_VIP
override GLOBAL_DEFINES += +define+SYNOPSYS_SV
# reduces verbosity in sf5a mem cells
override GLOBAL_DEFINES += +define+BACKDOOR_DISPLAY_OFF
# SVT configuration defines
override GLOBAL_DEFINES += +define+SVT_EXCLUDE_METHODOLOGY_PKG_INCLUDE
override GLOBAL_DEFINES += +define+SVT_UVM_12_OR_HIGHER
override GLOBAL_DEFINES += +define+UVM
override GLOBAL_DEFINES += +define+SVT_UVM_TECHNOLOGY
override REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_SPM_DEFAULT_DV_SIM
#ECC define needed for the HDL TOP, only applies in a ecc testcase
ifneq ($(findstring ecc,$(TESTNAME)),)
    override GLOBAL_DEFINES += +define+ECC_TESTCASE
endif
