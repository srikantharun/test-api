# Configuration for the IP
IP_NAME            = noc_mem_wrap_top
TOP_LEVEL_MODULES  = hdl_top
BENDER_MANI_LOC    = .
UVM                = 1
TESTNAME           = noc_mem_capacity_test
# TESTNAME           = noc_mem_random_test
SEED               = 1

REGRESS_VERIFSDK_PLATFORM = uvm.HW_IP_NOC_MEM_DEFAULT_DV_SIM
REGRESS_VERIFSDK_LABEL   ?= HW_IP_NOC_MEM_TEST

# Defaults -- check docs/europa/blocks/noc/memory-macros.md for all value combinations used in the design
override GLOBAL_DEFINES += +define+DATAW=579
override GLOBAL_DEFINES += +define+DEPTH=63
override GLOBAL_DEFINES += +define+MACRO_DATAW=160
override GLOBAL_DEFINES += +define+MACRO_DEPTH=64
