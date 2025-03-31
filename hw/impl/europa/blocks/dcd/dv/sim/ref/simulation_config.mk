###################################################################
# TB config
###################################################################
BENDER_MANI_LOC := .
IP_NAME := allegro_tb_p
UVM_TESTNAME := allegro_tb_test
TOP_LEVEL_MODULES := alg_ip_top_tb
UVM_VERBOSITY := UVM_LOW
UVM=1
REGRESS_VERIFSDK_PLATFORM=uvm.SIM_DECODER_ALLEGRO_TB
GLOBAL_DEFINES += +define+UVM_NO_DPI
GLOBAL_DEFINES += +define+SVT_APB_DISCONNECT_TOP_LEVEL_APB_IF_SIGNALS
GLOBAL_DEFINES += +define+SVT_APB_MAX_ADDR_WIDTH=32
GLOBAL_DEFINES += +define+SVT_APB_MAX_DATA_WIDTH=32

ifeq ("$(USE_ALLEGRO_IP_TOP)", "1")
GLOBAL_DEFINES += +define+USE_ALLEGRO_IP_TOP
endif

# Use sf5a models by default
USE_SF5A_MODELS ?= 1

ifeq ("$(USE_SF5A_MODELS)", "1")
BENDER_TARGETS_EXT += sf5a
BENDER_TARGETS_EXT += asic
endif
