
# Configuration for the IP
IP_NAME            = process_monitor
TOP_LEVEL_MODULES  = process1_monitor_wrapper
TOP_LEVEL_MODULES += process2_monitor_wrapper

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

# Custom compile configuration

BENDER_TARGETS_EXR = "asic simulation"
