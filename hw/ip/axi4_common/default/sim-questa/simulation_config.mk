# Configuration for the IP
IP_NAME            = axi4_common_sanity_compile
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

TOP_LEVEL_MODULES  = axi_mailbox
TOP_LEVEL_MODULES += axi2reg
TOP_LEVEL_MODULES += simple_axi_demux
