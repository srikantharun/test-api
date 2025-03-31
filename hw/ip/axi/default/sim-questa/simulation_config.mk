
# Configuration
IP_NAME            = axe_axi_sanity_compile

TOP_LEVEL_MODULES  = axe_axi_multicut
TOP_LEVEL_MODULES += axe_axi_cut
TOP_LEVEL_MODULES += axe_axi_atop_filter
TOP_LEVEL_MODULES += axe_axi_err_sub
TOP_LEVEL_MODULES += axe_axi_demux
TOP_LEVEL_MODULES += axe_axi_mux
TOP_LEVEL_MODULES += axe_axi_id_prepend
TOP_LEVEL_MODULES += axe_axi_id_remap
TOP_LEVEL_MODULES += axe_axi_xbar
TOP_LEVEL_MODULES += axe_axi_dw_downsizer
TOP_LEVEL_MODULES += axe_axi_dw_upsizer
TOP_LEVEL_MODULES += axe_axi_dw_converter
TOP_LEVEL_MODULES += axe_axi_modify_address
TOP_LEVEL_MODULES += axe_axi_atu
TOP_LEVEL_MODULES += axe_axi_riscv_amos
TOP_LEVEL_MODULES += axe_axi_riscv_lrsc
TOP_LEVEL_MODULES += axe_axi_riscv_atomics
TOP_LEVEL_MODULES += axe_axi_isolate

BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl
