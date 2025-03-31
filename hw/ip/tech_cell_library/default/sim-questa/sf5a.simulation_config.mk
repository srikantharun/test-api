
# Configuration
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl
BENDER_TARGETS_EXT += asic
BENDER_TARGETS_EXT += sf5a

IP_NAME            = axe_tcl_sf5a

TOP_LEVEL_MODULES  += axe_tcl_clk_buffer
TOP_LEVEL_MODULES  += axe_tcl_clk_inverter
TOP_LEVEL_MODULES  += axe_tcl_clk_and2
TOP_LEVEL_MODULES  += axe_tcl_clk_or2
TOP_LEVEL_MODULES  += axe_tcl_clk_xor2
TOP_LEVEL_MODULES  += axe_tcl_clk_mux2
TOP_LEVEL_MODULES  += axe_tcl_clk_gating

TOP_LEVEL_MODULES  += axe_tcl_pad_inout
TOP_LEVEL_MODULES  += axe_tcl_pad_output
TOP_LEVEL_MODULES  += axe_tcl_pad_input
# TOP_LEVEL_MODULES  += axe_tcl_pad_oscillator
TOP_LEVEL_MODULES  += axe_tcl_pad_power

TOP_LEVEL_MODULES  += axe_tcl_seq_sync

TOP_LEVEL_MODULES  += axe_tcl_std_buffer
TOP_LEVEL_MODULES  += axe_tcl_std_inverter
TOP_LEVEL_MODULES  += axe_tcl_std_and2
TOP_LEVEL_MODULES  += axe_tcl_std_and3
TOP_LEVEL_MODULES  += axe_tcl_std_nand2
TOP_LEVEL_MODULES  += axe_tcl_std_nand3
TOP_LEVEL_MODULES  += axe_tcl_std_or2
TOP_LEVEL_MODULES  += axe_tcl_std_or3
TOP_LEVEL_MODULES  += axe_tcl_std_nor2
TOP_LEVEL_MODULES  += axe_tcl_std_nor3
TOP_LEVEL_MODULES  += axe_tcl_std_xor2
TOP_LEVEL_MODULES  += axe_tcl_std_xor3
TOP_LEVEL_MODULES  += axe_tcl_std_xnor2
TOP_LEVEL_MODULES  += axe_tcl_std_xnor3
TOP_LEVEL_MODULES  += axe_tcl_std_mux2
