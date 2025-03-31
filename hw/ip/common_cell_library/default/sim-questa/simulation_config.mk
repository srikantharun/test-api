
# Configuration
BENDER_MANI_LOC    = $(MAKEFILE_DIR)/../rtl

IP_NAME            = axe_ccl

TOP_LEVEL_MODULES  = cc_decode_population
TOP_LEVEL_MODULES += cc_decode_onehot
TOP_LEVEL_MODULES += axe_ccl_clk_div_by_2
TOP_LEVEL_MODULES += axe_ccl_clk_or_tree
TOP_LEVEL_MODULES += axe_ccl_rst_n_sync
TOP_LEVEL_MODULES += axe_ccl_cdc_pulse
TOP_LEVEL_MODULES += axe_ccl_cnt_to_threshold
TOP_LEVEL_MODULES += axe_ccl_mon_hysteresis_comparator
TOP_LEVEL_MODULES += axe_ccl_mon_minimum_maximum
TOP_LEVEL_MODULES += axe_ccl_stream_fifo_mem
TOP_LEVEL_MODULES += axe_ccl_cnt_delta
TOP_LEVEL_MODULES += axe_ccl_decode_gray
TOP_LEVEL_MODULES += axe_ccl_cdc_fifo
TOP_LEVEL_MODULES += axe_ccl_cdc_4_phase
TOP_LEVEL_MODULES += axe_ccl_cdc_reset_control

TOP_LEVEL_MODULES += id_queue

GLOBAL_DEFINES    += +define+ASSERTIONS_ON
