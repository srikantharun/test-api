#!/usr/bin/env bash

BLOCK=soc_mgmt
# infile must match exact DFT release used to create netlist
infile="${DFT_HOME}/${BLOCK}/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${BLOCK}_p_rtl2.dft_inserted_design/${BLOCK}_p.sdc"

sed -r \
    -e 's@tessent_persistent_cell_BUF_C_TCK/o_clk@tessent_persistent_cell_BUF_C_TCK/u_tc_lib_clk_inv1/Y@g' \
    -e 's@tessent_persistent_cell_BUF_I_TCK/o_clk@tessent_persistent_cell_BUF_I_TCK/u_tc_lib_clk_inv1/Y@g' \
    -e 's@tessent_persistent_cell_BIST_CLK_OR_TCK/i_sel@tessent_persistent_cell_BIST_CLK_OR_TCK/u_tc_lib_clk_mux/S0@g' \
    -e 's@tessent_persistent_cell_BIST_CLK_INT/i_sel@tessent_persistent_cell_BIST_CLK_INT/u_tc_lib_clk_mux/S0@g' \
    -e 's@tessent_persistent_cell_ltest_clock_mux@tessent_persistent_cell_ltest_clock_mux/u_tc_lib_clk_mux@g' \
    -e 's@tessent_persistent_cell_edt_update_mux/o_z@tessent_persistent_cell_edt_update_mux/u_tc_lib_std_mux/Y@g' \
    -e 's@tessent_persistent_cell_from_scan_out\*_mux\*/o_z@tessent_persistent_cell_from_scan_out\*_mux\*/u_tc_lib_std_mux/Y@g' \
    -e 's@tessent_persistent_cell_from_scan_out\*_and/o_z@tessent_persistent_cell_from_scan_out\*_and/u_tc_lib_std_inv/Y@g' \
    -e 's@tessent_persistent_cell_AND_([^/]*)/o_z@tessent_persistent_cell_AND_\1/u_tc_lib_std_inv/Y@g' \
    -e 's@tessent_persistent_cell_([^/]*)/o_z@tessent_persistent_cell_\1/u_tc_lib_std_buf/Y@g' \
    -e '/set_false_path -through \$all_mbisr_clock_pins/s/^/#/' \
    $infile > ${BLOCK}_p.hierfix.sdc
#    -e 's@clock_gen/tessent_persistent_cell_edt_update_mux@clock_gen*tessent_persistent_cell_edt_update_mux@g' \
#    -e 's@clock_gen/clock_signals/tessent_persistent_cell_test_clock_buf@clock_gen*clock_signals*tessent_persistent_cell_test_clock_buf@g' \
