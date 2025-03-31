#!/usr/bin/env bash

# infile must match exact DFT release used to create netlist
infile=${DFT_HOME}"/noc_h_north/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/noc_h_north_p_rtl2.dft_inserted_design/noc_h_north_p.sdc"

sed -r \
    -e "s@tessent_persistent_cell_BUF_C_TCK/o_clk@tessent_persistent_cell_BUF_C_TCK/u_tc_lib_clk_inv1/Y@g" \
    -e "s@tessent_persistent_cell_BUF_I_TCK/o_clk@tessent_persistent_cell_BUF_I_TCK/u_tc_lib_clk_inv1/Y@g" \
    -e "s@tessent_persistent_cell_BIST_CLK_OR_TCK/i_sel@tessent_persistent_cell_BIST_CLK_OR_TCK/u_tc_lib_clk_mux/S0@g" \
    -e "s@tessent_persistent_cell_BIST_CLK_INT/i_sel@tessent_persistent_cell_BIST_CLK_INT/u_tc_lib_clk_mux/S0@g" \
    -e "s@tessent_persistent_cell_ltest_clock_mux@tessent_persistent_cell_ltest_clock_mux/u_tc_lib_clk_mux@g" \
    -e "s@tessent_persistent_cell_AND_([^/]*)/o_z@tessent_persistent_cell_AND_\1/u_tc_lib_std_inv/Y@g" \
    -e "s@tessent_persistent_cell_([^/]*)/o_z@tessent_persistent_cell_\1/u_tc_lib_std_buf/Y@g" \
    -e "s@tessent_persistent_cell_([^/]*)/i_a@tessent_persistent_cell_\1/u_tc_lib_std_buf/A@g" \
    $infile > noc_h_north_p.hierfix.sdc
