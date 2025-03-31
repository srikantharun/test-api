#settings
set DESIGN            ddr_west_clock_gen_p
set DESIGN_ID         rtl2
set USE_MBIST_TSDB    0
set USE_PREPROCESSING 0
set BLACKBOXES        { }
set_context dft -rtl -design_id ${DESIGN_ID}
set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

dofile ${DEPENDENCIES_DIR}/read_rtl.do

set_current_design ${DESIGN}

set_design_level physical_block

if { [llength $BLACKBOXES] > 0 } {
  add_black_boxes -modules $BLACKBOXES
} else {
  add_black_boxes -auto
}

add_dft_signals ltest_en -source test_mode -make_ijtag_port
set_dft_specification_requirements -logic_test off -host_scan_interface_type tap

add_clock 0 i_ref_clk -period 20.000ns

add_input_constraints i_ao_rst_n -C1
add_input_constraints i_global_rst_n  -C1

#######DFT control points added for PLL lock#####

register_static_dft_signal_names tdr1 -reset_value 0
add_dft_signals tdr1 -create_with_tdr
add_dft_control_points u_ddr_west_clock_gen/u_pll_wrapper/i_pll_bypass -dft_signal_source_name tdr1


for {set j 0} {$j < 10 } {incr j } {
register_static_dft_signal_names tdr_pll_m${j} -reset_value 0
add_dft_signals tdr_pll_m${j} -create_with_tdr
add_dft_control_points u_ddr_west_clock_gen/u_pll_wrapper/i_pll_m[$j] -dft_signal_source_name tdr_pll_m${j}
}
for {set j 0} {$j < 6 } {incr j } {
register_static_dft_signal_names tdr_pll_p${j} -reset_value 0
add_dft_signals tdr_pll_p${j} -create_with_tdr
add_dft_control_points u_ddr_west_clock_gen/u_pll_wrapper/i_pll_p[$j] -dft_signal_source_name tdr_pll_p${j}
}

for {set j 0} {$j < 3 } {incr j } {
register_static_dft_signal_names tdr_pll_s${j} -reset_value 0
add_dft_signals tdr_pll_s${j} -create_with_tdr 
add_dft_control_points u_ddr_west_clock_gen/u_pll_wrapper/i_pll_s[$j] -dft_signal_source_name tdr_pll_s${j}
}

set_system_mode analysis

create_dft_specification
report_config_data
process_dft_specification
# Print modified files list to shell and to listfile
write_filemap ./tsdb_outdir/modified_files.lst

extract_icl

# ICLNetwork
set_context patterns -ijtag
set patSpec [create_patterns_specification -replace]
report_config_data
source pll.pdl
# pll Program
set_system_mode ana
open_pattern_set pat1 -tester_period 50ns
iCall pll_cmd
read_config_data -in_wrapper $patSpec -from_string {

 Patterns (pll_cmd) {
 ProcedureStep (pll_cmd) { iCall(pll_cmd) { iProcArguments { } } }
}
}

process_patterns_specification
#display_specification
#stop

exit
