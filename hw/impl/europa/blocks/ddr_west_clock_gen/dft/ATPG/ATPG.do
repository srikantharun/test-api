##########################################################################################
# Script: atpg.tcl
# tessent atpg dofile
# Owner:
#
##########################################################################################

set DESIGN_BASE ddr_west_clock_gen
set DESIGN ${DESIGN_BASE}_p
set DFT_HOME [getenv DFT_HOME]

file mkdir ./pat
set_context pattern -scan

dofile ../tessent_setup.tcl

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*/*/FE-Common/ATPG/FastScan/*/*.mdt
read_mem_libs

open_tsdb /home/projects_2/workspace/rangsing/europa/hw/impl/europa/blocks/noc/ddr_west_clock_gen/dft/insertion/logic_test/tsdb_outdir

read_design ${DESIGN} -design_id rtl2 -no_hdl

read_verilog /data/europa/pd/ddr_west_clock_gen_p/block_build/dev_dft_2/build/fc/compile/results/ddr_west_clock_gen_p.insert_dft.v

set_tsdb_output_directory ./tsdb_outdir

set_current_design ${DESIGN}
set cmd "set_module_matching_options -module_name_map_list { ${DESIGN}_rtl2_tessent_edt_c1_int ${DESIGN}_${DESIGN}_rtl2_tessent_edt_c1_int_0 }"
eval $cmd
add_core_instances -module ${DESIGN}_${DESIGN}_rtl2_tessent_edt_c1_int_0

report_core_instance_parameters

#set_current_mode int_sa -type internal
#import_scan_mode int_sa -fast_capture off

#set_ijtag_retargeting_options -tck_period 10ns

#set_capture_timing_options -mode_type internal -capture_clock_period 40ns
#set_core_instance_parameters -instrument_type occ -parameter_values {capture_window_size 3}

add_black_boxes -auto

delete_input_constraints i_noc_rst_n
#delete_input_constraints trst

#add_clocks 0 bisr_clk
add_clock 0 i_lpddr_graph_0_aon_clk
add_clock 0 i_lpddr_graph_0_clk 
add_clock 0 i_lpddr_graph_1_aon_clk
add_clock 0 i_lpddr_graph_1_clk 
add_clock 0 i_lpddr_graph_2_aon_clk 
add_clock 0 i_lpddr_graph_2_clk
add_clock 0 i_lpddr_graph_3_aon_clk
add_clock 0 i_lpddr_graph_3_clk
add_clocks 0 i_noc_clk
add_clocks 0 tck
add_clocks 0 test_clk

add_clocks 1 i_noc_rst_n
add_clocks 1 i_lpddr_graph_0_aon_rst_n
add_clocks 1 i_lpddr_graph_0_rst_n 
add_clocks 1 i_lpddr_graph_1_aon_rst_n
add_clocks 1 i_lpddr_graph_1_rst_n
add_clocks 1 i_lpddr_graph_2_aon_rst_n
add_clocks 1 i_lpddr_graph_2_rst_n
add_clocks 1 i_lpddr_graph_3_aon_rst_n
add_clocks 1 i_lpddr_graph_3_rst_n

#add_clocks 1 bisr_reset
add_clocks 1 trst
add_input_constraints test_mode -c1

set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1

set_system_mode analysis
report_static_dft_signal_settings > static_signals_ddr_west_clock_gen.rpt

report_scan_cells > rpt/scan_cells.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt

set_pattern_type -sequential 2

create_pattern
report_patterns > rpt/pat.rpt
# coverage Improvement Analysis
report_statistics -detailed_analysis > statistical_report_${DESIGN}.rpt
create_flat_model
write_flat_model ${DESIGN} -include_proc_simulation_data all
write_faults fltlist_au.tc -class au.tc -repl
write_faults fltlist_au.pc -class au.pc -repl


write_tsdb_data -repl

if ![file isdirectory pattern] {
  file mkdir pattern
}

write_pattern ./pat/${DESIGN}_scan_par.v -verilog -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl
exit


