##########################################################################################
# Script: atpg.tcl
# tessent atpg dofile
# Owner:
#
##########################################################################################

set DESIGN_BASE l2
set DESIGN ${DESIGN_BASE}_p
set DFT_HOME [getenv DFT_HOME]

file mkdir ./pat
set_context pattern -scan

dofile ../tessent_setup.tcl

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*/*/FE-Common/ATPG/FastScan/*/*.mdt
read_mem_libs

open_tsdb $DFT_HOME/l2/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb $DFT_HOME/l2/Latest/tsdb/logic_test/tsdb_outdir

read_design ${DESIGN} -design_id rtl2 -no_hdl

read_verilog /data/europa/pd/l2_p/block_build/dev/build/fc/compile/results/l2_p.insert_dft.v

set_tsdb_output_directory ./tsdb_outdir

set_current_design ${DESIGN}

set cmd "set_module_matching_options -prefix_pattern_list { ${DESIGN}_ } -suffix_pattern_list {_\[0-9\]+} -regexp"
eval $cmd
foreach_in_collection mod [get_modules ".*tessent_edt_c1_int_\[0-9\]*$" -regexp] {
  add_core_instances -module $mod
}
foreach_in_collection inst [get_instances ".*_tessent_sib_sti_inst$" -regexp] {
  add_core_instances -instance $inst
}

report_core_instances
report_core_instance_parameters

add_black_boxes -auto


add_clocks 0 i_clk
add_clocks 0 test_clk
add_clocks 0 i_ref_clk -period 10ns -pulse_always
add_clocks 1 i_global_rst_n
add_clocks 1 i_ao_rst_n
add_input_constraints test_mode -c1

set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1
set_static_dft_signal_values tck_occ_en 1

set_system_mode analysis
report_static_dft_signal_settings

report_clocks                        > rpt/clocks.rpt
report_input_constraints             > rpt/input_constraints.rpt
report_scan_cells                    > rpt/scan_cells.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt
report_primary_inputs                > rpt/primary_inputs.rpt
report_core_parameters               > rpt/core_parameters.rpt
report_core_instances                > rpt/core_instances.rpt
report_core_instance_parameters      > rpt/core_instance_parameters.rpt

set_pattern_type -sequential 2

create_pattern

report_statistics  -detailed_analysis -threshold 0.01
report_faults -class au           > rpt/au.rpt
report_patterns                   > rpt/pat.rpt
report_procedures -expand_iprocs  > rpt/procedures_expanded.rpt
report_procedures                 > rpt/procedures.rpt
report_timeplates                 > rpt/timeplates.rpt
report_load_unload_timing_options > rpt/load_unload_timing_options.rpt
report_false_paths                > rpt/false_paths.rpt
report_multicycle_paths           > rpt/multicycle_paths.rpt
report_atpg_constraints           > rpt/atpg_constraints.rpt

write_tsdb_data -repl

if ![file isdirectory pattern] {
  file mkdir pattern
}

set_pattern_filtering -sample_per_type 10
write_pattern ./pat/${DESIGN}_scan_par.v -verilog -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl

exit
