##########################################################################################
# Script: atpg.tcl
# tessent atpg dofile
# Owner:
#
##########################################################################################

set DESIGN_BASE aic_ls
set DESIGN ${DESIGN_BASE}_p
set DFT_HOME [getenv DFT_HOME]

set DFT_RELEASE "/data/releases/europa/dft/bronze/aic_ls/202412110729"
set SI_NETLIST  "/data/europa/pd/aic_ls_p/block_build/dev_bronze_AM/build/fc/compile/results/aic_ls_p.insert_dft.v"

file mkdir ./pat
set_context pattern -scan

dofile ../tessent_setup.tcl

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*/*/FE-Common/ATPG/FastScan/*/*.mdt
read_mem_libs

open_tsdb ${DFT_RELEASE}/tsdb/memory_test/tsdb_outdir
open_tsdb ${DFT_RELEASE}/tsdb/logic_test/tsdb_outdir

read_design ${DESIGN} -design_id rtl2 -no_hdl

read_verilog $SI_NETLIST

set_tsdb_output_directory ./tsdb_outdir

set_current_design ${DESIGN}

#set cmd "set_module_matching_options -module_name_map_list { ${DESIGN}_rtl2_tessent_edt_c1_int ${DESIGN}_${DESIGN}_rtl2_tessent_edt_c1_int_0 }"
#eval $cmd
#add_core_instances -module ${DESIGN}_${DESIGN}_rtl2_tessent_edt_c1_int_0
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

#set_current_mode int_sa -type internal
#import_scan_mode int_sa -fast_capture off

#set_ijtag_retargeting_options -tck_period 10ns

#set_capture_timing_options -mode_type internal -capture_clock_period 40ns
#set_core_instance_parameters -instrument_type occ -parameter_values {capture_window_size 3}

add_black_boxes -auto

delete_input_constraints i_rst_n
delete_input_constraints ijtag_reset

#add_clocks 0 bisr_clk
add_clocks 0 i_clk
#add_clocks 0 ijtag_tck
add_clocks 0 test_clk

add_clocks 1 i_rst_n
#add_clocks 1 bisr_reset
#add_clocks 1 ijtag_reset
add_input_constraints test_mode -c1

set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1
set_static_dft_signal_values tck_occ_en 1

set_system_mode analysis
report_static_dft_signal_settings

report_clocks                        > rpt/clocks.rpt
report_input_constraints             > rpt/input_constraints.rpt
report_scan_cells                    > rpt/scan_cells.rpt
report_drc_rules -summary            > rpt/drc_rules_summary.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt
report_primary_inputs                > rpt/primary_inputs.rpt
report_core_parameters               > rpt/core_parameters.rpt
report_core_instances                > rpt/core_instances.rpt
report_core_instance_parameters      > rpt/core_instance_parameters.rpt

set_pattern_type -sequential 2
#-multiple_load on

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
