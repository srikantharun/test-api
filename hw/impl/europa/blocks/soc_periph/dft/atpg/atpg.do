##########################################################################################
# Script: atpg.tcl
# tessent atpg dofile
# Owner:
#
##########################################################################################

set DESIGN_BASE soc_periph
set DESIGN ${DESIGN_BASE}_p
set DFT_HOME [getenv DFT_HOME]

file mkdir ./pat
set_context pattern -scan

dofile ../tessent_setup.tcl

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*/*/FE-Common/ATPG/FastScan/*/*.mdt
read_mem_libs

open_tsdb $DFT_HOME/soc_periph/Latest/tsdb/logic_test/tsdb_outdir

read_design ${DESIGN} -design_id rtl2 -no_hdl

read_verilog /data/europa/pd/soc_periph_p/block_build/dev_dft/build/fc/compile/results/soc_periph_p.insert_dft.v

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

delete_input_constraints [get_ports i_*rst_n]
delete_input_constraints ijtag_reset

add_clocks 0 bisr_clk
add_clock 0 i_emmc_clk
add_clock 0 i_periph_clk

#add_clocks 0 i_clk
add_clocks 0 ijtag_tck
add_clocks 0 test_clk

add_clocks 1 [get_ports i_*rst_n]
add_clocks 1 bisr_reset
add_clocks 1 ijtag_reset
add_input_constraints test_mode -c1

set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1

set_system_mode analysis
report_static_dft_signal_settings

report_scan_cells > rpt/scan_cells.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt

set_pattern_type -sequential 2

create_pattern
report_patterns > rpt/pat.rpt
write_tsdb_data -repl

if ![file isdirectory pattern] {
  file mkdir pattern
}

write_pattern ./pat/${DESIGN}_scan_par.v -verilog -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl
exit
