##########################################################################################
# Script: stuckat.do
# tessent atpg dofile
# Owner: redouan.tahraoui@axelera.ai
#
##########################################################################################



set DESIGN apu_p
set DFT_HOME [getenv DFT_HOME] 
set mode intest ;# mode=intest || extest

if ![file isdirectory pattern_dir] {
  file mkdir patterns
  file delete patterns/*
}

if ![file isdirectory reports] {
  file mkdir reports
}

if ![file isdirectory tsdb_outdir] {
  file mkdir tsdb_outdir
#  file delete ${tsdb_outdir}/*
}

set_context pattern -scan

set_tsdb_output_directory ./tsdb_outdir

dofile ../../tessent_setup.tcl
# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}

# Mem lib
#read_mem_libs
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_*/dev/*/*.mdt

#open_tsdb $DFT_HOME/apu/Latest/dft/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/apu_l2c/Latest/tsdb/logic_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/apu_l2c/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/apu_core/Latest/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/apu_core/Latest/tsdb/logic_test/tsdb_outdir

open_tsdb /data/releases/europa/dft/shared-scratch/apu/Latest/tsdb/logic_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/shared-scratch/apu/Latest/tsdb/memory_test/tsdb_outdir

#open_tsdb ./tsdb


read_design ${DESIGN}	 -design_id rtl2 -no_hdl
read_design apu_core_p -design_identifier rtl2 -no_hdl
read_design apu_l2c_p -design_identifier rtl2 -no_hdl

read_verilog /data/europa/pd/apu_core_p/block_build/dev_dft/build/fc/compile/results/apu_core_p.insert_dft.v
read_verilog /data/europa/pd/apu_l2c_p/block_build/dev_dft/build/fc/compile/results/apu_l2c_p.insert_dft.v
read_verilog /data/europa/pd/apu_p/block_build/dev_dft_trial/build/fc/compile/results/apu_p.insert_dft.v


set_current_design ${DESIGN}
add_black_boxes -auto

set cmd "set_module_matching_options -prefix_pattern_list { ${DESIGN}_ } -suffix_pattern_list {_\[0-9\]+} -regexp"
eval $cmd
set cmd "set_module_matching_options -prefix_pattern_list {apu_core_p_} -append"
eval $cmd
set cmd "set_module_matching_options -prefix_pattern_list {apu_l2c_p_}  -append"
eval $cmd


if {$mode == "extest"} {

  foreach_in_collection mod [get_modules "apu*.*tessent_edt_cx_\[0-9\]*$" -regexp] {
    add_core_instances -module $mod
  }

  set_static_dft_signal_values int_mode 0
  set_static_dft_signal_values ext_mode 1 

} elseif {$mode == "intest"} {
  
  foreach_in_collection mod [get_modules "apu*.*tessent_edt_c1_int_\[0-9\]*$" -regexp] {
    add_core_instances -module $mod
  }

  foreach_in_collection inst [get_instances -hier "apu*.*_tessent_sib_sti_inst" -regexp] {
    add_core_instances -instance $inst
  }

  set_static_dft_signal_values int_mode 1
  set_static_dft_signal_values ext_mode 0 

}

# adding occ core instances
foreach_in_collection mod [get_modules "${DESIGN}.*tessent_occ_\[0-9\]*$" -regexp] {
  add_core_instances -module $mod
}


#add_core_instances -module  apu_p_apu_p_rtl2_tessent_ssn_scan_host_sh_0

report_core_instance_parameters

add_clocks 0 i_clk  -pulse_always -period 1ns
add_clocks 0 i_ref_clk  -pulse_always -period 1ns
#add_clocks 0 bisr_clk  -pulse_always -period 10ns

add_input_constraints test_mode -c1

set_load_unload_timing_options   \
 -usage ssn                      \
 -shift_clock_period             20 \
 -ssn_bus_clock_period           10 \
 -scan_en_setup_extra_cycles     2 \
 -scan_en_hold_extra_cycles      2 \
 -edt_update_setup_extra_cycles  2 \
 -edt_update_hold_extra_cycles   2

set_drc_handling e14 warn
set_system_mode analysis

#report_scan_cells > rpt/apu_p_${mode}_scan_cells.rpt
#report_drc_rules -verbose -all_fails > rpt/apu_p_${mode}_drc_rules.rpt

set_pattern_type -sequential 2

if {$mode == "extest"} {
  read_faults tsdb_outdir/logic_test_cores/${DESIGN}.logic_test_core/${DESIGN}.atpg_mode_unwrapped/${DESIGN}_unwrapped_stuck.faults.gz -merge
}

create_pattern
write_tsdb_data -repl

report_scan_cells        > reports/${mode}_scan_cells.rpt
report_scan_chains       > reports/${mode}_scan_chains.rpt
report_ssn_configuration > reports/${mode}_ssn_config.rpt
report_cell_constraints  > reports/${mode}_cell_constraint.rpt
report_patterns          > reports/${mode}_patterns.rpt
report_clocks            > reports/${mode}_clocks.rpt
report_statistics        > reports/${mode}_statistics.rpt


if ![file isdirectory pattern] {
  file mkdir pattern
}

write_pattern ./pattern/apu_p_${mode}.ser.v -verilog -serial -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl
exit
