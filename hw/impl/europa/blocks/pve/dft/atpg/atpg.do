set DESIGN_BASE pve
set DESIGN ${DESIGN_BASE}_p
set DESIGN_ID rtl2
set DFT_HOME [getenv DFT_HOME]
set PROD 0

global ft block pat_ids mode fault_id sdc_mode sdc_corner
dofile $env(REPO_ROOT)/hw/impl/europa/dft/dofiles/funcs.tcl
dofile ../tessent_setup.tcl

set design_id rtl
if {$PROD} {
    set parallel 64
} else {
    set parallel 1
}
if {${ft} eq "stuck"} {
    set fc "off"
} else {
    set fc "on"
}
global tck_period_ns
set ::tck_period_ns 10
set cap_period_factor 4
global tck_period_ps
set ::tck_period_ps [expr $tck_period_ns * 1000]
set_context pattern -scan -design_id ${DESIGN_ID}
set_tsdb_output_directory tsdb_outdir
set_multiprocessing_options -multithreading on
add_processors localhost:${parallel}

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*/*/FE-Common/ATPG/FastScan/*/*.mdt
read_mem_libs
open_tsdb /data/releases/europa/dft/bronze/pve_cva6v/202411121318/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pve_cva6v/202411121318/tsdb/logic_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pve_l1/202411141444/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pve_l1/202411141444/tsdb/logic_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pve/202411151304/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pve/202411151304/tsdb/logic_test/tsdb_outdir
read_design pve_cva6v_p -design_id ${DESIGN_ID} -no_hdl
read_design pve_l1_p    -design_id ${DESIGN_ID} -no_hdl
read_design pve_p   -design_id ${DESIGN_ID} -no_hdl
read_verilog /data/europa/pd/pve_cva6v_p/block_build/dev_prebronze_21oct.fp03/build.dft/fc/compile/results/pve_cva6v_p.insert_dft.v.gz
read_verilog /data/europa/pd/pve_l1_p/block_build/dev/build/fc/compile/results/pve_l1_p.insert_dft.v.gz
read_verilog /data/europa/pd/pve_p/block_build/dev_dft/build/fc/compile/results/pve_p.insert_dft.v.gz

set_module_matching_options -prefix_pattern_list {pve_p aic_did_p_ aic_mid_p_ aic_ls_p_ aic_infra_p_} -suffix_pattern_list {_[0-9]+} -regexp
set_current_design $block

add_clock 0 i_clk     -period 1ns -pulse_always
add_clock 0 i_ref_clk -period 10ns -pulse_always
add_clock 1 i_ao_rst_n
add_clock 1 i_global_rst_n

if {[file exists ./local_scan_mode.do]} {
    dof ./local_scan_mode.do
}
if {[file exists ./local_constraints.do]} {
    dof ./local_constraints.do
}
set_split_capture on
set_current_mode ${mode} -type internal
set_capture_timing_options -mode_type internal -capture_clock_period "[expr ${tck_period_ns}*${cap_period_factor}]ns"
set_load_unload_timing_options         \
    -usage ssn                         \
    -shift_clock_period             20 \
    -ssn_bus_clock_period           10 \
    -scan_en_setup_extra_cycles     2  \
    -scan_en_hold_extra_cycles      2  \
    -edt_update_setup_extra_cycles  2  \
    -edt_update_hold_extra_cycles   2
set_ijtag_retargeting_options -tck_period ${tck_period_ns}ns

# Outputs of imc_bank are isolated to 0
add_black_boxes -modules imc_bank 0
add_black_boxes -auto

set_core_instance_parameters -instrument_type occ -parameter_values "capture_window_size 3 fast_capture_mode $fc"
report_core_instance_parameters
set_system_mode analysis
report_static_dft_signal_settings
set_fault_type ${ft}
add_faults -all
if {$PROD} {
    set_atpg_limits off
} else {
    set_atpg_limit -pattern_count 50
}
create_pattern
if {$PROD} {
    order_patterns -remove on
}
report_statistics  -detailed_analysis -threshold 0.01
if {$PROD == 0} {
    set_chain_test -suppress_capture on -type nomask
}
write_tsdb_data -replace -pattern_id $pat_id
catch {
    set rpt_dir [get_tsdb_output_directory]/rpt_${ft}
    file mkdir $rpt_dir
    report_clocks                        > ${rpt_dir}/clocks.rpt
    report_input_constraints             > ${rpt_dir}/input_constraints.rpt
    report_primary_inputs                > ${rpt_dir}/primary_inputs.rpt
    report_procedures -expand_iprocs     > ${rpt_dir}/procedures_expanded.rpt
    report_procedures                    > ${rpt_dir}/procedures.rpt
    report_timeplates                    > ${rpt_dir}/timeplates.rpt
    report_core_parameters               > ${rpt_dir}/core_parameters.rpt
    report_core_instances                > ${rpt_dir}/core_instances.rpt
    report_core_instance_parameters      > ${rpt_dir}/core_instance_parameters.rpt
    report_load_unload_timing_options    > ${rpt_dir}/load_unload_timing_options.rpt
    report_scan_cells                    > ${rpt_dir}/scan_cells.rpt
    report_drc_rules -verbose -all_fails > ${rpt_dir}/drc_rules.rpt
    report_patterns                      > ${rpt_dir}/patterns.rpt
    report_ssn_configuration             > ${rpt_dir}/ssn_configuration.rpt
    report_false_paths                   > ${rpt_dir}/false_paths.rpt
    report_multicycle_paths              > ${rpt_dir}/multicycle_paths.rpt
    report_atpg_constraints              > ${rpt_dir}/atpg_constraints.rpt

    write_procfile ${rpt_dir}/procfile.rpt -expand_iprocs -replace
    ax_redirect ${rpt_dir}/iprocs.rpt "ax_report_iprocs ${block}"
    report_drc_rules -verbose -all_fails > ${rpt_dir}/drc_rules.rpt
}
catch {
    set dbg_dir [get_tsdb_output_directory]/dbg_${ft}
    file mkdir $dbg_dir
    write_icl $dbg_dir/${block}.icl -replace
    write_core_description $dbg_dir/${block}.tcd -replace
    write_pdl $dbg_dir/${block}.pdl -replace
    write_procfile $dbg_dir/${block}.testproc -replace
    write_flat_model $dbg_dir/${block}.flat.gz -replace
}

set odir [get_tsdb_output_directory]/pat
set param_list {SIM_COMPARE_SUMMARY 1 SIM_CHANGE_PATH 1 SIM_CLOCK_MONITOR 0 SIM_TIMEPLATE_COMM 1 SIM_VECTOR_COMM 1}
file mkdir $odir

set_pattern_filtering -clock_sequence -sample_per_type 2
report_patterns > $odir/filtered_patterns.rpt

set formats [list -v v  ]

catch {
    foreach {format ext} $formats {
        write_patterns $odir/${block}_filtered_patterns_${ft}_scan_par.${ext}                -parallel  -pattern_set scan                                   ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_scan_ser.${ext}                -serial    -pattern_set scan                                   ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_full_ser.${ext}                -serial                                                        ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_ssh_loopback.${ext}                       -pattern_set ssh_loopback                           ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_ssh_loopback_scan_ser.${ext}              -pattern_set ssh_loopback -scan                     ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_ssn_continuity_ser.${ext}                 -pattern_set ssn_continuity                         ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_ssn_setup_ser.${ext}                                                        -ssn_setup only   ${format} -replace -param_list $param_list -verbose
        write_patterns $odir/${block}_filtered_patterns_${ft}_chain_ser.${ext}               -serial    -pattern_set chain                                  ${format} -replace -param_list $param_list -verbose
    }
}

exit
