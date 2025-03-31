##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for dcd.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN dcd_p
set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]
source ${GIT_ROOT}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

set glob_paths {}
foreach mem_lib [split $MEM_LIBS_PATH$REG_FILES_PATH " "] {
    if { $mem_lib == "" } {
        # Trailing whitespace, skip
        continue
    }
    lappend glob_paths "${mem_lib}/fusion_ref_library/*"
}
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*c54/*/FE-Common/LIBERTY/*/*c54l08_tt_nominal_max_0p7500v_125c.db_ccs_tn_lvf"
set link_paths {}
foreach glob_path $glob_paths {
    lappend link_paths [glob $glob_path]
}

set_app_var link_path "* [join $link_paths]"

read_verilog /data/europa/pd/dcd_p/block_build/dev_bronze5_run2/build/fc/compile/results/dcd_p.insert_dft.v.gz
read_verilog /data/europa/pd/alg_core_wrapper/block_build/dev_bronze5_run2/build/fc/compile/results/alg_core_wrapper.insert_dft.v.gz

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_shift_port_clocks.tcl
    #ssn_clk will be defined by tessent sdc
    remove_clock ssn_clk
    
    source /data/releases/europa/dft/bronze/dcd/202412101306/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/dcd_p_rtl2.dft_inserted_design/dcd_p.hierfix.sdc
    
    #call the proper TCL procs for scan shift mode
    
    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    
    tessent_set_ltest_modal_shift

    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set i_mcu_clk [get_attribute -objects [get_ports i_mcu_clk] -name clocks]
    get_clocks "tessent_ssn_bus_clock_network [get_object_name ${i_clk}] [get_object_name ${i_mcu_clk}]"
    set sync_clock_list [list tessent_ssn_bus_clock_network $i_clk $i_mcu_clk]
    set_clock_groups -asynchronous -name clk_1 -group [get_clocks $sync_clock_list ] -group [get_clocks {ijtag_tck}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]

    # force occ clk mux selector to 1
    set_case_analysis 1 [get_pins -hier test_mode_reg/Q]
    
} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsShift.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsShift.sdc

exit
