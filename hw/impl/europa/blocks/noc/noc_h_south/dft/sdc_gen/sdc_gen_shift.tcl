##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for noc_h_south.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN noc_h_south_p
set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]
source ${GIT_ROOT}/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

set glob_paths {}
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*c54/*/FE-Common/LIBERTY/*/*c54l08_tt_nominal_max_0p7500v_125c.db_ccs_tn_lvf"
set link_paths {}
foreach glob_path $glob_paths {
    lappend link_paths [glob $glob_path]
}

set_app_var link_path "* [join $link_paths]"

read_verilog /data/europa/pd/noc_h_south_p/block_build/dev_rtl1p0_fixed_constraints/build/fc/compile/results/noc_h_south_p.insert_dft.v.gz 

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev_noc_h_south_p_rtl_v1p0/export/clocks/noc_h_south_p_shift_port_clocks.tcl 
    #test_clk will be defined by tessent sdc
    remove_clock test_clk

    source /data/releases/europa/dft/bronze/noc_h_south/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/noc_h_south_p_rtl2.dft_inserted_design/noc_h_south_p.hierfix.sdc 
    
    #call the proper TCL procs for scan shift mode
    
    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    
    tessent_set_ltest_modal_shift
   
    set_clock_groups -asynchronous -name clk_1 \
     -group [get_clocks {tessent_test_clock aic_0_aon_clk aic_0_clk aic_1_aon_clk aic_1_clk aic_2_aon_clk aic_2_clk aic_3_aon_clk aic_3_clk l2_0_aon_clk l2_0_clk l2_1_aon_clk l2_1_clk l2_2_aon_clk l2_2_clk l2_3_aon_clk l2_3_clk noc_clk}] -group [get_clocks {ijtag_tck}]

    #add case analysis on scan shift and test mode
    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 1 [get_ports scan_en]
} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsShift.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsShift.sdc

exit
