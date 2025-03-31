##########################################################################################
# Script: sdc_gen_atspeed.tcl
#
# Description: PT script to process DFT constraints for noc_h_north.
#              Script is for advanced users only. For more info contact maintainer.
#
#              atspeed mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN noc_h_north_p
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

read_verilog /data/europa/pd/noc_h_north_p/block_build/dev_0p9/build/fc/compile/results/noc_h_north_p.mapped.v.gz 

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/noc_h_north_p_atspeed_port_clocks.tcl 
    set i_clk [get_attribute -objects [get_ports i_noc_clk] -name clocks]

    #usually these clocks are asynchronous, please check your partition
    set_clock_groups -asynchronous -name clk_1 -group [get_clocks {aic_4_clk}] -group [get_clocks {aic_5_clk}] -group [get_clocks {aic_6_clk}] -group [get_clocks {aic_7_clk}] -group [get_clocks {aic_4_aon_clk}] -group [get_clocks {aic_5_aon_clk}] -group [get_clocks {aic_6_aon_clk}] -group [get_clocks {aic_7_aon_clk}] -group [get_clocks {l2_4_clk}] -group [get_clocks {l2_5_clk}] -group [get_clocks {l2_6_clk}] -group [get_clocks {ijtag_tck}] -group [get_clocks {l2_7_clk}] -group [get_clocks {test_clk}]

    #reset signals are static in scan mode
    set_false_path -from [get_ports i_aic_4_aon_rst_n]
    set_false_path -from [get_ports i_aic_4_rst_n]
    set_false_path -from [get_ports i_aic_5_aon_rst_n]
    set_false_path -from [get_ports i_aic_5_rst_n]
    set_false_path -from [get_ports i_aic_6_aon_rst_n]
    set_false_path -from [get_ports i_aic_6_rst_n]
    set_false_path -from [get_ports i_aic_7_aon_rst_n]
    set_false_path -from [get_ports i_aic_7_rst_n]
    set_false_path -from [get_ports i_l2_4_aon_rst_n]
    set_false_path -from [get_ports i_l2_4_rst_n]
    set_false_path -from [get_ports i_l2_5_aon_rst_n]
    set_false_path -from [get_ports i_l2_5_rst_n]
    set_false_path -from [get_ports i_l2_6_aon_rst_n]
    set_false_path -from [get_ports i_l2_6_rst_n]
    set_false_path -from [get_ports i_l2_7_aon_rst_n]
    set_false_path -from [get_ports i_l2_7_rst_n]
    set_false_path -from [get_ports i_noc_rst_n]

    source /data/releases/europa/dft/bronze/noc_h_north/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/noc_h_north_p_rtl2.dft_inserted_design/noc_h_north_p.hierfix.sdc 

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_noc_clk] -name clocks]
    set tessent_clock_mapping(i_noc_clk) $i_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck

    set_case_analysis 1 [get_ports test_mode]
    set_case_analysis 0 [get_ports scan_en]
    set_case_analysis 0 [get_ports edt_update]
    
    tessent_set_ltest_modal_edt_fast_capture
    
    # if partition has memories, read mbist sdc as well
    tessent_set_ijtag_non_modal

} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsAtspeed.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsAtspeed.sdc

exit
