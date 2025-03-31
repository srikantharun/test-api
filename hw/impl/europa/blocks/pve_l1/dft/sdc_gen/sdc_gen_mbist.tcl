##########################################################################################
# Script: sdc_gen_mbist.tcl
#
# Description: PT script to process DFT constraints for PVE_L1.
#              Script is for advanced users only. For more info contact maintainer.
#
#              mbist mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN pve_l1_p
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

read_verilog /data/europa/pd/pve_l1_p/block_build/dev_prithivi/build/fc/compile/results/pve_l1_p.insert_dft.v.gz

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev/export/clocks/${DESIGN}_func_port_clocks.tcl
    #test_clk will be defined by tessent sdc
    remove_clock test_clk

    source /data/releases/europa/dft/bronze/pve_l1/202501151329/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set i_clk [get_attribute -objects [get_ports i_clk] -name clocks]
    set tessent_clock_mapping(i_clk) $i_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_ijtag_tck) ijtag_tck
    set tessent_slow_clock_period 10
    set BisrCKPeriod 20

    tessent_set_non_modal off ;# logictest off/on , disable scan logic

    set_case_analysis 0 [get_ports test_mode]
    set_case_analysis 0 [get_ports scan_en]
} else {
    read_sdc ../../synth-rtla/constraints/dft/${DESIGN}.cnsMbist.sdc
}

#sanity check of timing
report_timing

#write sdc
write_sdc -nosplit ${DESIGN}.cnsMbist.sdc

exit
