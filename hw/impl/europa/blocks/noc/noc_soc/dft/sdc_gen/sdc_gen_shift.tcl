##########################################################################################
# Script: sdc_gen_shift.tcl
#
# Description: PT script to process DFT constraints for noc_soc.
#              Script is for advanced users only. For more info contact maintainer.
#
#              shift mode
#
# Maintainer: <leonidas.katselas@axelera.ai>
#
##########################################################################################

set CHECK_MANUAL_CHANGES 0
set DESIGN noc_soc_p
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

read_verilog /data/europa/pd/noc_soc_p/block_build/dev_v0.9_dft/build/fc/compile/results/noc_soc_p.insert_dft.v.gz 

link_design ${DESIGN}

set_app_var sdc_write_unambiguous_names false

if { $CHECK_MANUAL_CHANGES == 0 } {
    source /data/europa/pd/europa/constraints/dev_noc_soc_p/export/clocks/noc_soc_p_shift_port_clocks.tcl 
    #test_clk will be defined by tessent sdc
    remove_clock test_clk

    source $env(DFT_HOME)/noc_soc/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc
    
    #call the proper TCL procs for scan shift mode
    
    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0
    set tessent_slow_clock_period 10
    
    tessent_set_ltest_modal_shift

    set_clock_groups -asynchronous -name clk_1 \
     -group [get_clocks { apu_clk apu_aon_clk dcd_aon_clk pcie_aon_clk pcie_targ_cfg_clk pcie_targ_cfg_dbi_clk pve_0_aon_clk pve_1_aon_clk soc_mgmt_aon_clk sys_spm_aon_clk soc_mgmt_clk dcd_codec_clk dcd_mcu_clk noc_clk pcie_init_mt_clk pcie_targ_mt_clk pve_0_clk pve_1_clk sys_spm_clk}]
    
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
