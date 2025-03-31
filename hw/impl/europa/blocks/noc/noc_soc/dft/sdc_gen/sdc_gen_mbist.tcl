##########################################################################################
# Script: sdc_gen_mbist.tcl
#
# Description: PT script to process DFT constraints for noc_soc.
#              Script is for advanced users only. For more info contact maintainer.
#
#              mbist mode
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
    source /data/europa/pd/europa/constraints/dev_noc_soc_p_0.9/clocks/results/func/noc_soc_p_port_clocks.tcl 
    #test_clk will be defined by tessent sdc
    remove_clock test_clk
##set i_clk [get_attribute -objects [get_ports i_noc_clk] -name clocks]

    #usually these clocks are asynchronous, please check your partition
    set_clock_groups -asynchronous -name clk_1 \
     -group [get_clocks {apu_aon_clk}] \
     -group [get_clocks {apu_clk}] \
     -group [get_clocks {dcd_aon_clk}] \
     -group [get_clocks {dcd_codec_clk}] \
     -group [get_clocks {dcd_mcu_clk}] \
     -group [get_clocks {noc_clk}] \
     -group [get_clocks {pcie_aon_clk}] \
     -group [get_clocks {pcie_init_mt_clk}] \
     -group [get_clocks {pcie_targ_cfg_clk}] \
     -group [get_clocks {pcie_targ_cfg_dbi_clk}] \
     -group [get_clocks {pcie_targ_mt_clk}] \
     -group [get_clocks {pve_0_aon_clk}] \
     -group [get_clocks {pve_0_clk}] \
     -group [get_clocks {pve_1_aon_clk}] \
     -group [get_clocks {pve_1_clk}] \
     -group [get_clocks {soc_mgmt_aon_clk}] \
     -group [get_clocks {soc_mgmt_clk}] \
     -group [get_clocks {sys_spm_aon_clk}] \
     -group [get_clocks {sys_spm_clk}]
    set_clock_groups -physically_exclusive -group [get_clocks {bisr_clk}]

    #reset signals are static in scan mode
    set_false_path -from [get_ports i_apu_aon_rst_n]
    set_false_path -from [get_ports i_apu_rst_n]
    set_false_path -from [get_ports i_dcd_aon_rst_n]
    set_false_path -from [get_ports i_dcd_codec_rst_n]
    set_false_path -from [get_ports i_dcd_mcu_rst_n]
    set_false_path -from [get_ports i_noc_rst_n]
    set_false_path -from [get_ports i_pcie_aon_rst_n]
    set_false_path -from [get_ports i_pcie_init_mt_rst_n]
    set_false_path -from [get_ports i_pcie_targ_cfg_dbi_rst_n]
    set_false_path -from [get_ports i_pcie_targ_cfg_rst_n]
    set_false_path -from [get_ports i_pcie_targ_mt_rst_n]
    set_false_path -from [get_ports i_pve_0_aon_rst_n]
    set_false_path -from [get_ports i_pve_0_rst_n]
    set_false_path -from [get_ports i_pve_1_aon_rst_n]
    set_false_path -from [get_ports i_pve_1_rst_n]
    set_false_path -from [get_ports i_soc_mgmt_aon_rst_n]
    set_false_path -from [get_ports i_soc_mgmt_rst_n]
    set_false_path -from [get_ports i_sys_spm_aon_rst_n]
    set_false_path -from [get_ports i_sys_spm_rst_n]

    source $env(DFT_HOME)/noc_soc/Latest/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/${DESIGN}_rtl2.dft_inserted_design/${DESIGN}.hierfix.sdc

    tessent_set_default_variables
    set_ijtag_retargeting_options -tck_period 10.0

    #Get the name of the clock for i_clk pin from the design
    set tessent_clock_mapping(i_noc_clk) noc_clk
    set tessent_clock_mapping(tessent_bisr_clock_bisr_clk) bisr_clk
    set tessent_clock_mapping(ts_tck_tck) ijtag_tck
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
