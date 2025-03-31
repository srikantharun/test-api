set DESIGN pcie_p
set mbist_sdc 0
set atspeed_sdc 0
set shift_sdc 1

set MEM_IP ${DESIGN}
set GIT_ROOT [exec git rev-parse --show-toplevel]
source /home/projects_2/workspace/fkih/europa_lpddr_dft3/hw/ip/tech_cell_library/default/rtl/sf5a/tc_mbist_techlib.tcl

set glob_paths {}
foreach mem_lib [split $MEM_LIBS_PATH$REG_FILES_PATH " "] {
    if { $mem_lib == "" } {
        # Trailing whitespace, skip
        continue
    }
    lappend glob_paths "${mem_lib}/fusion_ref_library/*"
}
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/s6t/*/*c54/*/FE-Common/LIBERTY/*/*c54l08_tt_nominal_max_0p7500v_125c.db_ccs_tn_lvf"
lappend glob_paths "/data/foundry/samsung/sf5a/ip/synopsys/generated/v1.0/fusion_ref/pma/dwc_c20pcie4_pma_x4_ns_us_GlobalRvia_MOL_nominal_detailed"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/ln05lpe_sc_s6t_flkp_rvt_c54l08_physical_only"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.11/ln05lpe_sc_s6t_flkp_lvt_c54l08_c"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_ra1rp_hsr_rvt_2560x16m4b4c1r2/fusion_ref_library/ln05lpe_a00_mc_ra1rp_hsr_rvt_2560x16m4b4c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_512x12m1b8c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_512x12m1b8c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/ln05lpe_sc_s6t_flkp_rvt_c54l08_c"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_elk_rvt_c54_a00_V2.01/ln05lpe_sc_s6t_elk_rvt_c54l08_c"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x120m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x120m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x124m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x124m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf1_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf1rp_hsr_rvt_264x136m2b1c1r2/fusion_ref_library/ln05lpe_a00_mc_rf1rp_hsr_rvt_264x136m2b1c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.11/ln05lpe_sc_s6t_flkp_lvt_c54l08_physical_only"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x144m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x144m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x148m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x148m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x88m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_64x88m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x84m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x84m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x116m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x116m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x104m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x104m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_vrom_hd_lvt_V2.02/v1.0/ln05lpe_a00_mc_vromp_hd_lvt_20480x16m32b8c1/fusion_ref_library/ln05lpe_a00_mc_vromp_hd_lvt_20480x16m32b8c1_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_elk_lvt_c54_a00_V2.01/ln05lpe_sc_s6t_elk_lvt_c54l08_c"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x160m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x160m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_260x128m1b8c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_260x128m1b8c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_356x140m1b8c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_356x140m1b8c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_284x132m1b8c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_284x132m1b8c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.03/v1.0/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x136m1b2c1r2/fusion_ref_library/ln05lpe_a00_mc_rf2rp_hsr_rvt_32x136m1b2c1r2_c_lvf_dth"
lappend glob_paths "/data/foundry/samsung/sf5a/ip/synopsys/generated/v1.0/fusion_ref/pma/dwc_c20pcie4_pma_x4_ns_us_GlobalRvia_MOL_nominal_detailed"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.11/ln05lpe_sc_s6t_flk_lvt_c54l08_c"
lappend glob_paths "/data/foundry/samsung/sf5a/std_cell/samsung/generated/v1.0/fusion_ref/ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10/ln05lpe_sc_s6t_flk_rvt_c54l08_c"

set link_paths {}
foreach glob_path $glob_paths {
    lappend link_paths [glob $glob_path]
}


set_app_var link_path "* [join $link_paths]"

#read_verilog /home/projects_2/workspace/fkih/europa_pcie3/hw/impl/europa/blocks/pcie/dft/sdc/rel_ss2_dft1_0.1v_06Nov24/NETLIST/pcie_p.v.gz
#read_verilog /data/europa/pd/pcie_p/block_build/dev_dft/build/fc/compile/results/pcie_p.insert_dft.v
#read_verilog /data/europa/pd/pcie_p/block_build/dev_dft_AM/build/fc/compile/results/pcie_p.insert_dft.v
#read_verilog /data/europa/pd/pcie_p/block_build/dev_dft2/build/fc/compile/results/pcie_p.insert_dft.v
#read_verilog /data/foundry/samsung/sf5a/ip/synopsys/pcie/20241219_hd1p5/rel_hd1.5_DFT_prel_pcie_p_ss_18Dec2024/HD1.5_DFT2_RTL/netlist/pcie_p.v.gz
read_verilog /home/projects_2/workspace/fkih/europa_pcie3/hw/impl/europa/blocks/pcie/dft/sdc/rel_SS3_DFT2v0.2_25Dec2024/NETLIST/pcie_p.v.gz

link_design pcie_p

source /data/releases/europa/dft/bronze/pcie/202412070934/tsdb/logic_test/tsdb_outdir/dft_inserted_designs/pcie_p_rtl2.dft_inserted_design/pcie_p.hierfix.sdc.snps
#source pcie_p.sdc

#set_case_analysis 1 [get_pins -hier */MCS[0]]
#set_case_analysis 0 [get_pins -hier */MCS[1]]
#set_case_analysis 1 [get_pins -hier */ADME[2]]
#set_case_analysis 0 [get_pins -hier */ADME[1]]
#set_case_analysis 0 [get_pins -hier */ADME[0]]
#set_case_analysis 0 [get_pins -hier */PDE]

set sdc_write_unambiguous_names false

if { $mbist_sdc == "1" } {
#set CONSTR_DIR /home/projects_2/workspace/fkih/pcie_silver/hw/impl/europa/blocks/pcie/synth-rtla/constraints/
#source -e /home/projects_2/workspace/fkih/pcie_silver/hw/impl/europa/blocks/pcie/synth-rtla/constraints/pcie_p_constraints.tcl

set i_pcie_init_mt_axi_clk_period                [expr 1.67]
set i_pcie_targ_mt_axi_clk_period                [expr 1.67]
set i_pcie_targ_cfg_dbi_axi_clk_period           [expr 10]
set i_pcie_aux_clk_period                        [expr 10]
set i_apb_pclk_period                            [expr 10]
set i_ref_alt_clk_p_period                       [expr 10]
set i_ref_clk_period                             [expr 10]
set tck_period                                   [expr 10]

create_clock [get_ports {i_pcie_init_mt_axi_clk}]      -name i_pcie_init_mt_axi_clk      -period $i_pcie_init_mt_axi_clk_period      -waveform [list 0 [expr $i_pcie_init_mt_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_targ_mt_axi_clk}]      -name i_pcie_targ_mt_axi_clk      -period $i_pcie_targ_mt_axi_clk_period      -waveform [list 0 [expr $i_pcie_targ_mt_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_targ_cfg_dbi_axi_clk}] -name i_pcie_targ_cfg_dbi_axi_clk -period $i_pcie_targ_cfg_dbi_axi_clk_period -waveform [list 0 [expr $i_pcie_targ_cfg_dbi_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_aux_clk}]              -name i_pcie_aux_clk              -period $i_pcie_aux_clk_period       -waveform [list 0 [expr $i_pcie_aux_clk_period*0.5]] 
create_clock [get_ports {i_apb_pclk}]                  -name i_apb_pclk                  -period $i_apb_pclk_period                  -waveform [list 0 [expr $i_apb_pclk_period*0.5]] 
create_clock [get_ports {i_ref_alt_clk_p}]             -name i_ref_alt_clk_p             -period $i_ref_alt_clk_p_period             -waveform [list 0 [expr $i_ref_alt_clk_p_period*0.5]] 
create_clock [get_ports {i_ref_clk}]                   -name i_ref_clk                   -period $i_ref_clk_period                   -waveform [list 0 [expr $i_ref_clk_period*0.5]] 
create_clock [get_ports {tck}]                         -name "phy0_jtag_clk"     -period $tck_period
create_clock [get_ports {bisr_clk}]                    -name "bisr_clk"   -period $tck_period
create_clock -name phy0_mplla_ana_word_clk_i -period 1 -waveform { 0 0.5 } [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_ana_word_clk_i}]
create_generated_clock -name phy0_mplla_dword_clk_i -source [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_ana_word_clk_i}]  -divide_by 2  -add -master_clock [get_clocks {phy0_mplla_ana_word_clk_i}] [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_dword_clk_i}] 

set mac_scan_coreclk_period 2.0
create_clock -name mac_scan_coreclk  -period $mac_scan_coreclk_period  [get_pins u_pcie_subsys/u_pcie_ctrl_top_0/mac_scan_coreclk]
create_clock [get_ports {tck}]                         -name "tck"     -period $tck_period

tessent_set_default_variables
set_ijtag_retargeting_options -tck_period 10.0

  array set tessent_clock_mapping {
    tessent_bisr_clock_bisr_clk bisr_clk
    ts_tck_tck phy0_jtag_clk
    ck0 phy_fw_clk
    ck1 phy_fw_clk
    ck2 mac_scan_coreclk
    i_pcie_init_mt_axi_clk i_pcie_init_mt_axi_clk
    i_pcie_targ_mt_axi_clk i_pcie_targ_mt_axi_clk
    scan_atspeed_clk_500 phy0_mplla_ana_word_clk_i
  }


tessent_set_non_modal off
set_cell_mode NORMAL u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma
remove_generated_clock u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/*
write_sdc -nosplit pcie_p.mbist.sdc
}

if { $atspeed_sdc == "1" } {

tessent_set_default_variables
set_ijtag_retargeting_options -tck_period 10.0

set i_pcie_init_mt_axi_clk_period                [expr 1.67]
set i_pcie_targ_mt_axi_clk_period                [expr 1.67]
set i_pcie_targ_cfg_dbi_axi_clk_period           [expr 10]
set i_pcie_aux_clk_period                        [expr 10]
set i_apb_pclk_period                            [expr 10]
set i_ref_alt_clk_p_period                       [expr 10]
set i_ref_clk_period                             [expr 10]
set tck_period                                   [expr 10]

create_clock [get_ports {i_pcie_init_mt_axi_clk}]      -name i_pcie_init_mt_axi_clk      -period $i_pcie_init_mt_axi_clk_period      -waveform [list 0 [expr $i_pcie_init_mt_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_targ_mt_axi_clk}]      -name i_pcie_targ_mt_axi_clk      -period $i_pcie_targ_mt_axi_clk_period      -waveform [list 0 [expr $i_pcie_targ_mt_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_targ_cfg_dbi_axi_clk}] -name i_pcie_targ_cfg_dbi_axi_clk -period $i_pcie_targ_cfg_dbi_axi_clk_period -waveform [list 0 [expr $i_pcie_targ_cfg_dbi_axi_clk_period*0.5]] 
create_clock [get_ports {i_pcie_aux_clk}]              -name i_pcie_aux_clk              -period $i_pcie_aux_clk_period       -waveform [list 0 [expr $i_pcie_aux_clk_period*0.5]] 
create_clock [get_ports {i_apb_pclk}]                  -name i_apb_pclk                  -period $i_apb_pclk_period                  -waveform [list 0 [expr $i_apb_pclk_period*0.5]] 
create_clock [get_ports {i_ref_alt_clk_p}]             -name i_ref_alt_clk_p             -period $i_ref_alt_clk_p_period             -waveform [list 0 [expr $i_ref_alt_clk_p_period*0.5]] 
create_clock [get_ports {i_ref_clk}]                   -name i_ref_clk                   -period $i_ref_clk_period                   -waveform [list 0 [expr $i_ref_clk_period*0.5]] 
create_clock [get_ports {tck}]                         -name "tck"     -period $tck_period
create_clock [get_ports {bisr_clk}]                    -name "bisr_clk"   -period $tck_period
create_clock -name phy0_mplla_ana_word_clk_i -period 1 -waveform { 0 0.5 } [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_ana_word_clk_i}]
create_generated_clock -name phy0_mplla_dword_clk_i -source [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_ana_word_clk_i}]  -divide_by 2  -add -master_clock [get_clocks {phy0_mplla_ana_word_clk_i}] [get_pins {u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/mplla_dword_clk_i}] 

set mac_scan_coreclk_period 2.0
create_clock -name mac_scan_coreclk  -period $mac_scan_coreclk_period  [get_pins u_pcie_subsys/u_pcie_ctrl_top_0/mac_scan_coreclk]
create_clock [get_ports {tck}]                         -name "tck"     -period $tck_period

tessent_set_ltest_modal_edt_fast_capture
tessent_set_memory_bist_non_modal
set_cell_mode SCAN_ASST u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma
remove_generated_clock u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/*
write_sdc -nosplit pcie_p.atspeed.sdc

}

if { $shift_sdc == "1" } {
tessent_set_default_variables
set_ijtag_retargeting_options -tck_period 10.0

tessent_set_ltest_modal_edt_shift
set_cell_mode SCAN u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma
remove_generated_clock u_pcie_subsys/u_pcie_phy_top/u_pcie_pipe/phy0/pma/*
write_sdc -nosplit pcie_p.shift.sdc

}
#tessent_set_ltest_disable
#tessent_set_memory_bist_modal
#tessent_set_ltest_modal_edt_fast_capture
#tessent_set_ltest_modal_edt_shift

#set_case_analysis 1 [get_ports test_mode]
#set_case_analysis 0 [get_ports scan_en]

#report_timing

#write_sdc shift.sdc
#write_sdc atpseed.sdc

#check_timing -verbose > check_timing_shift.rpt
#check_timing -verbose > check_timing_atspeed.rpt
