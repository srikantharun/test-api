# Settings
set DESIGN            pcie_p
set DESIGN_ID         rtl2
set GENERATION        1
set USE_MBIST_TSDB    1
set USE_PREPROCESSING 0
set BLACKBOXES        { }

set_context pattern -scan

dofile ../tessent_setup.tcl

# Tech lib
read_cell_library ${GIT_ROOT}/hw/impl/europa/dft/libs/*
read_cell_library ${SF5A_TECH_CELL_LIBS}
# Mem lib
read_mem_libs

read_verilog /data/europa/pd/pcie_p/block_build/dev_dft2/build/fc/compile/results/pcie_p.insert_dft.v
#read_verilog /home/projects_2/workspace/fkih/europa_lpddr_sdc/hw/impl/europa/blocks/pcie/dft/scanpro/tsdb_outdir/dft_inserted_designs/pcie_p_gate.dft_inserted_design/pcie_p.vg
read_verilog /data/foundry/samsung/sf5a/ip/synopsys/dwc_pcie4phy_sssf5a_x4ns/2.01a/pma/atpg/13M_4Mx_7Dx_2Iz_LB/models/dwc_c20pcie4_pma_x4_ns_scan.v

open_tsdb /data/releases/europa/dft/bronze/pcie/202412070934/tsdb/memory_test/tsdb_outdir
open_tsdb /data/releases/europa/dft/bronze/pcie/202412070934/tsdb/logic_test/tsdb_outdir

read_design pcie_p -no_hdl -design_id rtl2
read_design DWC_pcie_subsystem -no_hdl -design_id rtl1

set_module_matching_options -module_name_map_list { pcie_p_rtl2_tessent_edt_c1_int pcie_p_pcie_p_rtl2_tessent_edt_c1_int_0 
                                                    pcie_p_rtl2_tessent_edt_cx     pcie_p_pcie_p_rtl2_tessent_edt_cx_0 
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_0
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_1
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_2
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_3
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_4
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_5
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_6
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_7
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_8
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_9
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_10
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_11
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_12
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_13
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_14
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_15
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_16
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_17
                                                    pcie_p_rtl2_tessent_occ pcie_p_pcie_p_rtl2_tessent_occ_18

}

add_core_instances -module pcie_p_pcie_p_rtl2_tessent_edt_c1_int_0 

report_core_instance_parameters

add_black_boxes -auto

#set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1

add_clocks 1 i_global_rst_n 
add_clocks 1 i_ao_rst_n

add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_0
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_1
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_2
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_3
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_4
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_5
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_6
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_7
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_8
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_9
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_10
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_11
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_12
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_13
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_14
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_15
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_16
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_17
add_core_instances -module pcie_p_pcie_p_rtl2_tessent_occ_18

add_primary_inputs pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/ate_test_mode_latch_reg/Q -pseudo_port_name ate_test_mode_latch_reg
add_input_constraints ate_test_mode_latch_reg -c0

add_primary_inputs pcie_p_rtl2_tessent_tdr_phy0_scan_clk_sel_inst/ijtag_data_out_0_latch_reg/Q -pseudo_port_name ijtag_data_out_0_latch_reg
add_input_constraints ijtag_data_out_0_latch_reg -c1

add_primary_inputs pcie_p_rtl2_tessent_tdr_sri_ctrl_inst/int_mode_latch_reg/Q -pseudo_port_name int_mode_latch_reg
add_input_constraints int_mode_latch_reg -c1


set_drc_handling t24 warn
set_system_mode analysis
report_static_dft_signal_settings

report_scan_cells > rpt/scan_cells.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt

set_pattern_type -sequential 2

create_pattern
report_patterns > pat.rpt
write_tsdb_data -repl

if ![file isdirectory pattern] {
  file mkdir pattern
}

write_pattern ./pattern/pcie_pattern_sa.ser.v -verilog -serial -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl
#exit
