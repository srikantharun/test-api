# Settings
set DESIGN            lpddr_p
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
#read_mem_libs
set_design_macros DWC_LPDDR5XPHY_ATPG_MODEL VIRL_functiononly DWC_LPDDR5XPHY_VIRL_functiononly _fv


read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_lvt_V2.05/v1.0/ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2/ln05lpe_a00_mc_ra1rwp_hsr_lvt_1536x78m4b4c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_rvt_V2.05/v1.0/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1536x39m4b4c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_rvt_V2.05/v1.0/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x8m4b2c1r2/ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x8m4b2c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_lvt_V2.05/v1.0/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x56m4b4c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_ra1_hs_lvt_V2.05/v1.0/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2/ln05lpe_a00_mc_ra1rp_hsr_lvt_1024x72m4b4c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf2_hs_rvt_V2.05/v1.0/ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2/ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x128m1b4c1r2.mdt
read_cell_library /data/foundry/samsung/sf5a/memory/samsung/generated/ln05lpe_a00_memory_compiler_rf1_hs_rvt_V2.05/v1.0/ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2/ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2.mdt

read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_pbk_lvt_c54_a00_V2.10/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_pbk_lvt_c54l08/ln05lpe_sc_s6t_pbk_lvt_c54l08.mdt
read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_pbk_rvt_c54_a00_V4.11/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_pbk_rvt_c54l08/ln05lpe_sc_s6t_pbk_rvt_c54l08.mdt
read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_pbk_rvt_c54_a00_V4.11/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_pbktg_rvt_c54l08/ln05lpe_sc_s6t_pbktg_rvt_c54l08.mdt
read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_pbk_rvt_c54_a00_V3.00/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_pbk_rvt_c54l08/ln05lpe_sc_s6t_pbk_rvt_c54l08.mdt
read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_flk_slvt_c54_a00_V4.11/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_flk_slvt_c54l08/ln05lpe_sc_s6t_flk_slvt_c54l08.mdt
read_cell_library /data/foundry/samsung/sf5a/std_cell/samsung/ln05lpe_sc_s6t_elk_lvt_c54_a00_V3.11/FE-Common/ATPG/FastScan/ln05lpe_sc_s6t_elk_lvt_c54l08/ln05lpe_sc_s6t_elk_lvt_c54l08.mdt

read_verilog /home/projects_2/workspace/fkih/europa_lpddr_sdc/hw/impl/europa/blocks/lpddr/dft/atpg/lpddr_p_compile.v

read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../acx2_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyacx2_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../ckx2_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyckx2_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../cmosx2_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphycmosx2_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../csx2_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphycsx2_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../dx4_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphydx4_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../dx5_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphydx5_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../master_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphymaster_top_ew.v
read_verilog /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a/../../zcal_ew/Latest/gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyzcal_top_ew.v

set RELEASE_DIR /home/projects_2/workspace/fkih/europa_lpddr_sdc/hw/impl/europa/blocks/lpddr/dft/atpg/20250109_LP5_IP_ATPG_FILE_V1_00a/

## HArd Macro atpg_model list 
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_acx2_ew.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rxdca.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_core.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_atpg.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_cal_SR.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxac_ew.v
read_verilog $RELEASE_DIR/acx2_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyacx2_top_ew.v
##
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_acx2_ew.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rxdca.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_atpg.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_core.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_cal_SR.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxac_ew.v
read_verilog $RELEASE_DIR/ckx2_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyckx2_top_ew.v
##
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_por_ew.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxcmos_ew.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_decoder3to8.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_vregvsh_vref_mux.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rxacvref_vref_dec_analog.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_mux64.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_mux8.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_rxacvref_ew.v
read_verilog $RELEASE_DIR/cmosx2_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphycmosx2_top_ew.v
##
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_csx2_ew.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rxdca.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_core.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_atpg.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_cal_SR.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxcs_ew.v
read_verilog $RELEASE_DIR/csx2_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphycsx2_top_ew.v
##
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_dx4_ew.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxdq_ew.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxdqs_ew.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_rxreplica_ew.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lcdl_ew.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rptx2.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rxdca.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_atpg.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_core.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_cal_SR.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/dx4_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphydx4_top_ew.v
##
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_dx5_ew.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxdq_ew.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_txrxdqs_ew.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_rxreplica_ew.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_rxdca.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lcdl_ew.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_atpg.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_core.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_lcdl_cal_SR.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/dx5_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphydx5_top_ew.v
##
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_ato_pll_ew.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../include/techrevision.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_techrevision.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_pclk_master.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_phy_pll_ns.v
read_verilog $RELEASE_DIR/master_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphymaster_top_ew.v
##
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../common_files/define.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpllogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/atpg_primitives.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpslogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/sa05nxpvlogl08hdd060f_A00.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_stdcells_HM_models.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../behavior/dwc_lpddr5xphy_rtl_syn_stdlib.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_ato_ew.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_zcalio_ew.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../include/dwc_lpddr5xphy_lstx_zcal_ew.v
read_verilog $RELEASE_DIR/zcal_ew/1.00a/atpg/tetramax/common_files/../../../gate_level_netlist/13M_4Mx_7Dx_2Iz_LB/dwc_lpddr5xphyzcal_top_ew.v

#todo, check why we don't have the model of this cell ?
read_verilog dwc_lpddr5xphy_pclk_rptx1.v

open_tsdb /data/releases/europa/dft/bronze/lpddr/202412041032/tsdb/memory_test/tsdb_outdir/
open_tsdb /data/releases/europa/dft/bronze/lpddr/202412041032/tsdb/logic_test/tsdb_outdir/

#hand written snps occ tcd
read_core_descriptions snps_occ_tcd/dwc_lpddr5xphymaster_top_ew_dwc_lpddr5xphy_occ_ctrl_0.tcd

read_design snps_ddr_subsystem -no_hdl -design_id rtl1
read_design lpddr_p -no_hdl -design_id rtl2

set_module_matching_options -module_name_map_list { lpddr_p_rtl2_tessent_edt_c1_int lpddr_p_lpddr_p_rtl2_tessent_edt_c1_int_0 
                                                    lpddr_p_rtl2_tessent_edt_cx     lpddr_p_lpddr_p_rtl2_tessent_edt_cx_0
                                                    lpddr_p_rtl2_tessent_occ lpddr_p_lpddr_p_rtl2_tessent_occ_0
                                                    lpddr_p_rtl2_tessent_occ lpddr_p_lpddr_p_rtl2_tessent_occ_1
						    
}

set_current_design lpddr_p

add_core_instances -module lpddr_p_lpddr_p_rtl2_tessent_edt_c1_int_0
add_core_instances -module lpddr_p_lpddr_p_rtl2_tessent_occ_0
add_core_instances -module lpddr_p_lpddr_p_rtl2_tessent_occ_1
 
#add_core_instances -module dwc_lpddr5xphymaster_top_ew_dwc_lpddr5xphy_occ_ctrl_0

report_core_instance_parameters

add_black_boxes -auto

#set_procfile proc
set_static_dft_signal_values async_set_reset_static_disable 1


add_clock 0 i_lpddr_clk    -period 1ns   -pulse_always
add_clock 0 i_ao_clk	   -period 100ns -pulse_always
add_clock 1 i_global_rst_n
add_clock 1 i_ao_rst_n

#These are quick hacks, need to be programmed with a proper test proc
add_primary_inputs  lpddr_p_rtl2_tessent_tdr_scan_mode_inst/ijtag_data_out  -pseudo_port_name  ijtag_data_out
add_input_constraints ijtag_data_out  -c1 
add_primary_inputs lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst/ijtag_data_out_0_latch_reg/Q -pseudo_port_name ijtag_data_out_0_latch_reg
add_input_constraints ijtag_data_out_0_latch_reg -c1
add_primary_inputs lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst/ijtag_data_out_0_latch_reg/Q -pseudo_port_name tdr_scan_shift_cg
add_input_constraints tdr_scan_shift_cg -c1
add_primary_inputs u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_sib_sti_inst/ijtag_to_reset -pseudo_port_name ijtag_to_reset
add_input_constraints ijtag_to_reset -c1 

#These are needed to allow tracing of snps occ chains
set N_occs [sizeof_collection [get_instances -hierarchical *u_occ_ctrl]]
set snps_occs  [get_instances -hierarchical *u_occ_ctrl]
foreach_in_collection inst $snps_occs {
     echo [get_name_list $inst] >> rpt/snps_occs.rpt
}
for {set i 0} {$i < $N_occs} {incr i} { 
add_primary_inputs [get_name_list [index_collection $snps_occs $i]]/u_slow_gate/insts0/inst0/q  -pseudo_port_name snps_occ_slow_gate_$i
add_input_constraints snps_occ_slow_gate_$i -c1

add_primary_inputs [get_name_list [index_collection $snps_occs $i]]/u_clkand2/X  -pseudo_port_name snps_occ_clkand2_$i
add_input_constraints snps_occ_clkand2_$i -c0

}


set_static_dft_signal_values int_ltest_en 1
set_static_dft_signal_values int_edt_mode 1
set_static_dft_signal_values int_mode 1
set_static_dft_signal_values ext_edt_mode 0
#set_static_dft_signal_values tck_occ_en   1

set_drc_handling t24 warn
set_system_mode analysis
report_static_dft_signal_settings

report_scan_cells > rpt/scan_cells.rpt
report_drc_rules -verbose -all_fails > rpt/drc_rules.rpt

set_pattern_type -sequential 2

#temp fix
set_contention_check off -atpg 

create_pattern
report_patterns > pat.rpt
write_tsdb_data -repl

if ![file isdirectory pattern] {
  file mkdir pattern
}

write_pattern ./pattern/ai_core_pattern_sa.ser.v -verilog -serial -parameter_list {SIM_TOP_NAME TB SIM_INSTANCE_NAME DUT_inst} -repl
#exit
