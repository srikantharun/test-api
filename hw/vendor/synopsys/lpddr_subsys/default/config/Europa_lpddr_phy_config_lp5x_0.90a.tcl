#*****************************************************************************
#
# This file was automatically generated by coreConsultant (version V-2024.03).
#
# FILENAME : /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/lpddr_phy_config_lp5x_0.50a.tcl
# DATE :     July 10, 2024
# ABSTRACT : 
#            Script generated by write_batch_script.  This script
#            was used to capture the coreConsultant workspace 'lpddr5x_phy_0_90'.
#            The command line was:
#                 write_batch_script -include -create_workspace -activities -default_params /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/lpddr_phy_config_lp5x_0.50a.tcl
#
# LICENSES AUTHORIZED: coreConsultant
#
#
#*****************************************************************************
##
# Use this script to create a coreConsultant workspace for the lpddr5x phy version 0.90a. This matches with the release SS3 from snps.

create_workspace -name ss4_phy_release -installation /data/foundry/LIB/synopsys/dwc_ap_lpddr5x_phy_sssf5a/0.90a/installed_coreKit/2.30a
set_design_attribute PreventFilePrefix 0
set_design_attribute PreventMacroPrefix 0

set_activity_parameter SetDesignFileMacroPrefixes DesignPrefix {}; # == default value.
set_activity_parameter SetDesignFileMacroPrefixes FilePrefix {}; # == default value.
set_activity_parameter SetDesignFileMacroPrefixes MacroPrefix {}; # == default value.
autocomplete_activity  SetDesignFileMacroPrefixes
set_configuration_parameter DWC_LPDDR5XPHY_NUM_CHANNELS 2
set_configuration_parameter DWC_LPDDR5XPHY_DTO_ENABLED 0; # == default value.
set_configuration_parameter DWC_LPDDR5XPHY_LBIST_EN 0; # == default value.
set_configuration_parameter DWC_LPDDR5XPHY_PIPE_DFI_CTRL 1
set_configuration_parameter DWC_LPDDR5XPHY_UPF_CTRL 1; # == default value.
set_configuration_parameter DWC_LPDDR5XPHY_POP_ENABLED 0; # == default value.
set_configuration_parameter DWC_LPDDR5XPHY_PCLKCA_RPTR_ENABLED 0; # == default value.
autocomplete_activity SpecifyConfiguration
generate_reports -reports {ComponentConfiguration IO PrimeProfiles}
generate_views -views {IPXACTComponent}

set_tool_root fm_shell -root /opt/synopsys/fm/Q-2019.12-SP2 -64bit
set_tool_root pt_shell -root /opt/synopsys/prime/S-2021.06-SP1 -64bit
set_tool_root vcs -root /opt/synopsys/vcs/S-2021.09-SP1-1
set_tool_root dc_shell -root /opt/synopsys/syn2/S-2021.06-SP1 -64bit
set_tool_root vcstatic -root /opt/synopsys/vc_static/U-2023.03 -64bit
set_tool_root vcsi -root /opt/synopsys/vcs/S-2021.09-SP1-1
set_tool_root spyglass -root /opt/synopsys/vc_static/U-2023.03/SG_COMPAT/SPYGLASS_HOME -64bit

set_activity_parameter TechSetup SearchPath {. /opt/synopsys/syn2/S-2021.06-SP1/libraries/syn /opt/synopsys/syn2/S-2021.06-SP1/minpower/syn /opt/synopsys/syn2/S-2021.06-SP1/dw/syn_ver /opt/synopsys/syn2/S-2021.06-SP1/dw/sim_ver /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/csx2_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/acx2_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/utility_blocks/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/utility_cells/Latest/timing/11M_4Mx_7Dx/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/master_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/ckx2_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/zcal_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/dx4_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/dx5_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/cmosx2_ew/Latest/timing/13M_4Mx_7Dx_2Iz_LB/lib_pg}
set_activity_parameter TechSetup TargetLibrary {}; # == default value.
set_activity_parameter TechSetup LinkLibrary {* dw_foundation.sldb}
set_activity_parameter TechSetup MinLibrary {}; # == default value.
set_activity_parameter TechSetup MilkywayDesignLibrary {}; # == default value.
set_activity_parameter TechSetup TechFileFormat tf; # == default value.
set_activity_parameter TechSetup TechFile {}; # == default value.
set_activity_parameter TechSetup CreateMwDesignOptions {}; # == default value.
set_activity_parameter TechSetup MaxTluPlusFile {}; # == default value.
set_activity_parameter TechSetup MinTluPlusFile {}; # == default value.
set_activity_parameter TechSetup Tech2ItfMap {}; # == default value.
set_activity_parameter TechSetup MaxEmulationTluPlus {}; # == default value.
set_activity_parameter TechSetup MinEmulationTluPlus {}; # == default value.
set_activity_parameter TechSetup MilkywayReferenceLibrary {}; # == default value.
set_activity_parameter TechSetup MilkywayLogic0Net VSS
set_activity_parameter TechSetup MilkywayLogic1Net VDD
set_activity_parameter TechSetup FpgaVendor {}; # == default value.
set_activity_parameter TechSetup FpgaFamily {}; # == default value.
set_activity_parameter TechSetup FpgaDevice {}; # == default value.
set_activity_parameter TechSetup FpgaSpeedGrade {}; # == default value.
set_activity_parameter TechSetup FpgaPackage {}; # == default value.

set_activity_parameter OrientSelect orient_NumAnib 2; # == default value.
set_activity_parameter OrientSelect orient_NumDbyte 4; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_MASTER_ORIENT_NO 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_MASTER_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_MASTER_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_CMOSX2_ORIENT_NO 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_CMOSX2_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_CMOSX2_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_ZCAL_ORIENT_NO 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_ZCAL_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_ZCAL_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_AC_WRAPPER_0_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_AC_WRAPPER_0_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_AC_WRAPPER_1_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_AC_WRAPPER_1_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_0_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_0_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_1_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_1_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_2_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_2_ORIENT_NS 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_3_ORIENT_EW 0; # == default value.
set_activity_parameter OrientSelect DWC_LPDDR5XPHY_DBYTE_WRAPPER_3_ORIENT_NS 0; # == default value.

set_activity_parameter PreMapSetup PreMapFile /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/constraints/ddr_premap_generic.v; # == default value.
set_activity_parameter PreMapSetup ScriptsOnly 0; # == default value.
set_activity_parameter PreMapSetup RunStyle local; # == default value.
set_activity_parameter PreMapSetup RunOptions {}; # == default value.
set_activity_parameter PreMapSetup EmailAddress uytterhoeven; # == default value.

set_activity_parameter SimpleSynthesize DFI_Freq 1067; # == default value.
set_activity_parameter SimpleSynthesize Synthesize 1; # == default value.
set_activity_parameter SimpleSynthesize ScanInsertion 1; # == default value.
set_activity_parameter SimpleSynthesize StaticTimingAnalysis 1; # == default value.
set_activity_parameter SimpleSynthesize FormalVerification 1; # == default value.
set_activity_parameter SimpleSynthesize ScriptsOnly 0; # == default value.
set_activity_parameter SimpleSynthesize RunStyle local; # == default value.
set_activity_parameter SimpleSynthesize RunOptions {}; # == default value.
set_activity_parameter SimpleSynthesize EmailAddress uytterhoeven; # == default value.

set_activity_parameter runCTB_simulate DumpEnabled 1; # == default value.
set_activity_parameter runCTB_simulate DumpFileFormat FSDB; # == default value.
set_activity_parameter runCTB_simulate EnableTCM 0; # == default value.
set_activity_parameter runCTB_simulate UseBlockingHoldJob 1; # == default value.
set_activity_parameter runCTB_simulate designware_home /opt/synopsys/dware/eu001-1.0; # == default value.
set_activity_parameter runCTB_simulate ctb_vip_home {}; # == default value.
set_activity_parameter runCTB_simulate run_test_demo_basic 1; # == default value.
set_activity_parameter runCTB_simulate skip_train 1; # == default value.
set_activity_parameter runCTB_simulate seqCtrl 543; # == default value.
set_activity_parameter runCTB_simulate quickboot 0; # == default value.
set_activity_parameter runCTB_simulate swizzle_dbyte 0; # == default value.
set_activity_parameter runCTB_simulate swizzle_ca 0; # == default value.
set_activity_parameter runCTB_simulate run_test_demo_lp 0; # == default value.
set_activity_parameter runCTB_simulate demo_lp_mode 1; # == default value.
set_activity_parameter runCTB_simulate upf 0; # == default value.
set_activity_parameter runCTB_simulate xprop 0; # == default value.
set_activity_parameter runCTB_simulate firstpstate 0; # == default value.
set_activity_parameter runCTB_simulate fsp_disable 0; # == default value.
set_activity_parameter runCTB_simulate rxpdlight 0; # == default value.
set_activity_parameter runCTB_simulate run_test_demo_dfi_sideband 0; # == default value.
set_activity_parameter runCTB_simulate demo_dfi_sideband_mode 1; # == default value.
set_activity_parameter runCTB_simulate skip_train_sb 1; # == default value.
set_activity_parameter runCTB_simulate seqCtrl_sb 543; # == default value.
set_activity_parameter runCTB_simulate snoop_en 0; # == default value.
set_activity_parameter runCTB_simulate run_test_demo_ate 0; # == default value.
set_activity_parameter runCTB_simulate demo_ate_mode 0; # == default value.
set_activity_parameter runCTB_simulate padlbk 0; # == default value.
set_activity_parameter runCTB_simulate dmem_nz 0; # == default value.
set_activity_parameter runCTB_simulate ate_cust_mb_cfg_file {}; # == default value.
set_activity_parameter runCTB_simulate ate_cust_csr_cfg_file {}; # == default value.
set_activity_parameter runCTB_simulate dram 3; # == default value.
set_activity_parameter runCTB_simulate rank 1; # == default value.
set_activity_parameter runCTB_simulate dfi_mode 3; # == default value.
set_activity_parameter runCTB_simulate data_test 1; # == default value.
set_activity_parameter runCTB_simulate wck_free 1; # == default value.
set_activity_parameter runCTB_simulate csr_bkdoor 0; # == default value.
set_activity_parameter runCTB_simulate bkdoor 0; # == default value.
set_activity_parameter runCTB_simulate jtag 0; # == default value.
set_activity_parameter runCTB_simulate disable_pmu_ecc 0; # == default value.
set_activity_parameter runCTB_simulate freq0 800; # == default value.
set_activity_parameter runCTB_simulate freq_ratio0 2; # == default value.
set_activity_parameter runCTB_simulate datarate0 6400; # == default value.
set_activity_parameter runCTB_simulate pll_bypass0 0; # == default value.
set_activity_parameter runCTB_simulate dm0 0; # == default value.
set_activity_parameter runCTB_simulate wdbi0 0; # == default value.
set_activity_parameter runCTB_simulate rdbi0 0; # == default value.
set_activity_parameter runCTB_simulate pstate1_ctrl 0; # == default value.
set_activity_parameter runCTB_simulate freq1 800; # == default value.
set_activity_parameter runCTB_simulate freq_ratio1 2; # == default value.
set_activity_parameter runCTB_simulate datarate1 6400; # == default value.
set_activity_parameter runCTB_simulate pll_bypass1 0; # == default value.
set_activity_parameter runCTB_simulate dvfsc1 0; # == default value.
set_activity_parameter runCTB_simulate pstate2_ctrl 0; # == default value.
set_activity_parameter runCTB_simulate freq2 800; # == default value.
set_activity_parameter runCTB_simulate freq_ratio2 2; # == default value.
set_activity_parameter runCTB_simulate datarate2 6400; # == default value.
set_activity_parameter runCTB_simulate pll_bypass2 0; # == default value.
set_activity_parameter runCTB_simulate pstate3_ctrl 0; # == default value.
set_activity_parameter runCTB_simulate freq3 800; # == default value.
set_activity_parameter runCTB_simulate freq_ratio3 2; # == default value.
set_activity_parameter runCTB_simulate datarate3 6400; # == default value.
set_activity_parameter runCTB_simulate pll_bypass3 0; # == default value.
set_activity_parameter runCTB_simulate single_ended_type 0; # == default value.
set_activity_parameter runCTB_simulate extra_options {}; # == default value.
set_activity_parameter runCTB_simulate ScriptsOnly 0; # == default value.
set_activity_parameter runCTB_simulate RunStyle local; # == default value.
set_activity_parameter runCTB_simulate RunOptions {}; # == default value.
set_activity_parameter runCTB_simulate EmailAddress uytterhoeven; # == default value.

set_activity_parameter runSpyglass ScriptsOnly 0; # == default value.
set_activity_parameter runSpyglass RunStyle local; # == default value.
set_activity_parameter runSpyglass RunOptions {}; # == default value.
set_activity_parameter runSpyglass GuideWareVersion GuideWare/2021.09; # == default value.
set_activity_parameter runSpyglass RtlListFile /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/src/dwc_lpddr5xphy_top.lst; # == default value.
set_activity_parameter runSpyglass SpyglassAdditionalRtlFiles spyglass/dwc_lpddr5xphy_hardmacro.lst; # == default value.
set_activity_parameter runSpyglass SpyglassLintGoal 1; # == default value.
set_activity_parameter runSpyglass EmailAddress uytterhoeven; # == default value.
set_activity_parameter runSpyglass SpyglassCdcGoal 1; # == default value.
set_activity_parameter runSpyglass SpyglassCdcClockResetIntegrityGoal 1; # == default value.
set_activity_parameter runSpyglass SpyglassCdcAbstractGoal 1; # == default value.
set_activity_parameter runSpyglass SpyglassRdcGoal 1; # == default value.
set_activity_parameter runSpyglass CustomRuleSelection {}; # == default value.

set_activity_parameter runVcSpyglass VcStaticHome /opt/synopsys/vc_static/U-2023.03; # == default value.
set_activity_parameter runVcSpyglass ScriptsOnly 0; # == default value.
set_activity_parameter runVcSpyglass LintEnable 1; # == default value.
set_activity_parameter runVcSpyglass RunStyle local; # == default value.
set_activity_parameter runVcSpyglass RunOptions {}; # == default value.
set_activity_parameter runVcSpyglass CdcEnable 1; # == default value.
set_activity_parameter runVcSpyglass RdcEnable 1; # == default value.
set_activity_parameter runVcSpyglass RcaEnable 0; # == default value.
set_activity_parameter runVcSpyglass AbstractEnable 0; # == default value.
set_activity_parameter runVcSpyglass DwComponentCompileDir {}; # == default value.
set_activity_parameter runVcSpyglass EmailAddress {}; # == default value.
set_activity_parameter runVcSpyglass DwComponentPreCompileEnable 0; # == default value.
set_activity_parameter runVcSpyglass UseBlockingHoldJob 0; # == default value.
set_activity_parameter runVcSpyglass AnalysisMode {}; # == default value.
set_activity_parameter runVcSpyglass AdditionalRtlFiles /home/projects_2/workspace/ruytterh/europa/lpddr_experiments/lpddr5x_phy_0_50/vcspyglass/dwc_lpddr5xphy_hardmacro.lst; # == default value.
