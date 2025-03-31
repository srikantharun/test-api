# *****************************************************
# Modified top-level constraints for lpddr_p,
# Original version from snps at $DDR_SUBSYSTEM_RTL_PATH/syn/constrain/script/DWC_ddrctl.tcl
# Axelera modified to intercept lpddr_p, this adds/changes stuff for the following points
# - i_oa_clk -> additional clock added by axelera driving always on logic in the wrapper. Does not propagate into subsys
# - i_lpddr_clk -> Grouped top-level clock, this clock drives all subsys clocks. It is split between a normal lpddr_clk and lpddr_bypass_clk
#   - removed existing create_clock statements and replaced by axelera one
#   - create generated clock for lpddr_clk and lpddr_bypass_clk
# - intercept changes to interface -> existing in/out delays modified, some removed and some added.
# - Removed max delay statements on memory control signals that will be tied
# - Removed max delay statements on DFT signals, DFT constraints intercept these.
# - Added DFT related constraints.



# ****************************************************
# coreConsultant generated intent command file for design: DWC_ddrctl
# Generator version: 2.0
# Generated at: 16:03:39 on 07/25/24
# ****************************************************

if { ![info exists CONSTR_DIR] } {
  puts "WARNING: CONSTR_DIR is not defined. Setting to local dir. It should point to the directory that contains all axelera constraints files."
  set CONSTR_DIR "."
}

# Allow override of INST_HIER
if { ![info exists INST_HIER] } {
  set INST_HIER ""
}
## [AX] General axelera hierachy above snps subsys.
set axelera_hier ${INST_HIER}u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst
set DDR_HIER_PREFIX "${axelera_hier}/i_DWC_lpddr5x_phy"


##---------------------------------------------------------------------------------------
## default units
##---------------------------------------------------------------------------------------
set_units -capacitance pF -time ns

##==============================================================================
# Set "cdc_scale" variable.
#===============================================================================
# This variable scales the TEMBUF delay in relation of VDD value.
# The VDD supply voltage value is based on typical corner.
#===============================================================================
#  VDD[V]          0.75          0.70          0.65          0.60
#-------------------------------------------------------------------------------
#  cdc_scale        1            1.25          1.33           2
#===============================================================================

if {[info exist cdc_scale]} {
puts "INFO: Fusion Compiler is used. Current cdc_scale is ${cdc_scale}"
} else {

#cdc_scale for Design Compiler - default is cdc_scale 1
set cdc_scale 1

puts "INFO: Design Compiler is used. Current cdc_scale is ${cdc_scale}"
}



##==========================##
## Source clock constraints ##
##==========================##
# TODO: discuss and review draft clocks file with snps
source -e -v ${CONSTR_DIR}/lpddr_p.clocks.tcl

##=======================##
## Source IO constraints ##
##=======================##
# TODO: discuss and review draft io file with snps
source -e -v ${CONSTR_DIR}/lpddr_p.io.tcl

##===============================##
## Source exeception constraints ##
##===============================##
# TODO: discuss and review draft exceptions file with snps
# TODO: add expections for reset paths out of the ppmu.
source -e -v ${CONSTR_DIR}/lpddr_p.exceptions.tcl

##===============================##
## Source DFT func mode settings ##
##===============================##
read_sdc ${CONSTR_DIR}/lpddr_p.dft_disable.tcl
# MBIST constraints use mapped pin names -> on a pre-mapped design they will generated warnings that they cannot be applied.
# It should be fine to ignore these and make sure the constraints get applied after the inital mapping is done.
read_sdc ${CONSTR_DIR}/lpddr_p.mbist.sdc

##-----------------------------------------------------------------------------------------
## Functional mode settings
##-----------------------------------------------------------------------------------------
# AX: these are controlled by the jtag tab, in funcmode they receive the same case setting as SNPS used on the ports.
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_scan_mode_inst/ijtag_data_out]
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst/ijtag_data_out]
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst/ijtag_data_out]
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_scan_occ_*_inst/ijtag_data_out]
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_scan_asst_mode_inst/ijtag_data_out]
set_case_analysis 0 [get_pins -hier lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst/all_test_latch_reg/Q]

##-----------------------------------------------------------------------------------------
## Pipe usage settings by DfiClk frequency > 800MHz
##-----------------------------------------------------------------------------------------
if {$lpddr_clk_period < 1.250} {
puts "INFO: Case Analysis Set on configurable pipe stages"
##-- csrDxOutPipeEn
set_case_analysis 1 [get_pins		${DDR_HIER_PREFIX}/pub_top/pub/csrDxOutPipeEn_reg/Q]
##-- csrDxInPipeEn
set_case_analysis 1 [get_pins		${DDR_HIER_PREFIX}/pub_top/pub/csrDxInPipeEn_reg/Q]
##-- csrAcInPipeEn
set_case_analysis 1 [get_pins		${DDR_HIER_PREFIX}/pub_top/pub/csrAcInPipeEn_reg/Q]
}


##=========================================================================================
## 11. Misc
##=========================================================================================
##------------------------------------------------------------------------------
## Force output of all clock-gating cells to be ideal in DC & PT with synthesis netlist
##------------------------------------------------------------------------------
## [AX] SNPS, does this need to be in the constraints, seems more like a tool-flow thing. Commenting for now.
# if {$flow == "syn_compile"} {
#     set cg_out_net [get_nets -of_objects [get_pins	-of [get_cells	.* -hier -quiet -regexp -filter "ref_name =~ .*dwc_lpddr5xphy_clkgater_.* || ref_name =~ .*dwc_lpddr5xphy_pmu_clkgate.*"] -filter "pin_direction==out"]]
#     set_ideal_network -no_propagate $cg_out_net
#     unset cg_out_net
# }

##====================================##
## Source ctrl exeception constraints ##
##====================================##
# TODO: snps, do we need these? And if so, what do they do?
source -e -v ${CONSTR_DIR}/lpddr_p.ctrl_exceptions.tcl

##=========================================================================================
## Extra check
##=========================================================================================
##-- source the extra checks file here to make certain it is run
## TODO: SNPS what are these extra things, do we need to keep them?
set flow ""
if {$flow == "syn_sta"} {
  source  -echo -verbose ${CONSTR_DIR}/lpddr_p.extra_checks.tcl > ${REPORTS_DIR}/${DESIGN_NAME}.sta.extra_checks.rpt

  ##-- Notes: Min pulse width checks for PllBypClk and DfiClk may be removed or ignored if PllBypClk is unused.
  ##-- Notes: The clock min pulse width check is intended to be conducted after CTS with adjusted clock uncertainty values
  ##-- Notes: the STA analysis after synthesis will report min_pulse_width violation because of the large clock uncertainties. This violation can be waived.
  set_min_pulse_width [expr 0.40 * $PllRefClk_period] [get_pins		${DDR_HIER_PREFIX}/u_DWC_DDRPHYMASTER_topX/PllRefClk]
  set_min_pulse_width [expr 0.40 * $PllBypClk_period] [get_pins		${DDR_HIER_PREFIX}/u_DWC_DDRPHYMASTER_topX/PllBypClk]
  set_min_pulse_width [expr 0.40 * $DfiClk_period]    [get_pins		${DDR_HIER_PREFIX}/u_DWC_DDRPHYMASTER_topX/DfiClkIn]
}
