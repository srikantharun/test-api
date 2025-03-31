################################################################################
## Copyright 2021-2022 Synopsys, Inc. All rights reserved
################################################################################
## SDC for lpddr5xmphy
##------------------------------------------------------------------------------
## File:        dwc_lpddr5xphy_top.extra_checks.tcl
## Description: Special(extra) checks
################################################################################

################################################################################
## File Contents
##------------------------------------------------------------------------------
## 1. Pclk Latency and skew
##
## 2. DfiClk Latency and skew
##
## 3. PllRefClk Latency
##
## 4. PllBypClk Latency
##
################################################################################
################################################################################
## Notes for customer
##------------------------------------------------------------------------------
##-- 1. PClk skew check must be covered by construction and SPICE simulation by circuit team
##-- 2. The checkers for clock latency what we provided, the startpoints are from PHY_TOP clock ports 
##--    Customer should change the startpoint from SOC source (e.g. PLL output) in SOC level
################################################################################


##==============================================================================
## Suppress messages during special checks
##==============================================================================
##--    - Disable the following messages (warnings) because the cause is known 
##--    - ENV-003:  Informs for used min or max wire load model selection group chosen atomaticlly  
##--    - PTE-003:  Some timing arcs have been disabled for breaking timing loops or because of constant propagation
##--    - PTE-016:  Informs for expanding clock and calculated base period 
##--    - PTE-018:  Prime Time informs for abandoning fast timing updates in timing update.  
##--    - PTE-101:  Was not inferred clock-gating check for reported pin of cell. This is not clock tree build phase and this is not issue   
##--    - UITE-416: Some start and end points are invalid when report_timing, get_timing_paths are specified with using "*"

suppress_message ENV-003
suppress_message PTE-003
suppress_message PTE-016
suppress_message PTE-018
suppress_message PTE-101
suppress_message UITE-416

##==============================================================================
## Enable reporting paths that started at inactive startpoints
##------------------------------------------------------------------------------
## From 2019.03 version of PT, inactive startpoints are ignored and
## a new variable timing_report_unconstrained_paths_from_nontimed_startpoints
## is added.
## But for extra_check, this behavioral is needed.
##==============================================================================

if {[info exists timing_report_unconstrained_paths_from_nontimed_startpoints]} {
   set reserve_value_unconstrained [get_app_var timing_report_unconstrained_paths_from_nontimed_startpoints]
   set_app_var timing_report_unconstrained_paths_from_nontimed_startpoints true
}

##==============================================================================
## Valiables setting
##==============================================================================
##-- Multiplay the latency limit value by the voltage dependent delay coefficient "cdc_scale" for the different power supplay values.
##-- PLL REFCLK insertion delay should be < 936ps*voltage_dependent_delay_coefficient
set PllRefClkMasterLatencyLimit   [expr 0.936*${cdc_scale}]

##-- PLL BypClk insertion delay should be < 936ps*voltage_dependent_delay_coefficient
set PllBypClkMasterLatencyLimit   [expr 0.936*${cdc_scale}]

##-- PClkIn insertion delay from MASTER to all HardIP should be < 350ps
set PClkAllLatencyLimit         0.350

##-- PClkIn skew should be < 155ps
set PClkSkewLimit               0.155

##-- Max skew across DfiClkIn inputs of all HardIP should be < 117ps
set DfiClkAllSkewLimit          0.117

##-- Insertion delay to DfiClkIn inputs of all HardIP should be < 936ps*voltage_dependent_delay_coefficient
set DfiClkAllLatencyLimit       [expr 0.936*${cdc_scale}]

##==============================================================================
## 1. Pclk Latency and skew for DBYTE
##------------------------------------------------------------------------------
##    - From Master pclk output pins to all hardip's PclkIn input pins
##==============================================================================
##-- Note: PClk skew check must be covered by construction and SPICE simulation by circuit team

##==============================================================================
## 2. DfiClk Latency and skew
##------------------------------------------------------------------------------
##    - From DfiClk port to all hardip's DfiClk pins 
##    - Customer should change the startpoint from SOC source for more accurate in SOC level
##==============================================================================
##-- begin DfiClk latency/skew for all hardips

echo ""
echo "Latency delay from DfiClk to all hardip's DfiClk pins must be less than $DfiClkAllLatencyLimit ns" 
echo "Skew between all hardips' DfiClk pins must be less than $DfiClkAllSkewLimit ns" 
set endp   [get_pins	${DDR_HIER_PREFIX}/*u_AC_WRAPPER_X*/DIFF_CK*/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_AC_WRAPPER_X*/ACX_*/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_AC_WRAPPER_X*/CSX_*/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_DBYTE_WRAPPER_X*/dx_*/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_DWC_LPPDR5xMPHYZCAL_TOP/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_CMOSX2_TOP/DfiClkIn]
append_to_collection endp [get_pins	${DDR_HIER_PREFIX}/*u_DWC_DDRPHYMASTER_topX/DfiClkIn]
set num_endp [sizeof_collection $endp]
set startp [get_port DfiClk]
set tp     [get_timing_path -path full_clock_expanded -through $startp -rise_to $endp -max 10000 -nworst 10000 -delay max -slack_lesser_than infinity]

echo "Reporting DfiClk latency and skew to the following $num_endp pins"
report_latency_skew_endpoints $tp "DfiClk" ${DfiClkAllLatencyLimit} ${DfiClkAllSkewLimit}

##-- end DfiClk latency/skew for all hard macros


##==============================================================================
## 3. PllRefClk Latency
##------------------------------------------------------------------------------
##    - From port PllRefClk to master input pin PllRefClk 
##    - Customer should change the startpoint from SOC source for more accurate in SOC level
##==============================================================================

##-- begin PllRefClk latency to master
echo ""
echo "Latency delay from port PllRefClk to master input pin PllRefClk must be less than $PllRefClkMasterLatencyLimit ns" 
set endp   [get_pins		${DDR_HIER_PREFIX}/*u_DWC_DDRPHYMASTER_topX/PllRefClk]
set startp [get_port PllRefClk]
set tp     [get_timing_path -path full_clock_expanded -through $startp -rise_to $endp -delay max -slack_lesser_than infinity]
set masterPllRefClk_arrival [get_attr $tp arrival]
echo "     PllRefClk Arrival to u_DWC_DDRPHYMASTER_topX/PllRefClk: $masterPllRefClk_arrival"
echo "     PllRefClk Master Latency Limit: $PllRefClkMasterLatencyLimit "
set latency_slack [expr $PllRefClkMasterLatencyLimit - $masterPllRefClk_arrival]
if { $latency_slack < 0 } {
    echo "     latency slack (VIOLATED):   $latency_slack "
} else {
    echo "     latency slack (PASS):   $latency_slack "
}
##-- end PllRefClk latency to master


##==============================================================================
## 4. PllBypClk Latency
##------------------------------------------------------------------------------
##    - From port PllBypClk to master input pin PllBypClk 
##    - Customer should change the startpoint from SOC source for more accurate in SOC level
##==============================================================================
##-- begin PllBypClk latency to master
echo ""
echo "Latency delay from port PllBypClk to master input pin PllBypClk must be less than $PllBypClkMasterLatencyLimit ns" 
set endp   [get_pins		${DDR_HIER_PREFIX}/*u_DWC_DDRPHYMASTER_topX/PllBypClk]
set startp [get_ports PllBypClk]
set tp     [get_timing_path -path full_clock_expanded -through $startp -rise_to $endp -delay max -slack_lesser_than infinity]
set masterPllBypClk_arrival [get_attr $tp arrival]
echo "     PllBypClk Arrival to u_DWC_DDRPHYMASTER_topX/PllBypClk: $masterPllBypClk_arrival"
echo "     PllBypClk Master Latency Limit: $PllBypClkMasterLatencyLimit "
set latency_slack [expr $PllBypClkMasterLatencyLimit - $masterPllBypClk_arrival]
if { $latency_slack < 0 } {
    echo "     latency slack (VIOLATED):   $latency_slack "
} else {
    echo "     latency slack (PASS):   $latency_slack "
}

##-- end PllBypClk latency to master


##==============================================================================
## Unsuppress messages that suppressed during special checks
##==============================================================================
unsuppress_message ENV-003
unsuppress_message PTE-003
unsuppress_message PTE-016
unsuppress_message PTE-018
unsuppress_message PTE-101
unsuppress_message UITE-416

echo "\n"

##==============================================================================
## Recover setting for reporting paths that started at inactive startpoints
##==============================================================================

if {[info exists timing_report_unconstrained_paths_from_nontimed_startpoints]} {
   set_app_var timing_report_unconstrained_paths_from_nontimed_startpoints ${reserve_value_unconstrained}
}


echo "\n"

