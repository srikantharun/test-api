##=========================================================================================
## 1. LPDDR_P non PHY related IO
##=========================================================================================
## [AX] Default budget to start with is 60% for the outside world for all synchronous interfaces.
## This can/will be updated using more detailed budgetting values per corner.
## If needed these can be updated based on the required internal clock latencies per interface.
set input_budget 0.7
set output_budget 0.7

# 
# Minimum/Maximum delay values (arrival times) for input ports.
#
## [AX] grouped ports per interface/sideband-type and updated IO budget to parameter set above
# AXI interface(sync to i_lpddr_clk)
set_input_delay     -add_delay -max [expr $input_budget*$lpddr_clk_period]      -clock i_lpddr_clk_virt [get_ports i_lpddr_axi* ]
set_input_delay     -add_delay -min 0.0                                         -clock i_lpddr_clk_virt [get_ports i_lpddr_axi* ]
set_output_delay    -add_delay -max [expr $output_budget*$lpddr_clk_period]     -clock i_lpddr_clk_virt [get_ports o_lpddr_axi* ]
set_output_delay    -add_delay -min 0.0                                         -clock i_lpddr_clk_virt [get_ports o_lpddr_axi* ]
# APB cfg interface(sync to i_lpddr_clk)
set_input_delay     -add_delay -max [expr $input_budget * $lpddr_clk_period]    -clock i_lpddr_clk_virt [get_ports i_lpddr_cfg_apb4* ]
set_input_delay     -add_delay -min 0.0                                         -clock i_lpddr_clk_virt [get_ports i_lpddr_cfg_apb4* ]
set_output_delay    -add_delay -max [expr $output_budget * $lpddr_clk_period]   -clock i_lpddr_clk_virt [get_ports o_lpddr_cfg_apb4* ]
set_output_delay    -add_delay -min 0.0                                         -clock i_lpddr_clk_virt [get_ports o_lpddr_cfg_apb4* ]
# APB sys_CFG interface (sync to i_ao_clk)
set_input_delay     -add_delay -max [expr $input_budget*$ao_clk_period]         -clock i_ao_clk_virt    [get_ports i_lpddr_syscfg_apb4* ]
set_input_delay     -add_delay -min 0.0                                         -clock i_ao_clk_virt    [get_ports i_lpddr_syscfg_apb4* ]
set_output_delay    -add_delay -max [expr $output_budget*$ao_clk_period]        -clock i_ao_clk_virt    [get_ports o_lpddr_syscfg_apb4* ]
set_output_delay    -add_delay -min 0.0                                         -clock i_ao_clk_virt    [get_ports o_lpddr_syscfg_apb4* ]

# Noc clock enable should have very limited clock latency and tight budget
# PCTL logic should be placed close to the o_noc_clken port
set_output_delay    -add_delay -max [expr 0.8*$lpddr_clk_period]                -clock i_lpddr_clk_virt [get_ports o_noc_clken]
set_output_delay    -add_delay -min 0.0                                         -clock i_lpddr_clk_virt [get_ports o_noc_clken]

# Ports sync to i_ao_clk
set_input_delay     -add_delay -max [expr $input_budget*$ao_clk_period]         -clock i_ao_clk_virt [get_ports i_global_rst_n]
set_input_delay     -add_delay -min 0.0                                         -clock i_ao_clk_virt [get_ports i_global_rst_n]
set_input_delay     -add_delay -max [expr $input_budget*$ao_clk_period]         -clock i_ao_clk_virt [get_ports i_ao_rst_n]
set_input_delay     -add_delay -min 0.0                                         -clock i_ao_clk_virt [get_ports i_ao_rst_n]
set_output_delay    -add_delay -max [expr $output_budget*$ao_clk_period]        -clock i_ao_clk_virt [get_ports o_ao_rst_sync_n]
set_output_delay    -add_delay -min 0.0                                         -clock i_ao_clk_virt [get_ports o_ao_rst_sync_n]
set_output_delay    -add_delay -max [expr $output_budget*$ao_clk_period]        -clock i_ao_clk_virt [get_ports o_noc_rst_n]
set_output_delay    -add_delay -min 0.0                                         -clock i_ao_clk_virt [get_ports o_noc_rst_n]

# Async ports get constrained against a virtual async clock from AX
set_input_delay  -add_delay -max [expr $input_budget*$lpddr_async_virt_clk_period]   -clock i_lpddr_clk_async_virt [get_ports i_noc_async_*]
set_input_delay  -add_delay -min 0.0                                                 -clock i_lpddr_clk_async_virt [get_ports i_noc_async_*]
set_output_delay  -add_delay -max [expr $output_budget*$lpddr_async_virt_clk_period]   -clock i_lpddr_clk_async_virt [get_ports o_noc_async_*]
set_output_delay  -add_delay -min 0.0                                                 -clock i_lpddr_clk_async_virt [get_ports o_noc_async_*]

# Interrupt ports get constraints against the main clock, but given a multicycle since they are not timing critical.
set_output_delay  -add_delay -max [expr $output_budget*$lpddr_clk_period]   -clock i_lpddr_clk_virt [get_ports o_*_obs]
set_output_delay  -add_delay -min 0.0                                      -clock i_lpddr_clk_virt [get_ports o_*_obs]
set_output_delay  -add_delay -max [expr $output_budget*$lpddr_clk_period]  -clock i_lpddr_clk_virt [get_ports o_*_intr]
set_output_delay  -add_delay -min 0.0                                     -clock i_lpddr_clk_virt [get_ports o_*_intr]

# Relax observability and interrupt timing.
set_multicycle_path 3  -setup -to [get_ports o_*_obs]
set_multicycle_path 2  -hold -to [get_ports o_*_obs] 
set_multicycle_path 3  -setup -to [get_ports o_*_intr]
set_multicycle_path 2  -hold -to [get_ports o_*_intr] 

##=========================================================================================
## 1. PHY related IO, adapted from SNPS dwc_lpddr5xphy_top.io.tcl
##=========================================================================================

################################################################################
## Copyright 2021-2023 Synopsys, Inc. All rights reserved
################################################################################
## SDC for lpddr5xphy 
##------------------------------------------------------------------------------
## File:        dwc_lpddr5xphy_top.io.tcl
## Description: IO constraints
################################################################################

################################################################################
## File Contents
##------------------------------------------------------------------------------
## 1. Set IO delay
##
## 2. Exceptions on IO ports
##
## 3. Set design rule
################################################################################

################################################################################
## 1. Set IO delay
################################################################################

##==============================================================================
## Ports related to DfiClk
##------------------------------------------------------------------------------
## For 50% IO delay of DfiClk the next defines 
## DWC_LPDDR5XPHY_PIPE_DFI_WR, DWC_LPDDR5XPHY_PIPE_DFI_RD, DWC_LPDDR5XPHY_PIPE_DFI_MISC
## should be defined.
##==============================================================================

##==============================================================================
# Set IO external delay of ports related to DfiClk
#===============================================================================
#--            DfiClk frequency,       IO delay(ports related to DfiClk) 
#-------------------------------------------------------------------------------
#--   Mode1:       800MHz                      50% of DfiClk
#-------------------------------------------------------------------------------
#--   Mode2:      1067MHz                      50% of DfiClk        
#===============================================================================
## For 50% IO delay of DfiClk the next defines 
## DWC_LPDDR5XPHY_PIPE_DFI_WR, DWC_LPDDR5XPHY_PIPE_DFI_RD, DWC_LPDDR5XPHY_PIPE_DFI_MISC
## should be defined.
##==============================================================================
set DfiClk_IO_delay [expr 0.50]

##-- [AX] removed ports that are no longer on the IO,
# set_input_delay  [expr $DfiClk_IO_delay * $lpddr_clk_period ]      -clock Virtual_DfiClk       [get_ports {Reset}]
# set_output_delay [expr $DfiClk_IO_delay * $lpddr_clk_period ]      -clock Virtual_DfiClk       [get_ports {PhyInt_n*}]
# set_output_delay [expr $DfiClk_IO_delay * $lpddr_clk_period ]      -clock Virtual_DfiClk       [get_ports {PhyInt_fault*}]
# set_output_delay [expr $DfiClk_IO_delay * $lpddr_clk_period ]      -clock Virtual_DfiClk       [get_ports {dwc_lpddr5xphy_pmu_busy}]



#------------------------------------------------------------------------------
#DWC_LPDDR5XPHY_LBIST_EN
#------------------------------------------------------------------------------
if {[info exists def(DWC_LPDDR5XPHY_LBIST_EN)]}    {  
  set_input_delay  [expr $DfiClk_IO_delay * $lpddr_clk_period ] -clock Virtual_DfiClk [get_ports {lbist_mode} -filter {@port_direction == in}] 
}

##==============================================================================
## Bypass mode / Bypass signals setting
## Boundary Scan / Bypass Interface Signals / Bypass Mode Pins
##------------------------------------------------------------------------------
##==============================================================================
##-- [SS] Removed bypass ports after confirming in Solvnet case 01725096
########################################################################################   

##==============================================================================
## Constraint Ports in TDRClk Domain
##==============================================================================
##-- [AX] DFT signal constrains
## JTAG interface, tck port is defined as TDRCLK
set_input_delay  [expr 0.5*$input_budget * $TDRCLK_period ] -clock Virtual_TDRCLK [get_ports { tms tdi trst } -filter {@port_direction == in}]
set_output_delay [expr 0.5*$output_budget * $TDRCLK_period ] -clock Virtual_TDRCLK [get_ports { tdo_en tdo } -filter {@port_direction == out}]

# BISR interface
set_input_delay [expr 0.5*$input_budget * $bisr_clk_period] -clock bisr_clk_virt [get_ports { bisr_reset bisr_shift_en bisr_si}]
set_output_delay [expr 0.5*$output_budget * $bisr_clk_period] -clock bisr_clk_virt [get_ports {bisr_so}]

# SSN bus interface
set_input_delay [expr 0.5*$input_budget * $ssn_bus_clk_period] -clock ssn_bus_clk_virt [get_ports ssn_bus_data_in]
set_output_delay [expr $output_budget * $ssn_bus_clk_period] -clock ssn_bus_clk_virt [get_ports ssn_bus_data_out]

##==============================================================================
## Constraint Ports on BP_*
##==============================================================================
## BP_PWROK
##------------------------------------------------------------------------------
## [AX] BP_PWROK internally tied.
# set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_PWROK -filter {@port_direction == in}]

##------------------------------------------------------------------------------
## BP_ZN
##------------------------------------------------------------------------------
set_output_delay [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_ZN]

##------------------------------------------------------------------------------
## BP_DTO0, BP_DTO1
##------------------------------------------------------------------------------
if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
set_input_delay  [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports BP_DTO? -filter {@port_direction == inout}]
set_input_delay  [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports BP_DTO? -filter {@port_direction == inout}] -add_delay
set_output_delay [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports BP_DTO? -filter {@port_direction == inout}]
set_output_delay [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports BP_DTO? -filter {@port_direction == inout}] -add_delay
}

##------------------------------------------------------------------------------
## BP_ATO
##------------------------------------------------------------------------------
set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_ATO -filter {@port_direction == inout}]
set_output_delay [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_ATO -filter {@port_direction == inout}]

set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_ATO_PLL -filter {@port_direction == inout}]
set_output_delay [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BP_ATO_PLL -filter {@port_direction == inout}]

##------------------------------------------------------------------------------
## BP_MEMRESET_L
##------------------------------------------------------------------------------
set_output_delay [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports BP_MEMRESET_L -filter {@port_direction == out}]
set_output_delay [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports BP_MEMRESET_L -filter {@port_direction == out}] -add_delay

##------------------------------------------------------------------------------
## BP_A[*]
##------------------------------------------------------------------------------
set_input_delay  [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_A[*]} ]
set_input_delay  [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_A[*]} ] -add_delay
set_output_delay [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_A[*]} ]
set_output_delay [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_A[*]} ] -add_delay

##------------------------------------------------------------------------------
## BP_B*_D[*]
##------------------------------------------------------------------------------
set_input_delay  [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_B*_D[*]} ]
set_input_delay  [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_B*_D[*]} ] -add_delay
set_output_delay [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_B*_D[*]} ]
set_output_delay [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_B*_D[*]} ] -add_delay

##------------------------------------------------------------------------------
## BP_CK*
##------------------------------------------------------------------------------
set_input_delay  [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_CK*} ]
set_input_delay  [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_CK*} ] -add_delay
set_output_delay [expr $Virtual_BypassClk_period         * 0.170] -clock Virtual_BypassClk         [get_ports {BP_CK*} ]
set_output_delay [expr $Virtual_InternalBypassClk_period * 0.340] -clock Virtual_InternalBypassClk [get_ports {BP_CK*} ] -add_delay

##-- [AX] ports below are connected in axelera wrapper, constraints here can be removed
##==============================================================================
## Reset_async
##==============================================================================
# set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk  [get_ports {Reset_async}]

# ##==============================================================================
# ## BurnIn
# ##==============================================================================
# set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports BurnIn -filter {@port_direction == in}]

# ##==============================================================================
# ## Iddq_mode
# ##==============================================================================
# set_input_delay  [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports Iddq_mode -filter {@port_direction == in}]

# ##==============================================================================
# ## dwc_lpddr5xphy_dto[*]
# ##==============================================================================
# set_output_delay [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports {dwc_lpddr5xphy_dto[*]} ]

# ##==============================================================================
# ## dwc_lpddr5xphy_pll_lock
# ##==============================================================================
# set_output_delay [expr $Virtual_AsyncPortClk_period * 0.500] -clock Virtual_AsyncPortClk [get_ports {dwc_lpddr5xphy_pll_lock} ]

##==============================================================================
## SCAN ports
##------------------------------------------------------------------------------
##    All scan_* ports are related with scan_Virtual clock,
##    however scan_Virtual clock is asynchronous to all DFT clocks.
##    This prevents from checking timing between IO & FF.
##    Customer should allocate proper clocks per IO to check IO timing.
##==============================================================================
# [AX] scan signals intercepted by DFT inserted RTL all can be commented
##------------------------------------------------------------------------------
## scan_mode
##------------------------------------------------------------------------------
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports {scan_mode}]

# ##------------------------------------------------------------------------------
# ## scan_shift* scan_*_shift*
# ## scan_shift_cg: This port is scan enable for clock-gating and will be created during scan-stitching
# ##------------------------------------------------------------------------------
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports -quiet {scan_shift* scan_*_shift* scan_shift_cg*}]

# ##------------------------------------------------------------------------------
# ## scan_si*
# ## scan_*_si[*]: Will be created during scan-Stitching
# ##------------------------------------------------------------------------------
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports -quiet {scan_si* scan_*_si*}]

# ##------------------------------------------------------------------------------
# ## scan_so*
# ## scan_*_so*: Will be created during scan-Stitching
# ##------------------------------------------------------------------------------
# ##    Half cycle path
# ##------------------------------------------------------------------------------
# set_output_delay  [expr $scan_Virtual_period * 0.170] -clock scan_Virtual [get_ports -quiet {scan_so* scan_*_so*}]

# ##------------------------------------------------------------------------------
# ## scan_occ_bypass
# ##------------------------------------------------------------------------------
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports -quiet {scan_occ_bypass}]
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports -quiet {scan_occ_reset}]

# ##------------------------------------------------------------------------------
# ## scan_asst_mode
# ##------------------------------------------------------------------------------
# set_input_delay   [expr $scan_Virtual_period * 0.340] -clock scan_Virtual [get_ports -quiet {scan_asst_mode}]


################################################################################
## 2. Exceptions on IO ports
################################################################################

##------------------------------------------------------------------------------
## TEMBUF cells
##------------------------------------------------------------------------------

##==============================================================================
## (8) ALL_zCDCBUF_DfiClk_Untimed_DLY3333PS 
##------------------------------------------------------------------------------ 
## Virtual_DfiClk to Virtual_AsyncPortClk: zCDCBUF_DfiClk_Untimed_DLY3333PS
##    - Template: zCDCBUF_DfiClk_Untimed_DLY3333PS
##    - Description: These TEMBUF cells have paths from Virtual_DfiClk to
##                   Virtual_AsyncPortClk. These clocks are async, so set a max
##                   delay value.
## DfiClk and UcClk to Virtual_AsyncPortClk: zCDCBUF_DfiClk_Untimed_DLY3333PS
##    - Template: zCDCBUF_DfiClk_Untimed_DLY3333PS
##    - Description: These TEMBUF cells have paths from DfiClk and UcClk to
##                   Virtual_AsyncPortClk. These clocks are async, so set a max
##                   delay value.
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_Untimed_DLY3333PS_pins \
	[get_pins	-hier *zCDCBUF_DfiClk_Untimed_DLY3333PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + input_delay + output_delay
set VALUE_max_delay [expr 3.333*${cdc_scale} + $DfiClk_IO_delay * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_DfiClk_Untimed_DLY3333PS_pins} {
   eval $my_set_max_delay -from [get_clocks Virtual_DfiClk] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks Virtual_AsyncPortClk] \
                          ${VALUE_max_delay}
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock + output_delay
set VALUE_max_delay [expr 3.333*${cdc_scale} + ${clock_latency_DfiClk} + 0.500 * ${Virtual_AsyncPortClk_period}]

## [AX] removed scan_DfiClk from from list since it does not exists in func mode.
foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_DfiClk_Untimed_DLY3333PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list DfiClk ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks Virtual_AsyncPortClk] \
                          ${VALUE_max_delay}
}

##------------------------------------------------------------------------------ 
##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock + output_delay
set VALUE_max_delay [expr 3.333*${cdc_scale} + ${clock_latency_UcClk} + 0.500 * ${Virtual_AsyncPortClk_period}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_DfiClk_Untimed_DLY3333PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list UcClk]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks Virtual_AsyncPortClk] \
                          ${VALUE_max_delay}
}


##==============================================================================
## (11) ALL_zCDCBUF_Untimed_Untimed_DLY3333PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_Untimed_Untimed_DLY3333PS_pins \
	[get_pins	-hier *zCDCBUF_Untimed_Untimed_DLY3333PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + input_delay - latency_to_clock
set VALUE_max_delay [expr 3.333*${cdc_scale} + 0.500 * ${Virtual_AsyncPortClk_period} - ${clock_latency_DfiClk}]
## [AX] removed scan_DfiClk from from list since it does not exists in func mode.
foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_Untimed_Untimed_DLY3333PS_pins} {
   eval $my_set_max_delay -from [get_clocks Virtual_AsyncPortClk] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list DfiClk]] \
                          ${VALUE_max_delay}
}


##==============================================================================
## (13) ALL_zCDCBUF_Untimed_DfiClk_DLY1667PS
##------------------------------------------------------------------------------ 
## Virtual_AsyncPortClk to DfiClk: zCDCBUF_Untimed_DfiClk_DLY1667PS
##    - Template: zCDCBUF_Untimed_DfiClk_DLY1667PS
##    - Description: These TEMBUF cells have paths from Virtual_AsyncPortClk to
##                   UcPhasor_reg async pin. 
##                   This pin is async, so set a max delay value.
##==============================================================================
## [AX]: resets driven from AX partition controller -> they get a MCP of 5 cycles in another exception, this exception should no longer be required.
##-- Value: arch_requirement*voltage_dependent_delay_coefficient + input_delay - latency_to_clock
# set zCDCBUF_Untimed_DfiClk_DLY1667PS_pins [get_pins	-hier *zCDCBUF_Untimed_DfiClk_DLY1667PS*/TEM_DIN* ]
# set VALUE_max_delay  [expr 1.667*${cdc_scale} +  0.500 * $Virtual_AsyncPortClk_period - ${clock_latency_DfiClk}]
# foreach_in_collection cur_TEMBUF ${zCDCBUF_Untimed_DfiClk_DLY1667PS_pins} {
#    eval $my_set_max_delay                 -from [get_clocks Virtual_AsyncPortClk] \
#                                           -through ${cur_TEMBUF} \
#                                           -to  [filter_collection [all_fanout -from Reset_async -flat -endpoints_only] "full_name =~ *UcPhasor_reg/*"] \
#                                           ${VALUE_max_delay}
# }


##==============================================================================
## From ports to  HardIP's no timing arc pins
##==============================================================================

##==============================================================================
## List of Hard Macro
##    (1) dx4
##    (2) dx5
##    (3) acx2
##    (4) csx2
##    (5) ckx2
##    (6) cmosx2
##    (7) master
##    (8) zcal
##==============================================================================

##==============================================================================
## (1-1) dx4: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
## [AX] Signals below are intercepted by DFT or partition control logic. Exceptions no longer required.
# set dx4_macro [get_object_name [get_cells	-hier * -filter "ref_name=~*dwc_lpddr5xphydx4*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports BurnIn] \
#                           -to   [get_pins	${cur_instance}/BurnIn]
# }

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Reset_async] \
#                           -to   [get_pins	${cur_instance}/Reset_async]
# }

# ##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports scan_occ_bypass] \
#                           -to   [get_pins	${cur_instance}/scan_occ_bypass]
# }

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports scan_occ_reset] \
#                           -to   [get_pins	${cur_instance}/scan_occ_reset]
# }

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports scan_asst_mode] \
#                           -to   [get_pins	${cur_instance}/scan_asst_mode]
# }

# ##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports scan_shift_cg] \
#                           -to   [get_pins	${cur_instance}/scan_shift_cg]
# }

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports scan_shift_async] \
#                           -to   [get_pins	${cur_instance}/scan_shift_async]
# }

# ##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# foreach cur_instance $dx4_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Iddq_mode] \
#                           -to   [get_pins	${cur_instance}/Iddq_mode]
# }


##==============================================================================
## (1-2) dx4: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set dx4_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphydx4*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]
## TODO: SNPS is it normal that this creates a warning that MtestMuxOut_Ln* is forced to be a timing startpoint?
set list_of_max_delay_pins   [list MtestMuxOut_Ln* \
                                   MtestMuxOut_DQS ]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

foreach cur_instance $dx4_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports $list_of_endpoints]
   }
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
##-- [AX] port adapted to axelera name (we routed these signals to obs pins)
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]

set list_of_max_delay_pins    [list MtestMuxOut_Ln* \
                                    MtestMuxOut_DQS ]

foreach cur_instance $dx4_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]
   }
}


##==============================================================================
## (1-1) dx5: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
##-- [AX] ports not exposed at top-level
# set dx5_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphydx5*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# foreach cur_instance $dx5_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports BurnIn] \
#                           -to   [get_pins	${cur_instance}/BurnIn]
# }

# foreach cur_instance $dx5_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Reset_async] \
#                           -to   [get_pins	${cur_instance}/Reset_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_bypass] \
#                              -to   [get_pins	${cur_instance}/scan_occ_bypass]
# }

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_reset] \
#                              -to   [get_pins	${cur_instance}/scan_occ_reset]
# }

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_asst_mode] \
#                              -to   [get_pins	${cur_instance}/scan_asst_mode]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_cg] \
#                              -to   [get_pins	${cur_instance}/scan_shift_cg]
# }

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_async] \
#                              -to   [get_pins	${cur_instance}/scan_shift_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# foreach cur_instance $dx5_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports Iddq_mode] \
#                              -to   [get_pins	${cur_instance}/Iddq_mode]
# }


##==============================================================================
## (1-2) dx5: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set dx5_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphydx5*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_max_delay_pins    [list MtestMuxOut_Ln* \
                                    MtestMuxOut_DQS ]

set list_of_endpoints         [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

foreach cur_instance $dx5_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports $list_of_endpoints]
   }
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]

set list_of_max_delay_pins    [list MtestMuxOut_Ln* \
                                    MtestMuxOut_DQS ]

foreach cur_instance $dx5_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]
   }
}


##==============================================================================
## (1-1) acx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed at top-level anymore, all commented
# set acx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyacx2*"]]

# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# foreach cur_instance $acx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports BurnIn] \
#                           -to   [get_pins	${cur_instance}/BurnIn]
# }

# foreach cur_instance $acx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Reset_async] \
#                           -to   [get_pins	${cur_instance}/Reset_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_bypass] \
#                              -to   [get_pins	${cur_instance}/scan_occ_bypass]
# }

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_reset] \
#                              -to   [get_pins	${cur_instance}/scan_occ_reset]
# }

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_asst_mode] \
#                              -to   [get_pins	${cur_instance}/scan_asst_mode]
# }

##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_cg] \
#                              -to   [get_pins ${cur_instance}/scan_shift_cg]
# }

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_async] \
#                              -to   [get_pins ${cur_instance}/scan_shift_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# foreach cur_instance $acx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports Iddq_mode] \
#                              -to   [get_pins ${cur_instance}/Iddq_mode]
# }


##==============================================================================
## (1-2) acx2: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set acx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyacx2*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_max_delay_pins   [list MtestMuxOut_Ln*]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

foreach cur_instance $acx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports $list_of_endpoints]
   }
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]

set list_of_max_delay_pins    [list MtestMuxOut_Ln* ]

foreach cur_instance $acx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]
   }
}


##==============================================================================
## (1-1) csx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed on top-level
# set csx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphycsx2*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# foreach cur_instance $csx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports BurnIn] \
#                           -to   [get_pins ${cur_instance}/BurnIn]
# }

# foreach cur_instance $csx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Reset_async] \
#                           -to   [get_pins ${cur_instance}/Reset_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_bypass] \
#                              -to   [get_pins ${cur_instance}/scan_occ_bypass]
# }

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_reset] \
#                              -to   [get_pins ${cur_instance}/scan_occ_reset]
# }

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_asst_mode] \
#                              -to   [get_pins ${cur_instance}/scan_asst_mode]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_cg] \
#                              -to   [get_pins ${cur_instance}/scan_shift_cg]
# }

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_shift_async] \
#                              -to   [get_pins ${cur_instance}/scan_shift_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# foreach cur_instance $csx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports Iddq_mode] \
#                              -to   [get_pins	${cur_instance}/Iddq_mode]
# }


##==============================================================================
## (1-2) csx2: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set csx2_macro [get_object_name [get_cells	-hier * -filter "ref_name=~*dwc_lpddr5xphycsx2*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_max_delay_pins   [list MtestMuxOut_Ln*]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

foreach cur_instance $csx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports $list_of_endpoints]
   }
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]

set list_of_max_delay_pins    [list MtestMuxOut_Ln* ]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
foreach cur_instance $csx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]
   }
}


##==============================================================================
## (1-1) ckx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed on top-level
# set ckx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyckx2*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# foreach cur_instance $ckx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports BurnIn] \
#                           -to   [get_pins ${cur_instance}/BurnIn]
# }

# foreach cur_instance $ckx2_macro {
#    eval $my_set_max_delay ${VALUE_max_delay} \
#                           -from [get_ports Reset_async] \
#                           -to   [get_pins ${cur_instance}/Reset_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_bypass] \
#                              -to   [get_pins	${cur_instance}/scan_occ_bypass]
# }

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_occ_reset] \
#                              -to   [get_pins	${cur_instance}/scan_occ_reset]
# }

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports scan_asst_mode] \
#                              -to   [get_pins	${cur_instance}/scan_asst_mode]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_port scan_shift_cg] \
#                              -to   [get_pins	${cur_instance}/scan_shift_cg]
# }

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_port scan_shift_async] \
#                              -to   [get_pins	${cur_instance}/scan_shift_async]
# }

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# foreach cur_instance $ckx2_macro {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -from [get_ports Iddq_mode] \
#                              -to   [get_pins	${cur_instance}/Iddq_mode]
# }


##==============================================================================
## (1-2) ckx2: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set ckx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyckx2*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_max_delay_pins   [list MtestMuxOut]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

foreach cur_instance $ckx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports $list_of_endpoints]
   }
}

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]

set list_of_max_delay_pins    [list MtestMuxOut]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
foreach cur_instance $ckx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins ${cur_instance}/${item}] \
                             -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]
   }
}


##==============================================================================
## (1-1) cmosx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed on top-level
set cmosx2_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports BurnIn] \
#                        -to   [get_pins	${cmosx2_macro}/BurnIn]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Iddq_mode] \
#                        -to   [get_pins	${cmosx2_macro}/Iddq_mode]
                       
# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Reset_async] \
#                        -to   [get_pins	${cmosx2_macro}/Reset_async]

##------------------------------------------------------------------------------
# set VALUE_max_delay [expr 7.000 + $DfiClk_IO_delay * ${lpddr_clk_period}]
                     
# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Reset] \
#                        -to   [get_pins	${cmosx2_macro}/Reset]

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_port scan_shift_cg] \
#                        -to   [get_pins	${cmosx2_macro}/scan_shift_cg]

##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay + output_delay
##-- [SS] Updated delay to 5 ns in lates pub release
set VALUE_max_delay [expr 5.000 + 0.500 * ${Virtual_AsyncPortClk_period} + 0.170 * ${Virtual_BypassClk_period} ]
               
eval $my_set_max_delay ${VALUE_max_delay} \
                       -through [get_pins ${cmosx2_macro}/BP_PWROK] \
                       -to      [get_ports BP_MEMRESET_L]


##==============================================================================
## (1-2) cmosx2: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set cmosx2_macro [get_object_name [get_cells	-hier * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${cmosx2_macro}/MtestMuxOut] \
                       -to   [get_ports $list_of_endpoints]

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${cmosx2_macro}/MtestMuxOut] \
                       -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]


##==============================================================================
## (1-1) master: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed on top-level
# set master_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphymaster_top*"]]

# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports BurnIn] \
#                        -to   [get_pins	${master_macro}/BurnIn]
                       
# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Reset_async] \
#                        -to   [get_pins	${master_macro}/Reset_async]

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + 0.340 * ${scan_Virtual_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports scan_occ_bypass] \
#                        -to   [get_pins	${master_macro}/scan_occ_bypass]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports scan_occ_reset] \
#                        -to   [get_pins	${master_macro}/scan_occ_reset]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports scan_asst_mode] \
#                        -to   [get_pins	${master_macro}/scan_asst_mode]

##------------------------------------------------------------------------------
# ##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_port scan_shift_cg] \
#                        -to   [get_pins	${master_macro}/scan_shift_cg]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_port scan_shift_async] \
#                        -to   [get_pins	${master_macro}/scan_shift_async]

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} +  0.500 * ${Virtual_AsyncPortClk_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Iddq_mode] \
#                        -to   [get_pins	${master_macro}/Iddq_mode]


##==============================================================================
## (1-2) master: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set master_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphymaster_top*"]]

##-- Value: arch_requirement + input_delay
set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]
# [AX] to ports adapted to obs port indices that connect to pll lock pin in wrapper
eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${master_macro}/PllLock_raw] \
                       -to   [get_ports o_lpddr_obs[0]]

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${master_macro}/MtestMuxOut] \
                       -to   [get_ports $list_of_endpoints]

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${master_macro}/MtestMuxOut] \
                       -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]


##==============================================================================
## (1-3) master: Type 3
##------------------------------------------------------------------------------
##    - Target: combinational pins
##    - Method: set_max_delay
##==============================================================================
set master_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphymaster_top*"]]

##-- Value: arch_requirement + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
eval $my_set_max_delay ${VALUE_max_delay} \
                       -from    [get_pins ${master_macro}/DfiClkIn] \
                       -through [get_pins ${master_macro}/PllDigTst[*]] \
                       -to      [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]

##------------------------------------------------------------------------------
set list_of_endpoints        [list BP_A[*]]

##-- Value: arch_requirement + output_delay
   set VALUE_max_delay [expr 2.200 + 0.340 * ${Virtual_InternalBypassClk_period}]
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from    [get_pins ${master_macro}/DfiClkIn] \
                          -through [get_pins ${master_macro}/PllDigTst[*]] \
                          -to      [get_ports $list_of_endpoints]


##==============================================================================
## (1-1) zcal: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] ports not exposed on top-level
# set zcal_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyzcal_top*"]]

##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 4.000 * ${lpddr_clk_period} + 0.500 * ${Virtual_AsyncPortClk_period} ]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports BurnIn] \
#                        -to   [get_pins	${zcal_macro}/BurnIn]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Iddq_mode] \
#                        -to   [get_pins	${zcal_macro}/Iddq_mode]
                       
# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_ports Reset_async] \
#                        -to   [get_pins	${zcal_macro}/Reset_async]

##------------------------------------------------------------------------------
##-- Value: arch_requirement + input_delay
# set VALUE_max_delay [expr 1.250 + 0.340 * ${scan_Virtual_period}]

# eval $my_set_max_delay ${VALUE_max_delay} \
#                        -from [get_port scan_shift_cg] \
#                        -to   [get_pins	${zcal_macro}/scan_shift_cg]


##==============================================================================
## (1-2) zcal: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
set zcal_macro [get_object_name [get_cells -hier * -filter "ref_name=~*dwc_lpddr5xphyzcal_top*"]]

##-- Value: arch_requirement PUB delay + arch_requirement extra HM delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.950 + 0.340 * ${Virtual_InternalBypassClk_period}]

set list_of_endpoints        [list BP_A[*]]

if {[sizeof_collection [get_ports -quiet BP_DTO?]] > 0} {
   lappend list_of_endpoints "BP_DTO?"
}

eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${zcal_macro}/MtestMuxOut] \
                       -to   [get_ports $list_of_endpoints]

##------------------------------------------------------------------------------
##-- Value: arch_requirement PUB delay + output_delay
set VALUE_max_delay [expr 1.250 + 0.500 * ${Virtual_AsyncPortClk_period} ]
# [AX] to ports adapted to obs port indices that connect to dto pins in wrapper
eval $my_set_max_delay ${VALUE_max_delay} \
                       -from [get_pins ${zcal_macro}/MtestMuxOut] \
                       -to   [get_ports {o_lpddr_obs[8] o_lpddr_obs[7]}]


################################################################################
## 3. Set design rule
##------------------------------------------------------------------------------
## Input drive, output load, transition
##
## One could use either set_driving_cell or set_input_transition depending on preference,
## we suggest set_driving_cell for this example
##
##    - Clocks should NOT have driving cell in DC, remove from driving_cell list
##------------------------------------------------------------------------------
## Please refer to the SolvNet Doc ID 014628:
## "How do set_driving_cell and set_load affect annotated boundary nets?"
################################################################################
##==============================================================================
## Inputs drive
##==============================================================================
set inputs_clocks            [get_ports -quiet [get_attribute -quiet [get_clocks] sources] ]
set inputs_not_clocks        [remove_from_collection [all_inputs] ${inputs_clocks}]
set inputs_not_clocks_not_bp [remove_from_collection $inputs_not_clocks [get_ports BP_*]]
#
set_driving_cell -lib_cell NAND2_D2_T_S6TL_C54L08 $inputs_not_clocks_not_bp


##==============================================================================
## Output load
##------------------------------------------------------------------------------
##    Based on your technology & strategy, you should choose your own values
##==============================================================================
set_load 0.020 [get_ports [all_outputs]]

##==============================================================================
## Transition
##------------------------------------------------------------------------------
##    Based on your technology & strategy, you should choose your own values
##==============================================================================
set_max_transition 0.125 [remove_from_collection [get_ports [all_outputs]] [get_ports BP_*]]
set_max_transition 0.125 [remove_from_collection [get_ports [all_inputs]] [get_ports BP_*]]
