##==============================================================================
# Fusion Compiler settings information
#===============================================================================
# DfiClk and APBCLK.
# These clocks will be specified based on VDD value.
# APBCLK is equal to DfiClk or less.
# Table shows max supported frequency for each VDD value.
#===============================================================================
#  VDD                       [V]     0.75       0.70       0.65       0.60
#-------------------------------------------------------------------------------
#  DfiClk/APBCLK            [MHz]    1067       1067        800        533
#-------------------------------------------------------------------------------
#  scan_Virtual             [MHz]     300        100        100        100
#  scan_clk                 [MHz]     300        100        100        100
#  Virtual_BypassClk        [MHz]     300        100        100        100
#  Virtual_ControlBypassClk [MHz]     150        100        100        100
#==============================================================================

## The variable "mode" is preset to define frequncies depending on used mode.
## TODO: SNPS, is there any use in keeping the other modes besides func_800?
## AXE will not use the faster ones, and the slower ones should be covered implicitly?
## shift and atspeed mode will be defined using separate files.
#FC scenario3 800MHz
set lpddr_clk_period                [expr 1.250]
set ao_clk_period                   [expr 10.0]
# No scan clocks defined in AX func mode
# set scan_Virtual_period             [expr 10]
# set scan_clk_period                 [expr 10]
set Virtual_BypassClk_period        [expr 10]
set Virtual_ControlBypassClk_period [expr 10]

# [AX] after discussion with SNPS, for functional constraints, only func_800 is relevant, others are implicitly met when using this one. -> Commented setup below.
# set mode func_800
# switch $mode {
#     func_1067    
#     {
#         #FC scenario1 1067MHz
#         set lpddr_clk_period                [expr 0.938]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 3.330]
#         set scan_clk_period                 [expr 3.330]
#         set Virtual_BypassClk_period        [expr 3.330]
#         set Virtual_ControlBypassClk_period [expr 6.660]
#     }
#     func_800    {
#         #FC scenario3 800MHz
#         set lpddr_clk_period                [expr 1.250]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 10]
#         set scan_clk_period                 [expr 10] ## TODO: SNPS is reviewing the period
#         set Virtual_BypassClk_period        [expr 10]
#         set Virtual_ControlBypassClk_period [expr 10]
#     }
#     ## TODO: check that mode impacts case statements correctly for func mode (also check this for the scan at speed and scan shift modes)
#     ## TODO DFT Is equivalent scan at speed and impact of it should be ported to our scan at speed constraints{
#     func_800_scan_300  
#         #FC scenario5 800MHz, scan 300MHz 
#         set lpddr_clk_period                [expr 1.250]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 3.330]
#         set scan_clk_period                 [expr 3.330]
#         set Virtual_BypassClk_period        [expr 3.330]
#         set Virtual_ControlBypassClk_period [expr 6.660]
#     }
#     func_600    {
#         #FC scenario2 600MHz
#         set lpddr_clk_period                [expr 1.667]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 10]
#         set scan_clk_period                 [expr 10]
#         set Virtual_BypassClk_period        [expr 10]
#         set Virtual_ControlBypassClk_period [expr 10]
#     }
#     func_533    {
#         #FC scenario4 533MHz
#         set lpddr_clk_period                [expr 1.876]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 10]
#         set scan_clk_period                 [expr 10]
#         set Virtual_BypassClk_period        [expr 10]
#         set Virtual_ControlBypassClk_period [expr 10]
#     }
#     ## TODO: SNPS needs to check whether we need to keep these (in case they have impact further down the line)
#     dc_mode1 {
#         #DC mode1 from 0MHz to 800MHz, VDD 0.75V
#         set lpddr_clk_period                [expr 1.250]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 3.330]
#         set scan_clk_period                 [expr 3.330]
#         set Virtual_BypassClk_period        [expr 3.330]
#         set Virtual_ControlBypassClk_period [expr 6.660]
#     }
#     dc_mode2 {
#         #DC mode2 from 801MHz to 1067MHz, VDD 0.75V
#         set lpddr_clk_period                [expr 0.938]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 3.330]
#         set scan_clk_period                 [expr 3.330]
#         set Virtual_BypassClk_period        [expr 3.330]
#         set Virtual_ControlBypassClk_period [expr 6.660]
#     }
#     default {
#         #default mode 1067MHz, VDD 0.75V
#         set lpddr_clk_period                [expr 0.938]
#         set ao_clk_period                   [expr 10.0]
#         set scan_Virtual_period             [expr 3.330]
#         set scan_clk_period                 [expr 3.330]
#         set Virtual_BypassClk_period        [expr 3.330]
#         set Virtual_ControlBypassClk_period [expr 6.660]
#     }
# }

##----------------------------------------------------------------------------------------

##-- TDRCLK frequency is 300MHz 
set TDRCLK_period               [expr 3.33]

##-- InternalBypassClk_period frequency is 100MHz, used to time the internal bypass paths
set InternalBypassClk_period    [expr 10.00]

##-- InternalBypassGenUcClk_period frequency is 100MHz, used to time the internal bypass paths
set InternalBypassGenUcClk_period    [expr 10.00]

##-- Virtual_InternalBypassClk_period frequency is 100MHz, used to time the internal bypass paths
set Virtual_InternalBypassClk_period [expr 10.00]

##-- Virtual_AsyncPortClk frequency is 100MHZ 
set Virtual_AsyncPortClk_period [expr 10.00]

set half_DfiClk              [expr $lpddr_clk_period  * 0.5]

##-- UcClk frequency is DfiClk_frequency
set UcClk_period             [expr $lpddr_clk_period * 1 ]
# set scan_UcClk_period        [expr $lpddr_clk_period * 1 ]


set bisr_clk_period [expr 20.0]
set ssn_bus_clk_period [expr 10.0]
set lpddr_async_virt_clk_period $lpddr_clk_period

##----------------------------------------------------------------------------------------
## Variables for Clock Uncertainty.  
##    Values used here are examples, and not guarantee signoff quality.
##    Based on your technology & strategy, you should choose your own values
##----------------------------------------------------------------------------------------
## AX: SNPS will take these from guidelines doc
##-- freq_dependent are a percent of the clock cycle
# set default_clk_uncertainty_setup_freq_dependent      0.025
# set default_clk_uncertainty_hold_freq_dependent      0.000

# ##-- duty_cycle_percent is only for 1/2 cycle paths 
# ##-- and is how much the clock is expected to not be 50/50
# set default_clk_duty_cycle_percent                    0.010

# ##-- freq_indepenedent is in nS and it is added on top of the dependent piece
# ##-- Comments:
# ##-- Values used here are examples, and not guarantee signoff quality
# ##-- Customer should choose your own value based on your technology and strategy (pre-CTS and post-CTS) 

# set default_clk_uncertainty_setup_freq_independent    0.150
# set default_clk_uncertainty_hold__freq_independent    0.050

##=========================================================================================
## 1. CTRL CLOCKS
##=========================================================================================

# [AX] Main functional input clocks
# 100MHz always on clock, NOT PROPAGATED TO SUBSYS
create_clock [get_ports {i_ao_clk}] -name i_ao_clk -period $ao_clk_period -waveform [list 0 [expr $ao_clk_period*0.5]] 
# 800MHz ddr clock, ROOT OF ALL SUBSYS CLOCKS
create_clock [get_ports {i_lpddr_clk}] -name i_lpddr_clk -period $lpddr_clk_period -waveform [list 0 [expr $lpddr_clk_period*0.5] ]

# [AX] Generated functional clocks
# Generated clock for main lpddr_clk used to drive all but pll_ref and pll_byp clock.
set lpddr_clk_pin [get_pins u_pctl/g_clkdiv[0].u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
create_generated_clock -name lpddr_clk \
                            -source [get_ports i_lpddr_clk] \
                            -master_clock i_lpddr_clk \
                            -divide_by 1 \
                            -add \
                            $lpddr_clk_pin

# Bypass version of the lpddr_clk, used to constrain some paths that can only be activated when the PHY is in bypass mode.
# Original SNPS frequence was 100MHz so dividing main 800MHz input clock with 8 here.
create_generated_clock -name lpddr_bypass_clk \
                            -source [get_ports i_lpddr_clk] \
                            -master_clock i_lpddr_clk \
                            -edges {1 2 17} \
                            -add \
                            $lpddr_clk_pin

# Generated clock for lpddr_pll_ref_clk
set lpddr_pll_ref_clk_pin [get_pins u_pctl/g_clkdiv[1].u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
create_generated_clock -name lpddr_pll_ref_clk \
                            -source [get_ports i_lpddr_clk] \
                            -master_clock i_lpddr_clk \
                            -divide_by 1 \
                            -add \
                            $lpddr_pll_ref_clk_pin


#-- [AX] modified SNPS create_clock statements to generated clocks based on pctl output clocks going through individual clock buffers for each SNPS clock
## Fanout of each snps clock should still be identical to situation before wrapper insertion
# CTRL SNPS clocks
create_generated_clock -name aclk_0 \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -add -divide_by 1 \
                        [get_pins i_axi_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK]

create_generated_clock -name core_ddrc_core_clk \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -add \
                        -divide_by 1 \
                        [get_pins i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK]

create_generated_clock -name core_ddrc_core_clk_apbrw \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -divide_by 1 \
                        -add \
                        [get_pins i_core_ddrc_core_clk_apbrw_clk_buf/u_tc_lib_clk_inv1/Y]

create_generated_clock -name pclk \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -divide_by 1 \
                        -add \
                        [get_pins i_pclk_clk_buf/u_tc_lib_clk_inv1/Y]

create_generated_clock -name pclk_apbrw \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -divide_by 1 \
                        -add \
                        [get_pins i_pclk_apbrw_clk_buf/u_tc_lib_clk_inv1/Y]

create_generated_clock -name sbr_clk \
                        -source $lpddr_clk_pin \
                        -master_clock [get_clocks lpddr_clk] \
                        -divide_by 1 \
                        -add \
                        [get_pins i_sbr_clk_clk_buf/u_tc_lib_clk_inv1/Y]
# PHY SNPS clocks

## [AX] make sure the buffer cells are kept
set_dont_touch [get_cells i_axi_low_power_interface/u_clk_gate/u_tc_lib_clk_en ]
set_dont_touch [get_cells i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en ]
set_dont_touch [get_cells i_core_ddrc_core_clk_apbrw_clk_buf/u_tc_lib_clk_inv1 ]
set_dont_touch [get_cells i_pclk_clk_buf/u_tc_lib_clk_inv1 ]
set_dont_touch [get_cells i_pclk_apbrw_clk_buf/u_tc_lib_clk_inv1 ]
set_dont_touch [get_cells i_sbr_clk_clk_buf/u_tc_lib_clk_inv1 ]

##-- [SS] Four generated clocks in Subsystem 
##-- [AX] modified to have lpddr_clk as master clock
create_generated_clock -name core_ddrc_core_clk_arb \
                          -source [get_pins i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK] \
                          -master_clock core_ddrc_core_clk \
                          -divide_by 1 \
                          -add \
                          [get_pins	$axelera_hier/i_DWC_ddr_ss_clk_blk/u_axi_clk_gate/gate_clk ]
                          #[get_pins $axelera_hier/i_DWC_ddr_ss_clk_blk/u_axi_clk_gate/ckgt/ECK ] commented cause premapped cell file does not contain std-cells but behavioral model instead.
                          # TODO: SNPS revert commenting

create_generated_clock -name core_ddrc_core_clk_te \
                          -source [get_pins i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK] \
                          -master_clock core_ddrc_core_clk \
                          -divide_by 1 \
                          -add \
                          [get_pins	$axelera_hier/i_DWC_ddr_ss_clk_blk/u_core_clk_gate/gate_clk ]
                          # [get_pins $axelera_hier/i_DWC_ddr_ss_clk_blk/u_core_clk_gate/ckgt/ECK ] commented cause premapped cell file does not contain std-cells but behavioral model instead.
                          # TODO: SNPS revert commenting

create_generated_clock -name bsm_clk_1 \
                          -source [get_pins i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK] \
                          -master_clock core_ddrc_core_clk \
                          -divide_by 1 \
                          -add \
                          [get_pins	$axelera_hier/i_DWC_ddr_ss_clk_blk/u1_DWC_ddr_ss_clk_gate_bsm/gate_clk ]
                          # [get_pins $axelera_hier/i_DWC_ddr_ss_clk_blk/u_core_clk_gateckgt/ECK ] commented cause premapped cell file does not contain std-cells but behavioral model instead.
                          # TODO: SNPS revert commenting

create_generated_clock -name bsm_clk_0 \
                          -source [get_pins i_ddrc_low_power_interface/u_clk_gate/u_tc_lib_clk_en/ECK] \
                          -master_clock core_ddrc_core_clk \
                          -divide_by 1 \
                          -add \
                          [get_pins	$axelera_hier/i_DWC_ddr_ss_clk_blk/u0_DWC_ddr_ss_clk_gate_bsm/gate_clk ]
                          # [get_pins $axelera_hier/i_DWC_ddr_ss_clk_blk/u0_DWC_ddr_ss_clk_gate_bsmckgt/ECK ] commented cause premapped cell file does not contain std-cells but behavioral model instead.
                          # TODO: SNPS revert commenting

# [AX] DFt clock definitions
## bisr clk
create_clock -name bisr_clk -period $bisr_clk_period -waveform [list 0 [expr $bisr_clk_period*0.5] ] [get_ports {bisr_clk}]

## ssn bus clk
create_clock -name ssn_bus_clk -period $ssn_bus_clk_period -waveform [list 0 [expr $ssn_bus_clk_period*0.5] ] [get_ports {ssn_bus_clk}]

##-- TDRCLK
## [AX] DFT flow replaced TRDCLK by tck
create_clock -name "TDRCLK"       [get_ports tck] -period $TDRCLK_period

# Generated clocks for AX DFT logic
create_generated_clock -name bap1_tck -source [get_ports {tck}] -combinational  -add -master_clock [get_clocks {TDRCLK}] [get_pins {u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_mbist_bap_inst/tessent_persistent_cell_BUF_C_TCK/u_tc_lib_clk_inv1/Y}] 
create_generated_clock -name bap1_interfaces_tck -source [get_ports {tck}] -combinational  -add -master_clock [get_clocks {TDRCLK}] [get_pins {u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_mbist_bap_inst/tessent_persistent_cell_BUF_I_TCK/u_tc_lib_clk_inv1/Y}] 
create_generated_clock -name bscan_update_clock -source [get_ports {tck}]  -divide_by 1 -invert  -add -master_clock [get_clocks {TDRCLK}] [get_pins {u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_bscan_interface_I/tessent_persistent_cell_update_clock_gater_inst/u_tc_lib_clk_en/ECK}] 
create_generated_clock -name bscan_capture_shift_clock -source [get_ports {tck}]  -divide_by 1  -add -master_clock [get_clocks {TDRCLK}] [get_pins {u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/snps_ddr_subsystem_rtl1_tessent_bscan_interface_I/tessent_persistent_cell_capture_shift_clock_gater_inst/u_tc_lib_clk_en/ECK}] 


##=========================================================================================
## 2. PHY CLOCKS
##=========================================================================================
##----------------------------------------------------------------------------------------
## 2.1 Create Functional Clocks (all using the single clock input def from axelera)
##----------------------------------------------------------------------------------------
##-- DfiClk 
## -- [AX] Adapted create clocks to create_generated_clocks on individual clock buffers per original SNPS clock port. -> Fanout cone of clocks is still the same.
create_generated_clock -name "DfiClk" \
                        -source $lpddr_clk_pin \
                        -divide_by 1 \
                        -add \
                        -master_clock [get_clocks lpddr_clk] \
                        [get_pins i_dficlk_clk_buf/u_tc_lib_clk_inv1/Y]

##-- PllRefClk
create_generated_clock -name "PllRefClk" \
                        -source $lpddr_pll_ref_clk_pin \
                        -divide_by 1 \
                        -add \
                        -master_clock [get_clocks lpddr_pll_ref_clk] \
                        [get_pins i_pllrefclk_clk_buf/u_tc_lib_clk_inv1/Y]
##-- PllBypClk
create_generated_clock -name "PllBypClk" \
                        -source $lpddr_pll_ref_clk_pin \
                        -divide_by 1 \
                        -add \
                        -master_clock [get_clocks lpddr_pll_ref_clk] \
                        [get_pins i_pllbypclk_clk_buf/u_tc_lib_clk_inv1/Y]

# Make sure also these buffers are kept
set_dont_touch [get_cells i_dficlk_clk_buf/u_tc_lib_clk_inv1]
set_dont_touch [get_cells i_pllrefclk_clk_buf/u_tc_lib_clk_inv1]
set_dont_touch [get_cells i_pllbypclk_clk_buf/u_tc_lib_clk_inv1]
##-- APBCLK
#create_clock -name "APBCLK"       [get_ports APBCLK] -period $APBCLK_period
#[SS] Common pclk at Subsystem level for both PHY and controller APB interfaces


##------------------------------------------------------------------------------
## InternalBypassClk: Internal bypass clock
##    - Used to define all internal bypass signals, both inputs and outputs.
##      Valid internal bypass paths are: reg -> HM -> port; port -> HM -> reg; reg -> HM -> reg
##------------------------------------------------------------------------------
## [AX]: taking the lpddr_bypass_clk as master clock here. This clock is 1/8 of the frequency of the lpddr_clk, matching the original 100MHz from SNPS for the interal bypass clock.
create_generated_clock -name "InternalBypassClk" \
                        -source $lpddr_clk_pin \
                        -divide_by 1 \
                        -add \
                        -master_clock [get_clocks lpddr_bypass_clk] \
                        [get_pins i_dficlk_clk_buf/u_tc_lib_clk_inv1/Y]
# create_clock -name "InternalBypassClk" [get_pins  $axelera_hier/DfiClk] -period $InternalBypassClk_period -add


##----------------------------------------------------------------------------------------
##-- 2.2 Create Generated clocks
##----------------------------------------------------------------------------------------
##-- UcClk
##-- [AX] Clock gate pin is different for target library
create_generated_clock -name UcClk \
                          -source [get_pins i_dficlk_clk_buf/u_tc_lib_clk_inv1/Y] \
                          -master_clock DfiClk \
                          -divide_by 1 \
                          -add \
                          [get_pins	${DDR_HIER_PREFIX}/pub_top/tub/I_GateUcClk/CG ]


##------------------------------------------------------------------------------
## InternalBypassGenUcClk: Generated clock for internal bypass clock
##    - Used to define all internal bypass signals, related to UcClk.
##------------------------------------------------------------------------------
##-- InternalBypassGenUcClk
###-- [SS] CLock gate pin is different for target library
## [AX] updated source to pick DfiClk std-cell clock buffer
create_generated_clock -name InternalBypassGenUcClk \
                       -source [get_pins i_dficlk_clk_buf/u_tc_lib_clk_inv1/Y] \
                       -master_clock InternalBypassClk \
                       -divide_by 1 \
                       -add \
                       [get_pins ${DDR_HIER_PREFIX}/pub_top/tub/I_GateUcClk/CG]


##----------------------------------------------------------------------------------------
## 2.3 Create ATPG Clocks
##----------------------------------------------------------------------------------------
## [AX] scan clocks on DFI, APB and TDR do not need to exist in func mode
## [AX] scan_clk and scan_DlyTestClk, come from an OCC that will let through the func clock when test mode is set 0 with case statement, not additional clock def required.
##-- scan_DfiClk is muxed in outside of the phy top, scan capture is at DfiClk freq
# create_clock -name "scan_DfiClk"   [get_pins  $axelera_hier/DfiClk] -period $DfiClk_period -add

##-- scan_APBCLK is muxed in outside of the phy top, scan capture is at APBCLK freq
#[SS] only one pclk at Subsystem level
# create_clock -name "scan_APBCLK"   [get_ports pclk] -period $APBCLK_period -add

##-- scan_TDRCLK
# create_clock -name "scan_TDRCLK"   [get_ports TDRCLK] -period $TDRCLK_period -add

##-- scan_UcClk
##-- create_clock -name "scan_UcClk" [get_ports scan_UcClk] -period $scan_UcClk_period -waveform "0 $half_DfiClk" -add

##-- scan_clk
# create_clock -name "scan_clk" [get_ports scan_clk] -period $scan_clk_period

##-- scan_DlyTestClk
# create_clock -name "scan_DlyTestClk" [get_ports scan_DlyTestClk] -period $scan_DlyTestClk_period

##----------------------------------------------------------------------------------------
## 2.4 Create Virtual Clocks for IO
##----------------------------------------------------------------------------------------
##-- Virtual_BypassClk is used to define all Bypass* signals, both inputs and outputs, for external tx/rx paths
##-- Virtual_InternalBypassClk is used on Bypass ports and to constrain internal Bypass paths.
##-- Virtual_ControlBypassClk is used to constrain control bypass paths
##-- These ports are independent of all other clocks
create_clock -name "Virtual_BypassClk"          -period $Virtual_BypassClk_period
create_clock -name "Virtual_ControlBypassClk"   -period $Virtual_ControlBypassClk_period
create_clock -name "Virtual_InternalBypassClk"  -period $Virtual_InternalBypassClk_period

##-- Virtual_AsynsPortClk is used for Ports which are async to all clocks 
create_clock -name "Virtual_AsyncPortClk"       -period $Virtual_AsyncPortClk_period

##-- scan_Virtual is used for all scan_* ports, both inputs and outputs
## [AX]: no active scan clocks in func mode, commented
# create_clock -name "scan_Virtual"               -period $scan_Virtual_period

##-- Virtual_* clocks to constraint the IO ports
create_clock -name "Virtual_DfiClk"             -period $lpddr_clk_period
# [SS] pclk_virt created at SS level for common APB interface
#create_clock -name "Virtual_APBCLK"             -period $APBCLK_period
create_clock -name "Virtual_TDRCLK"             -period $TDRCLK_period

# [AX] Virtual clock defs for top-level axelera clocks for IO constraints
create_clock -name i_lpddr_clk_virt -period $lpddr_clk_period -waveform [list 0 [expr $lpddr_clk_period*0.5]]
create_clock -name i_lpddr_clk_async_virt -period $lpddr_async_virt_clk_period -waveform [list 0 [expr $lpddr_async_virt_clk_period*0.5]]
create_clock -name i_ao_clk_virt -period $ao_clk_period -waveform [list 0 [expr $ao_clk_period*0.5]]
create_clock -name bisr_clk_virt -period $bisr_clk_period -waveform [list 0 [expr $bisr_clk_period*0.5] ]
create_clock -name ssn_bus_clk_virt -period $ssn_bus_clk_period -waveform [list 0 [expr $ssn_bus_clk_period*0.5] ]
# [AX] Individual virtual clock for noc_clk_en IO port so it can have a different clock latency from others, only use if required.
# create_clock -name i_noc_clken_virt -period $lpddr_clk_period -waveform [list 0 [expr $lpddr_clk_period*0.5]]

##=========================================================================================
## 3. Clock Relationships
##=========================================================================================

##-----------------------------------------------------------------------------------------
##Create a clock variable of different sets of clock 
##-----------------------------------------------------------------------------------------


##-- Clocks_Bypass include bypass clocks                                                                                                  
set Clocks_Bypass                  [get_clocks [list lpddr_bypass_clk \
                                                     Virtual_BypassClk \
                                                     Virtual_ControlBypassClk \
                                                     InternalBypassClk \
                                                     InternalBypassGenUcClk \
                                                     Virtual_InternalBypassClk ]]

##-- [AX] Added lpddr clock driving all sync clock buffers for each individual clock
##-- [SS] Added controller clocks which are synchronous to DfiClk
##-- DfiClk clock group
set Clocks_DfiClk                  [get_clocks [list DfiClk \
                                                     Virtual_DfiClk \
                                                     UcClk \
                                                     core_ddrc_core_clk \
                                                     core_ddrc_core_clk_apbrw \
                                                     sbr_clk \
                                                     core_ddrc_core_clk_arb \
                                                     core_ddrc_core_clk_te \
                                                     bsm_clk_1 \
                                                     bsm_clk_0 \
                                                     pclk_apbrw \
                                                     aclk_0 \
                                                     pclk \
                                                     pclk_apbrw \
                                                     lpddr_clk \
                                                     ]]
## [AX] made clock var for always-on clocks
set Clocks_AO       [get_clocks [list i_ao_clk \
                                        i_ao_clk_virt]]

## [AX] made clock var for input clock
set Clocks_top      [get_clocks [list i_lpddr_clk i_lpddr_clk_virt i_lpddr_clk_async_virt]]

##-- Functional clock group
set Clocks_func                    [get_clocks *] 


##-- DFT clock group
set Clocks_dft                      [get_clocks [list \
                                    ssn_bus_clk \
                                    ssn_bus_clk_virt \
                                    bisr_clk \
                                    bisr_clk_virt \
                                    bap1_tck \
                                    bap1_interfaces_tck \
				    bscan_capture_shift_clock \
				    bscan_update_clock \
                                    ]]
##-- [SS] Added pclk and pclk_virt
## [AX] Added lpddr_pll_ref_clk
##-- Clocks_Other include clocks except DfiClk and Bypass 
set Clocks_Other                   [get_clocks [list PllBypClk \
                                                     PllRefClk \
                                                     TDRCLK \
                                                     bisr_clk \
                                                     Virtual_TDRCLK \
                                                     Virtual_AsyncPortClk \
                                                     lpddr_pll_ref_clk \
                                                    ]]


##-- Clocks_None should be empty - all clocks should be referenced above.  If there is a clock in Clocks_None, please resolve where it should go.
set Clocks_None                    [remove_from_collection $Clocks_func   [add_to_collection  $Clocks_DfiClk  [list $Clocks_Other $Clocks_Bypass $Clocks_AO $Clocks_top $Clocks_dft]] ]

#-- Prints clock information
puts "INFO: (Clocks) TOP clocks      - [get_object_name $Clocks_top]"
puts "INFO: (Clocks) AO clocks       - [get_object_name $Clocks_AO]"
puts "INFO: (Clocks) DFI clocks      - [get_object_name $Clocks_DfiClk]"
puts "INFO: (Clocks) Bypass clocks   - [get_object_name $Clocks_Bypass]"
puts "INFO: (Clocks) DFT clocks      - [get_object_name $Clocks_dft]"
puts "INFO: (Clocks) Other clocks    - [get_object_name $Clocks_Other]"

if {[llength $Clocks_None] > 0} {
  puts "Error: There is/are clock(s) that are in none of the clock groups. Please verify their name(s) is/are defined correctly in the constraint.tcl file: [get_object_name ${Clocks_None}] "
} 


##----------------------------------------------------------------------------------------
## The clock Virtual_BypassClk is pure async to rest of Clocks_non_dft.
## The clocks *InternalBypassClk are pure async to rest of Clocks_non_dft.
##----------------------------------------------------------------------------------------
##-- Clocks are async to every group else.
##-- [SS] Added controller clocks also for completeness
##-- [AX] Adapted to pickup axelera top-level clocks
##-- [AX] TODO: SNPS, why is TDRCLK in the list that is synchronous to all core clocks, TDRCLK is not sync to all these clocks.
set_clock_groups -asynchronous \
                 -name separate_bypass_clock_group_1 \
                 -group [list Virtual_InternalBypassClk \
                              Virtual_ControlBypassClk \
                              Virtual_BypassClk ] \
                 -group [list DfiClk \
                              Virtual_DfiClk \
                              UcClk \
                              core_ddrc_core_clk \
                              core_ddrc_core_clk_apbrw \
                              sbr_clk \
                              PllBypClk \
                              PllRefClk \
                              pclk \
                              TDRCLK \
                              bap1_tck \
                              bap1_interfaces_tck \
                              pclk_apbrw \
                              Virtual_TDRCLK \
                              aclk_0 \
                              core_ddrc_core_clk_arb \
                              core_ddrc_core_clk_te \
                              bsm_clk_1 \
                              bsm_clk_0 \
                              i_lpddr_clk \
                              i_lpddr_clk_virt \
                              lpddr_clk \
                              lpddr_pll_ref_clk ]

##-- [AX] Adapted to pickup axelera top-level clocks
set_clock_groups -asynchronous \
                 -name separate_bypass_clock_group_2 \
                 -group [list lpddr_bypass_clk \
                              InternalBypassClk \
                              InternalBypassGenUcClk ] \
                 -group [list DfiClk \
                              Virtual_DfiClk \
                              UcClk \
                              core_ddrc_core_clk \
                              core_ddrc_core_clk_apbrw \
                              sbr_clk \
                              PllBypClk \
                              PllRefClk \
                              pclk \
                              TDRCLK \
                              bap1_tck \
                              bap1_interfaces_tck \
                              pclk_apbrw \
                              Virtual_TDRCLK \
                              aclk_0 \
                              core_ddrc_core_clk_arb \
                              core_ddrc_core_clk_te \
                              bsm_clk_1 \
                              bsm_clk_0 \
                              i_lpddr_clk \
                              i_lpddr_clk_virt \
                              lpddr_clk \
                              lpddr_pll_ref_clk ]

set_clock_groups -physically_exclusive \
                 -name  separate_clocks_on_same_port_1 \
                 -group [list lpddr_clk DfiClk UcClk] \
                 -group [list lpddr_bypass_clk InternalBypassClk InternalBypassGenUcClk ]

set_clock_groups -asynchronous \
                 -name differentiate_bypass_async_clock_group \
                 -group [list lpddr_bypass_clk \
                              InternalBypassClk \
                              InternalBypassGenUcClk \
                              Virtual_InternalBypassClk ] \
                 -group Virtual_ControlBypassClk \
                 -group [list Virtual_BypassClk \
                              Virtual_AsyncPortClk ]

set_clock_groups -asynchronous -allow_paths \
                 -name bypass_async_clock_group \
                 -group Virtual_AsyncPortClk \
                 -group Virtual_BypassClk

# [AX] make DFT bisr_clk clock async to all other clocks
set_clock_groups -asynchronous -name bisr_clk_async_to_all -group [list bisr_clk bisr_clk_virt ]

# [AX] make DFT ssn_bus clock async to all other clocks
set_clock_groups -asynchronous -name ssn_bus_clk_async_to_all -group [list ssn_bus_clk ssn_bus_clk_virt]

##-- InternalBypassClk associated to DfiClk port together with Virtual_InternalBypassClk  
##-- are used to define internal bypass paths.
##-- The path: DfiClk port -> HM -> port is not valid internal bypass path. 
# [AX] changed get_port DfiClk to get_clock DFiClk.
set_false_path -from [get_clock DfiClk] \
               -to   [get_clock Virtual_InternalBypassClk]

##----------------------------------------------------------------------------------------
## Set Sync Clock Groups
##----------------------------------------------------------------------------------------
##-- Clocks are async to every group else.
##-- [SS] Added controller clock groups also
## [AX] modified to add top-level clocks, and moved PLL clocks in main lpddr clock group since they are sync.
set_clock_groups -asynchronous -allow_paths \
                 -name Functional_Group \
                 -group [ get_clocks [list i_ao_clk i_ao_clk_virt ]] \
                 -group [list TDRCLK Virtual_TDRCLK bap1_tck bap1_interfaces_tck bscan_update_clock bscan_capture_shift_clock] \
                 -group Virtual_AsyncPortClk \
                 -group i_lpddr_clk_async_virt \
                 -group [list DfiClk \
                              Virtual_DfiClk \
                              UcClk \
                              core_ddrc_core_clk \
                              core_ddrc_core_clk_apbrw \
                              sbr_clk \
                              pclk \
                              pclk_apbrw \
                              aclk_0 \
                              core_ddrc_core_clk_arb \
                              core_ddrc_core_clk_te \
                              bsm_clk_1 \
                              bsm_clk_0 \
                              i_lpddr_clk \
                              i_lpddr_clk_virt \
                              lpddr_clk \
                              PllBypClk PllRefClk lpddr_pll_ref_clk ]

##------------------------------------------------------------------------------
##-- The clock Virtual_BypassClk is pure async to rest of Clocks.
##-- The clocks *InternalBypass*Clk are pure async to rest of Clocks.
##------------------------------------------------------------------------------
##-- Vitual_InternalBypassClk is used to constraint all the internal Bypass paths which are from ports to registers in PUB or from registers in PUB to ports, or from registers in PUB through Hardip's bypass pins to registers in PUB.
##-- So there will be no path between Virtual_InternalBypassClk with any Virtual* clocks.
##-- Virtual_BypassClk is used to constraint all the external tx/rx Bypass paths which are from TxBypass* ports to BP or from BP to RxBypassData*, so there will be no path between Virtual_BypassClk with any function clocks    
##-- Virtual_ControlBypassClk is used to constraint all the external control Bypass paths which are from RxBypass*En* ports to RxBypass*Dat* ports.
##-- So there will be no path between Virtual_ControlBypassClk with any other clocks.
set_false_path -from [remove_from_collection $Clocks_DfiClk [get_clocks [list Virtual_DfiClk ]] ] \
               -to   [get_clocks {Virtual_BypassClk}]

set_false_path -from [get_clocks {Virtual_BypassClk}] \
               -to   [remove_from_collection $Clocks_DfiClk [get_clocks [list Virtual_DfiClk ]] ] 

set_false_path -from [get_clocks {Virtual_InternalBypassClk}] \
               -to   [get_clocks [list Virtual_InternalBypassClk Virtual_BypassClk Virtual_AsyncPortClk]]

set_false_path -from [get_clocks [list Virtual_InternalBypassClk Virtual_BypassClk Virtual_AsyncPortClk]] \
               -to   [get_clocks {Virtual_InternalBypassClk }]

set_false_path -from [remove_from_collection $Clocks_DfiClk [get_clocks [list Virtual_DfiClk ]] ] \
               -to   [get_clocks {Virtual_ControlBypassClk }]

set_false_path -from [get_clocks {Virtual_ControlBypassClk }] \
               -to   [remove_from_collection $Clocks_DfiClk [get_clocks [list Virtual_DfiClk ]] ]

set_false_path -from [get_clocks {Virtual_ControlBypassClk }] \
               -to   [get_clocks [list Virtual_InternalBypassClk Virtual_BypassClk ]]

set_false_path -from [get_clocks [list Virtual_InternalBypassClk Virtual_BypassClk ]] \
               -to   [get_clocks {Virtual_ControlBypassClk }]

# [AX] General constraints from/to ao_clk and other clocks.
set_max_delay $ao_clk_period -from [get_clocks [list i_ao_clk i_ao_clk_virt]] -to [remove_from_collection [all_clocks] [get_clocks [list i_ao_clk i_ao_clk_virt]]] -ignore_clock_latency
set_max_delay $ao_clk_period -to [get_clocks [list i_ao_clk i_ao_clk_virt]] -from [remove_from_collection [all_clocks] [get_clocks [list i_ao_clk i_ao_clk_virt]]] -ignore_clock_latency
set_false_path -hold -from [get_clocks [list i_ao_clk i_ao_clk_virt]] -to [remove_from_collection [all_clocks] [get_clocks [list i_ao_clk i_ao_clk_virt]]]
set_false_path -hold -to [get_clocks [list i_ao_clk i_ao_clk_virt]] -from [remove_from_collection [all_clocks] [get_clocks [list i_ao_clk i_ao_clk_virt]]]

# [AX] False paths from/to bap1_tck clocks
set_false_path -from [get_clocks [list DfiClk UcClk core_ddrc_core_clk]] -to [get_clocks [list bap1_tck bap1_interfaces_tck]]
set_false_path -to [get_clocks [list DfiClk UcClk core_ddrc_core_clk]] -from [get_clocks [list bap1_tck bap1_interfaces_tck]]
##------------------------------------------------------------------------------
## Since set "-allow_path" to enable timing analysis between the specified clock groups, 
## set a large delay value 200ns instead of INIFINITY between async clock groups. If the 
## path go through CDCBUF, then the max delay will be overridden by specific CDCBUF.
##------------------------------------------------------------------------------
##-- [SS] Changed APBCLK to Subsystem definition
## [AX] SNPS, are you sure that all paths to and from these clocks to all other clocks are non-sync when in cC async options are deselected?
## These are constrains that go very wide.
foreach cur_clock [list "TDRCLK Virtual_TDRCLK" \
                        PllRefClk \
                        PllBypClk \
                        Virtual_AsyncPortClk \
                        Virtual_BypassClk \
                        ] {
   set col_clocks [get_clocks ${cur_clock}]
   set col_others [remove_from_collection ${Clocks_func} ${col_clocks}]
   set_max_delay  200   -from ${col_clocks} -to ${col_others}
   set_max_delay  200   -from ${col_others} -to ${col_clocks}
   set_false_path -hold -from ${col_clocks} -to ${col_others}
   set_false_path -hold -from ${col_others} -to ${col_clocks}
}

##------------------------------------------------------------------------------------
## Set Physically Exclusive Clock Groups
##------------------------------------------------------------------------------------
##-- Clocks_scan are physically exclusive to all functional_clocks.  Either scan_mode or functional mode
## [AX] no scan clocks defined since DFT case statement put OCCs in func mode letting only func clock through
# set_clock_groups -physically_exclusive \
                #  -name separate_atpgClk_group \
                #  -group $Clocks_scan \
                #  -group $Clocks_func

##-----------------------------------------------------------------------------------------
## Set Async Relationship for Scan Clocks
##----------------------------------------------------------------------------------------- 
##-- Clocks_scan are async to all other scan_clocks, scan clocks are assumed to always be one-hot
## [AX] no scan clocks defined since DFT case statement put OCCs in func mode letting only func clock through
# set_clock_groups -asynchronous \
#                  -name atpg_clocks \
#                  -group scan_DfiClk \
#                  -group scan_APBCLK \
#                  -group scan_clk \
#                  -group scan_TDRCLK \
#                  -group scan_DlyTestClk \
#                  -group scan_Virtual

##=========================================================================================
## 4. Clock Uncertainties
##=========================================================================================
##-- Please check uncertainty with the foundry requirement.
## [AX] TODO: SNPS, adapt so guidelines in signoff document are met.
##-----------------------------------------------------------------------------------------
## 4.1 Inter-Clock Uncertainties
##-----------------------------------------------------------------------------------------
# foreach_in_collection my_clock [remove_from_collection [get_clocks *] [get_clocks [list UcClk InternalBypassGenUcClk \
#                                                                                           ]]] {
#     set clk_name   [get_attribute $my_clock full_name]
#     set clk_period [get_attribute $my_clock period]
#     set clk_uncertainty_full [expr ${clk_period}*${default_clk_uncertainty_setup_freq_dependent} + ${default_clk_uncertainty_setup_freq_independent}]
#     set clk_uncertainty_half [expr ${clk_period}*(${default_clk_uncertainty_setup_freq_dependent}+${default_clk_duty_cycle_percent})  + ${default_clk_uncertainty_setup_freq_independent}  ]
#     set clk_uncertainty_zero [expr ${clk_period}*${default_clk_uncertainty_hold__freq_dependent} + ${default_clk_uncertainty_hold__freq_independent}]
#     echo "${clk_name} Period: ${clk_period} Uncertainties  Full: ${clk_uncertainty_full} Half: ${clk_uncertainty_half} Zero: ${clk_uncertainty_zero}"

#     set_clock_uncertainty -setup $clk_uncertainty_full ${my_clock}
#     set_clock_uncertainty -setup $clk_uncertainty_half -rise_from ${my_clock} -fall_to ${my_clock}
#     set_clock_uncertainty -setup $clk_uncertainty_half -fall_from ${my_clock} -rise_to ${my_clock}
#     set_clock_uncertainty -hold  $clk_uncertainty_zero ${my_clock}
#     set_clock_uncertainty -hold  $clk_uncertainty_half -rise_from ${my_clock} -fall_to ${my_clock}
#     set_clock_uncertainty -hold  $clk_uncertainty_half -fall_from ${my_clock} -rise_to ${my_clock}
# }

##-----------------------------------------------------------------------------------------
## 4.2 Clock uncertainty for generated clocks
##-----------------------------------------------------------------------------------------
##-- UcClk
# set my_clock [get_clocks {UcClk} ]
# set clk_name   [get_attribute $my_clock full_name]
# set clk_period $UcClk_period
# set clk_uncertainty_full [expr ${clk_period}*${default_clk_uncertainty_setup_freq_dependent} + ${default_clk_uncertainty_setup_freq_independent}]
# set clk_uncertainty_zero [expr ${clk_period}*${default_clk_uncertainty_hold__freq_dependent} + ${default_clk_uncertainty_hold__freq_independent}]
# echo "${clk_name} Period: ${clk_period} Uncertainties  Full: ${clk_uncertainty_full} Zero: ${clk_uncertainty_zero}"
# set_clock_uncertainty -setup $clk_uncertainty_full ${my_clock}
# set_clock_uncertainty -hold  $clk_uncertainty_zero ${my_clock}

# ##-- InternalBypassGenUcClk
# set my_clock [get_clocks {InternalBypassGenUcClk} ]
# set clk_name   [get_attribute $my_clock full_name]
# set clk_period $InternalBypassGenUcClk_period
# set clk_uncertainty_full [expr ${clk_period}*${default_clk_uncertainty_setup_freq_dependent} + ${default_clk_uncertainty_setup_freq_independent}]
# set clk_uncertainty_zero [expr ${clk_period}*${default_clk_uncertainty_hold__freq_dependent} + ${default_clk_uncertainty_hold__freq_independent}]
# echo "${clk_name} Period: ${clk_period} Uncertainties  Full: ${clk_uncertainty_full} Zero: ${clk_uncertainty_zero}"
# set_clock_uncertainty -setup $clk_uncertainty_full ${my_clock}
# set_clock_uncertainty -hold  $clk_uncertainty_zero ${my_clock}


##------------------------------------------------------------------------------------------
## 4.3 Cross-Clock Uncertainties 
##------------------------------------------------------------------------------------------
##-- Comment: There is no addtional uncertainty needed between async cross-clocks
##-- All async cross-clock paths will be timed by set_max_delay - capture clock uncertainty

##=========================================================================================
## 5. Design Transitions
##-----------------------------------------------------------------------------------------
##-- [Recommendation]
##-- set_max_transition 10% on clock path
##-- set_max_transition 20% on the datapath
##-- Based on your technology & strategy, you should choose your own values
##=========================================================================================
##
## [AX] updated to meet signoff guidelines
## 300ps on all datapaths
## 10% of clock with a max of 125ps for slower clocks -> 125ps for all clocks
set_max_transition 0.3 [current_design]
set_max_transition 0.125 -clock_path [all_clocks]

# set_max_transition [expr 0.2 * $lpddr_clk_period] -data_path  $Clocks_DfiClk

# set_max_transition [expr 0.2 * $lpddr_clk_period] -data_path  $Clocks_Pll_Clk
# set_max_transition [expr 0.1 * $lpddr_clk_period] -clock_path $Clocks_Pll_Clk

# #-- [SS] Modified by SS
# set_max_transition [expr 0.2 * $APBCLK_period] -data_path  [get_clocks pclk]
# set_max_transition [expr 0.1 * $APBCLK_period] -clock_path [get_clocks pclk]


# set_max_transition [expr 0.2 * $DfiClk_period] -data_path  [get_clocks UcClk]
# set_max_transition [expr 0.1 * $DfiClk_period] -clock_path [get_clocks UcClk]

# set_max_transition [expr 0.2 * $PllRefClk_period] -data_path  [get_clocks PllRefClk]
# set_max_transition [expr 0.1 * $PllRefClk_period] -clock_path [get_clocks PllRefClk]

# set_max_transition [expr 0.2 * $DfiClk_period] -data_path [get_clocks PllBypClk]
# set_max_transition [expr 0.1 * $DfiClk_period] -clock_path [get_clocks PllBypClk]

##-- The scan_*Clk max_tran value is set as per maximum frequency for ATPG at-speed clock
# set_max_transition [expr 0.2 * $DfiClk_period] -data_path  [get_clocks {scan_clk scan_DlyTestClk}]
# set_max_transition [expr 0.1 * $DfiClk_period] -clock_path [get_clocks {scan_clk scan_DlyTestClk}]


##=========================================================================================
## 6. Clock Latency
##------------------------------------------------------------------------------
## Set clock latency for adjusting value of set_max_delay
## These values will be used in dwc_lpddr5xphy_top.io.tcl and dwc_lpddr5xphy_top.exceptions.tcl
##=========================================================================================

##-- For STA customer must provide clock latency values based on design data.
##-- The intent of the set_max_delay command is to go
##-- from the launch point to the capture point in the specified time
##-- The value of set_max_delay shouldn't include the clock latency, so we account
##-- for it in the timing reports using the clock latency values.

##-- If using the following optional setting "-ignore_clock_latency", all clock_latency_* and clock_skew_* variables are required to be set to "0"
##-- set my_set_max_delay "set_max_delay -ignore_clock_latency "
##-- Otherwise, set below clock_latency_* and clock_skew_* accordingly after CTS.

set my_set_max_delay "set_max_delay -ignore_clock_latency"


## [AX] Up to snps to set these if required. At top-level, our IO constraints should be met.
## If IO budget needs to include clock latency, desired clock latency should be discussed with AX
## and IO budget can be adapted based on that.
# Values used in the max_delay statement in io delays and exceptions
set clock_latency_DfiClk                         0.0
set clock_latency_UcClk                          0.0
set clock_latency_APBCLK                         0.0
set clock_latency_TDRCLK                         0.0


# if {$flow != "syn_sta"} {
#    set clock_latency_DfiClk                        0
#    set clock_latency_UcClk                         0
#    set clock_latency_APBCLK                        0
#    set clock_latency_TDRCLK                        0
# }
#    set clock_latency_DfiClk                        0
#    set clock_latency_UcClk                         0
#    set clock_latency_APBCLK                        0
#    set clock_latency_TDRCLK                        0

# if {$flow == "syn_sta"} {
#    set_clock_latency ${clock_latency_DfiClk}                        [get_clocks [list DfiClk \
#                                                                                  Virtual_DfiClk \
#                                                                                  scan_DfiClk ]]    
#    set_clock_latency ${clock_latency_UcClk}                         [get_clocks [list UcClk \
#                                                                                         ]]
#    ##-- [SS] Modified by SS
#    set_clock_latency ${clock_latency_APBCLK}                        [get_clocks {pclk \
#                                                                                  pclk_virt \
#                                                                                  scan_APBCLK  }]
#    set_clock_latency ${clock_latency_TDRCLK}                        [get_clocks {TDRCLK \
#                                                                                  Virtual_TDRCLK \
#                                                                                  scan_TDRCLK  }]
#    set_clock_latency 0                                              [get_clocks {Virtual_InternalBypassClk \
#                                                                                  Virtual_ControlBypassClk \
#                                                                                  Virtual_BypassClk}]
# }
