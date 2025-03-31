################################################################################
## Copyright 2021-2023 Synopsys, Inc. All rights reserved
################################################################################
## SDC for lpddr5xphy
##------------------------------------------------------------------------------
## File:        dwc_lpddr5xphy_top.exceptions.tcl
## Description: Exceptions for top-level design
################################################################################

################################################################################
## File Contents
##------------------------------------------------------------------------------
## 1. TEMBUF cells
##
## 2. Sync cells
##
## 3. MtestMux
##
## 4. Hard Macro
##
## 5. Operation dependent exceptions
##
## 6. Set case analysis for PipeEn registers
##
## 7. Ideal Net for Synthesis
##
## 8. Misc
################################################################################


##===============================================================================
##------------------------------------------------------------------------------
## Pin name: GTECH vs. gate
##------------------------------------------------------------------------------
##===============================================================================
##-- Notes :
##-- Clock pin name may vary among different foundary std cell library, customer 
##-- should check and update per the std cell library used in synthesis.

set clockPin "CK"
set dataPin "D*"

# if {$flow == "syn_compile"} {
#   set clockPin "clocked_on"
#   set dataPin "*next_state*"
# } else {
#   set clockPin "CK"
#   set dataPin "D*"
# }


################################################################################
## 1. TEMBUF cells
##------------------------------------------------------------------------------
## TEMBUF cells are "Timing Exceptions Marker BUFfers",
## they specify the amount of time a path from launch point to capture point
## or a path through the cell can take.
##    - For paths through an TEMBUF cell's TEM_DIN with the same clock for launch and capture,
##      a set_max_delay command is used.
##    - For paths through an TEMBUF cell's TEM_DIN with different clocks for launch and capture,
##      a set_max_delay command is used.
## NOTE: The Enable pin is on DfiClk domain, it should be a single cycle path! The enable pin is called TEM_EN
##------------------------------------------------------------------------------
## List of TEMBUF types
##    (1) ALL_zCDCBUF_APBCLK_DfiClk_DLY700PS
##    (2) ALL_zCDCBUF_DfiClk_APBCLK_DLY700PS
##    (3) ALL_zCDCBUF_DfiClk_TDRCLK_DLY3333PS
##    (4) ALL_zCDCBUF_TDRCLK_DfiClk_DLY2467PS
##    (5) ALL_zCDCBUF_DfiClk_HardIPClk_DLY1250PS
##    (6) ALL_zCDCBUF_DfiClk_HardIPClk_DLY3333PS
##    (7) ALL_zCDCBUF_HardIPClk_DfiClkIn_DLY3333PS
##    (8) ALL_zCDCBUF_DfiClk_Untimed_DLY3333PS
##    (9) ALL_zCDCBUF_DfiClk_Untimed_DLY2667PS
##    (10) ALL_zCDCBUF_DfiClk_Untimed_DLY1250PS
##    (11) ALL_zCDCBUF_Untimed_Untimed_DLY3333PS
##    (12) ALL_zCDCBUF_Untimed_Untimed_DLY1250PS
##    (13) ALL_zCDCBUF_Untimed_DfiClk_DLY1667PS
################################################################################

##==============================================================================
## (1) ALL_zCDCBUF_APBCLK_DfiClk_DLY700PS
##------------------------------------------------------------------------------ 
## APBCLK to DfiClk: zCDCBUF_APBCLK_DfiClk_DLY700PS
##    - Template: zCDCBUF_APBCLK_DfiClk_DLY700PS
##    - Description: These TEMBUF cells have paths from APBCLK to DfiClk.
##                   These clocks are async, so set a max delay of the DLY value.
##    NOTE: The Enable pin is on DfiClk, it should be a single cycle path!,
##          the enable pin is called EN#
##==============================================================================
## [AX] Removed scan clocks from clocks lists as they are not defined in func mode.
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set TEMBUF_zCDCBUF_APBCLK_DfiClk_DLY700PS_pins \
	[get_pins	-hier *zCDCBUF_APBCLK_DfiClk_DLY700PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock - latency_to_clock
set VALUE_max_delay [expr 0.700*${cdc_scale} + ${clock_latency_APBCLK} - ${clock_latency_DfiClk}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_APBCLK_DfiClk_DLY700PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list pclk \
                                                  ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list DfiClk \
                                                ]] \
                          ${VALUE_max_delay}
}

##==============================================================================
## (2) ALL_zCDCBUF_DfiClk_APBCLK_DLY700PS
##------------------------------------------------------------------------------ 
## DfiClk to APBCLK: zCDCBUF_DfiClk_APBCLK_DLY700PS
##    - Template: zCDCBUF_DfiClk_APBCLK_DLY700PS
##    - Description: These TEMBUF cells have paths from DfiClk to APBCLK.
##                   These clocks are async, so set a max delay of the DLY value.
##==============================================================================
## [AX] Removed scan clocks from clocks lists as they are not defined in func mode.
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set TEMBUF_zCDCBUF_DfiClk_APBCLK_DLY700PS_pins \
	[get_pins	-hier *zCDCBUF_DfiClk_APBCLK_DLY700PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock - latency_to_clock
set VALUE_max_delay [expr 0.700*${cdc_scale} + ${clock_latency_DfiClk} - ${clock_latency_APBCLK}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_DfiClk_APBCLK_DLY700PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list DfiClk \
                                                  ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list pclk \
                                                ]] \
                          ${VALUE_max_delay} 
} 

##==============================================================================
## (3) ALL_zCDCBUF_DfiClk_TDRCLK_DLY3333PS
##------------------------------------------------------------------------------ 
## DfiClk to TDRCLK: zCDCBUF_DfiClk_TDRCLK_DLY3333PS
##    - Template: zCDCBUF_DfiClk_TDRCLK_DLY3333PS
##    - Description: These TEMBUF cells have paths from DfiClk to TDRCLK.
##                   These clocks are async, so set a max delay of the DLY value.
##==============================================================================
## [AX] Removed scan clocks from clocks lists as they are not defined in func mode.
set TEMBUF_zCDCBUF_DfiClk_TDRCLK_DLY3333PS_pins \
	[get_pins	-hier *zCDCBUF_DfiClk_TDRCLK_DLY3333PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock - latency_to_clock
set VALUE_max_delay [expr 3.333*${cdc_scale} + ${clock_latency_DfiClk} - ${clock_latency_TDRCLK}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_DfiClk_TDRCLK_DLY3333PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list DfiClk \
                                                  ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list TDRCLK \
                                                ]] \
                          ${VALUE_max_delay} 
}

##==============================================================================
## (4) ALL_zCDCBUF_TDRCLK_DfiClk_DLY2467PS
##------------------------------------------------------------------------------ 
## TDRCLK to DfiClk and UcClk: zCDCBUF_TDRCLK_DfiClk_DLY2467PS
##    - Template: zCDCBUF_TDRCLK_DfiClk_DLY2467PS
##    - Description: These TEMBUF cells have paths from TDRCLK to DfiClk and UcClk.
##                   These clocks are async, so set a max delay of the DLY value.
##==============================================================================
set TEMBUF_zCDCBUF_TDRCLK_DfiClk_DLY2467PS_pins \
	[get_pins	-hier *zCDCBUF_TDRCLK_DfiClk_DLY2467PS*/TEM_DIN*]

##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock - latency_to_clock
set VALUE_max_delay [expr 2.467*${cdc_scale} + ${clock_latency_TDRCLK} - ${clock_latency_DfiClk}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_TDRCLK_DfiClk_DLY2467PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list TDRCLK \
                                                  ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list DfiClk \
                                                ]] \
                          ${VALUE_max_delay} 
}

##------------------------------------------------------------------------------ 
##-- Value: arch_requirement*voltage_dependent_delay_coefficient + latency_from_clock - latency_to_clock
set VALUE_max_delay [expr 2.467*${cdc_scale} + ${clock_latency_TDRCLK} - ${clock_latency_UcClk}]

foreach_in_collection cur_TEMBUF ${TEMBUF_zCDCBUF_TDRCLK_DfiClk_DLY2467PS_pins} {
   eval $my_set_max_delay -from [get_clocks [list TDRCLK \
                                                  ]] \
                          -through ${cur_TEMBUF} \
                          -to [get_clocks [list UcClk]] \
                          ${VALUE_max_delay} 
}


##==============================================================================
## (5) ALL_zCDCBUF_DfiClk_HardIPClk_DLY1250PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_HardIPClk_DLY1250PS_pins \
        [get_pins -hier  *zCDCBUF_DfiClk_HardIPClk_DLY1250PS*/TEM_DIN*]

##==============================================================================
## (6) ALL_zCDCBUF_DfiClk_HardIPClk_DLY3333PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_HardIPClk_DLY3333PS_pins \
        [get_pins -hier  *zCDCBUF_DfiClk_HardIPClk_DLY3333PS*/TEM_DIN*]

##==============================================================================
## (7) ALL_zCDCBUF_HardIPClk_DfiClkIn_DLY3333PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_HardIPClk_DfiClkIn_DLY3333PS_pins \
        [get_pins -hier  *zCDCBUF_HardIPClk_DfiClkIn_DLY3333PS*/TEM_DIN*]

##==============================================================================
## (8) ALL_zCDCBUF_DfiClk_Untimed_DLY3333PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_Untimed_DLY3333PS_pins \
        [get_pins -hier  *zCDCBUF_DfiClk_Untimed_DLY3333PS*/TEM_DIN*]

##-- Move to io.tcl

##==============================================================================
## (9) ALL_zCDCBUF_DfiClk_Untimed_DLY2667PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_Untimed_DLY2667PS_pins \
        [get_pins -hier  *zCDCBUF_DfiClk_Untimed_DLY2667PS*/TEM_DIN*]

##==============================================================================
## (10) ALL_zCDCBUF_DfiClk_Untimed_DLY1250PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_DfiClk_Untimed_DLY1250PS_pins \
        [get_pins -hier  *zCDCBUF_DfiClk_Untimed_DLY1250PS*/TEM_DIN*]

##==============================================================================
## (11) ALL_zCDCBUF_Untimed_Untimed_DLY3333PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_Untimed_Untimed_DLY3333PS_pins \
        [get_pins -hier  *zCDCBUF_Untimed_Untimed_DLY3333PS*/TEM_DIN*]

##-- Move to io.tcl

##==============================================================================
## (12) ALL_zCDCBUF_Untimed_Untimed_DLY1250PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_Untimed_Untimed_DLY1250PS_pins \
        [get_pins -hier  *zCDCBUF_Untimed_Untimed_DLY1250PS*/TEM_DIN*]

##==============================================================================
## (13) ALL_zCDCBUF_Untimed_DfiClk_DLY1667PS
##------------------------------------------------------------------------------ 
##
##==============================================================================
set TEMBUF_zCDCBUF_Untimed_DfiClk_DLY1667PS_pins \
        [get_pins -hier  *zCDCBUF_Untimed_DfiClk_DLY1667PS*/TEM_DIN*]

##-- Move to io.tcl


################################################################################
## 2. Sync cells
##------------------------------------------------------------------------------
## The D-pin of sync cells should be constrained to the RTL transport delay values
################################################################################

##==============================================================================
## zSync5_DLY300PS_PRESETnSync        300ps
##------------------------------------------------------------------------------ 
## launch clock: APBCLK capture clock: DfiClk
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/zSync5_DLY300PS_PRESETnSync/DataIn[0]]

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_APBCLK} - ${clock_latency_DfiClk}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list pclk]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list DfiClk]]
}

##==============================================================================
## zSync5_DLY300PS_rd_ack_apb_lvl        300ps
##------------------------------------------------------------------------------ 
## launch clock: DfiClk capture clock: APBCLK
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/zSync5_DLY300PS_rd_ack_apb_lvl/DataIn[0]] 

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_DfiClk} - ${clock_latency_APBCLK}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list DfiClk]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list pclk]]
}

##==============================================================================
## zSync5_DLY300PS_ack_echo        300ps
##------------------------------------------------------------------------------ 
## launch clock: APBCLK capture clock: DfiClk
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/zSync5_DLY300PS_ack_echo/DataIn[0]] 

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_APBCLK} - ${clock_latency_DfiClk}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list pclk]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list DfiClk]]
}

##==============================================================================
## zSync5_DLY300PS_read_gc_apb        300ps
##------------------------------------------------------------------------------ 
## launch clock: DfiClk capture clock: APBCLK
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[7] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[6] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[5] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[4] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[3] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[2] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[1] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_read_gc_apb/DataIn[0] ] 

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_DfiClk} - ${clock_latency_APBCLK}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list DfiClk]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list pclk]]
}

##==============================================================================
## zSync5_DLY300PS_write_gc_dfi        300ps
##------------------------------------------------------------------------------ 
## launch clock: APBCLK capture clock: DfiClk
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[7] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[6] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[5] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[4] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[3] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[2] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[1] \
                         ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_apbfifo/u_fifo/zSync5_DLY300PS_write_gc_dfi/DataIn[0] ]

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_APBCLK} - ${clock_latency_DfiClk}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list pclk]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list DfiClk]]
}

##==============================================================================
## zSync5_DLY300PS_tdrCsrReqVld_dfi        300ps
##------------------------------------------------------------------------------ 
## launch clock: TDRCLK capture clock: DfiClk
##==============================================================================
## [AX] TODO, discuss with SNPS whether these max delays are required since they constrain a redundant cdc between two sync clocks.
set my_zSync5_list [list ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/dwc_ddrphy_apb2cfg/dwc_ddrphy_cfg2tdrmux/zSync5_DLY300PS_tdrCsrReqVld_dfi/DataIn[0]] 

set VALUE_max_delay [expr 0.300*${cdc_scale} + ${clock_latency_TDRCLK} - ${clock_latency_DfiClk}]

foreach item $my_zSync5_list {
   eval $my_set_max_delay ${VALUE_max_delay} \
                          -from [get_clocks [list TDRCLK]] \
                          -through [get_pins	$item] \
 -to [get_clocks [list DfiClk]]
}
################################################################################
## 3. MtestMux
##------------------------------------------------------------------------------
##    - Disable clock gating check and Stop clock propagation  
##    - get_cells  -hierarchical -filter "ref_name =~ *dwc_lpddr5xphy_mtestmux_pub*"
##  Notes:
##    - Please be aware "set_disable_clock_gating_check" is not SDC command, it will not be written out by write_sdc command.
##    - If customers use the SDC output from Design Compiler to run physical implementation, then this command need to be set in environment manually.
################################################################################
##-- [SS] hier prefix attached to paths
#
set_disable_clock_gating_check [get_cells [list	 ${DDR_HIER_PREFIX}/pub_top/tub/zMtestMux/*	\
                                                 ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/zMtestMux/*	\
                                                 ${DDR_HIER_PREFIX}/pub_top/pub/*/zMtestMux*/*	\
 	                                         ${DDR_HIER_PREFIX}/pub_top/pub/dxw*/*/zMtestMux*/* ]]

set_sense -type clock \
          -stop_propagation \
          [get_pins	-leaf -of [get_nets -of [get_pins	[list ${DDR_HIER_PREFIX}/pub_top/tub/zMtestMux/MtestMuxOut	\
                                                                      ${DDR_HIER_PREFIX}/pub_top/tub/MRTUB/zMtestMux/MtestMuxOut	\
                                                                      ${DDR_HIER_PREFIX}/pub_top/pub/*/zMtestMux*/MtestMuxOut	\
 	                                                              ${DDR_HIER_PREFIX}/pub_top/pub/dxw*/*/zMtestMux*/MtestMuxOut] ]] \
 -filter {pin_direction == out}]
## [AX] commented since scan clocks are not defined in func mode.
# set_sense -stop_propagation -clocks [get_clock scan_DfiClk] [get_pins		${DDR_HIER_PREFIX}/pub_top/tub/I_GateUcClk/ckgt/CK]


################################################################################
## 4. Hard Macro
##------------------------------------------------------------------------------
## Additional exceptions for Hard Macro no timing arc pins, there is no capture 
## clock on these pins.
##
################################################################################
##-- Launch and capture clock latencies should be factored in when calculating
##-- max delay value.
##-- + ${clock_latency_CLK} by -from [get_clocks CLK]
##-- - ${clock_latency_CLK} by -to   [get_clocks CLK]

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
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set dx4_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphydx4*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $dx4_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }


##==============================================================================
## (1-2) dx4: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set dx4_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphydx4*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEn_DQS \
                                    RxBypassPadEn_Ln* \
                                    RxBypassRcvEn_DQS \
                                    RxBypassRcvEn_Ln* ]

foreach cur_instance $dx4_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) dx5: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set dx5_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphydx5*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $dx5_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }


##==============================================================================
## (1-2) dx5: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set dx5_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphydx5*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEn_DQS \
                                    RxBypassPadEn_Ln* \
                                    RxBypassRcvEn_DQS \
                                    RxBypassRcvEn_Ln* ]

foreach cur_instance $dx5_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) acx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set acx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphyacx2*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $acx2_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }

##------------------------------------------------------------------------------
set cmosx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

## TODO: SNPS this throws warning that PwrOkOut is forced to be a timing startpoint. Expected?
set list_of_startpoints 	[list $cmosx2_macro/PwrOkOut]

set list_of_max_delay_pins  [list PwrOkVDD]
##-- Value: arch_requirement
set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

foreach cur_instance $acx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins	$list_of_startpoints] \
 -to [get_pins	${cur_instance}/${item}]
   }
}


##==============================================================================
## (1-2) acx2: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set acx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphyacx2*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEn_Ln*]

foreach cur_instance $acx2_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) csx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set csx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycsx2*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $csx2_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }

##------------------------------------------------------------------------------
set cmosx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

set list_of_startpoints 	[list $cmosx2_macro/PwrOkOut]

set list_of_max_delay_pins  [list PwrOkVDD]

##-- Value: arch_requirement
set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

foreach cur_instance $csx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins	$list_of_startpoints] \
 -to [get_pins	${cur_instance}/${item}]
   }
}


##==============================================================================
## (1-2) csx2: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set csx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycsx2*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEn_Ln*]

foreach cur_instance $csx2_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) ckx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set ckx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphyckx2*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $ckx2_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }


##==============================================================================
## (1-2) ckx2: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set ckx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphyckx2*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEnC \
                                    RxBypassPadEnT]

foreach cur_instance $ckx2_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) cmosx2: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
## [AX] removed scan clocks for now
set cmosx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_max_delay_pins    [list dfi_reset_n]

##-- Value: arch_requirement + latency_from_clock
set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} + ${clock_latency_DfiClk}]

foreach cur_instance $cmosx2_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_clocks $list_of_startpoint_clocks] \
                             -to   [get_pins	${cur_instance}/${item}]
   }
}

##------------------------------------------------------------------------------
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $cmosx2_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }


##==============================================================================
## (1-2) cmosx2: Type 2
##------------------------------------------------------------------------------
##    - Target: combinational bypass pins
##    - Method: set_false_path
##==============================================================================
## [AX] removed scan clocks for now
set cmosx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_bypass_pins       [list RxBypassPadEn_MEMRESET_L]

foreach cur_instance $cmosx2_macro {
   foreach item $list_of_bypass_pins {
      set_false_path -from    [get_clocks $list_of_startpoint_clocks] \
                     -through [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) master: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set master_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphymaster_top*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $master_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }

##------------------------------------------------------------------------------
set cmosx2_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphycmosx2*"]]

#TODO: SNPS this is forcing PwrOkLcl to be a timing startpoint, is this expected?
set list_of_startpoints 	[list $cmosx2_macro/PwrOkLcl]

set list_of_max_delay_pins  [list PwrOkVDDLcl]

##-- Value: arch_requirement
set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

foreach cur_instance $master_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins	$list_of_startpoints] \
 -to [get_pins	${cur_instance}/${item}]
   }
}


##==============================================================================
## (1-2) master: Type 2
##------------------------------------------------------------------------------
##    - Target: output pins
##    - Method: set_max_delay
##==============================================================================
## [AX] removed scan clocks for now
set master_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphymaster_top*"]]

set list_of_startpoint_clocks [list DfiClk ] 
# scan_DfiClk
set list_of_endpoint_clocks   [list DfiClk ] 
# scan_DfiClk
set list_of_max_delay_pins  [list csrPHYREV[*] ]

##-- Value: arch_requirement
set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period} - ${clock_latency_DfiClk}]

foreach cur_instance $master_macro {
   foreach item $list_of_max_delay_pins {
      eval $my_set_max_delay ${VALUE_max_delay} \
                             -from [get_pins	${cur_instance}/${item}] \
 -to [get_clocks $list_of_endpoint_clocks]
   }
}


##==============================================================================
## (1-1) zcal: Type 1
##------------------------------------------------------------------------------
##    - Target: input pins
##    - Method: set_max_delay
##==============================================================================
# [AX] TODO: discuss with SNPS how these scan mode constraints should be handled. No scan mode for now -> commented
# set zcal_macro [get_object_name [get_cells -hier  * -filter "ref_name=~*dwc_lpddr5xphyzcal_top*"]]

# set list_of_max_delay_pins  [list scan_mode]

# ##-- Value: arch_requirement
# set VALUE_max_delay [expr 4.0 * ${lpddr_clk_period}]

# foreach cur_instance $zcal_macro {
#    foreach item $list_of_max_delay_pins {
#       eval $my_set_max_delay ${VALUE_max_delay} \
#                              -to   [get_pins	${cur_instance}/${item}]
#    }
# }


################################################################################
## 5. Operation dependent exceptions
################################################################################


################################################################################
## 6. Set case analysis for PipeEn registers
################################################################################


################################################################################
## 7. Ideal Net for Synthesis
##------------------------------------------------------------------------------
##  During synthesis, it should be ideal.
##  During PNR, it should not be ideal and should be properly implemented.
##  Please reter to sections "Special Nets", "Special Signal Connections and shielding" in IG for details 
################################################################################

##==============================================================================
## set_ideal_network and set_dont_touch
##==============================================================================

if {$synopsys_program_name != "pt_shell"} {

  ##----------------------------------------
  ##-- Set ideal_network
  ##----------------------------------------
  ##-- VIO
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/VIO_RxAcVref]] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	[ list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/VIO_PwrOk ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_PwrOk ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/VIO_PwrOk] ] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/VIO_PwrOk] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_PwrOk] ]

  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	[ list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/VIO_TIELO_ACX* ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/VIO_TIEHI_ACX*] ] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_TIEHI] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_ForceEnable*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_ForceData*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_TIEHI*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_TIELO*] ]

  ##-- Analog signals
  ##-- Pclk
  ##-- Notes: Customer should check the PclkRptIn* connections too
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DWC_DDRPHYMASTER_topX/Pclk_master0_*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/PclkIn ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/PclkIn ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/PclkIn] ] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkIn] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/PclkIn*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkRptOut*]]
  ## TIELO* TIEHI* nets
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkRptIn* ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIELO_PclkRptIn ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/TIELO_PclkRptIn* ] ] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIELO_RxDQSInX8] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIEHI_RxDQSInX8 ]]

  ##-- RxDQSX8C,RxDQSX8T
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/RxDQSX8T] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/RxDQSX8C] ]

  ##-- BUMP
  set_ideal_network -no_propagate [get_nets -of_objects [get_ports {BP*}] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/BP*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/BP*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/BP*] ]
  set_ideal_network -no_propagate [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/BP*] ]


  ##----------------------------------------
  ##-- Set don't touch on those special nets
  ##----------------------------------------
  ##-- VIO
  set_dont_touch [get_nets -of_objects [get_pins	[ list ${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_RxAcVref ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/VIO_RxAcVref] ]] true

  set_dont_touch [get_nets -of_objects [get_pins	[ list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/VIO_PwrOk ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_PwrOk ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/VIO_PwrOk] ] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/VIO_PwrOk] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_PwrOk]] true

  set_dont_touch [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/VIO_TIELO_ACX* ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/VIO_TIEHI_ACX*]]] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_CMOSX2_TOP/VIO_TIEHI]] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_ForceEnable*] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_ForceData*] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_TIEHI*] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/VIO_TIELO*] ] true

  ##-- Analog signals
  ##-- Pclk
  ##-- Notes: Customer should check the PclkRptIn* connections too
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DWC_DDRPHYMASTER_topX/Pclk_master0_*] ] true
  set_dont_touch [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/PclkIn ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/PclkIn ${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/PclkIn]] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkIn] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/PclkIn*]] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkRptOut*] ] true
  ## TIELO* TIEHI* nets
  set_dont_touch [get_nets -of_objects [get_pins	[list ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/PclkRptIn* ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIELO_PclkRptIn ${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/TIELO_PclkRptIn* ] ]] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIELO_RxDQSInX8] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/TIEHI_RxDQSInX8] ] true

  ##-- RxDQSX8C,RxDQSX8T
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/RxDQSX8T] ] true
  set_dont_touch [get_nets -of_objects [get_pins	${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/RxDQSX8C] ] true

  ##-- BUMP
  set_dont_touch [get_nets -of_objects [get_ports {BP*}] ]  true
  set_dont_touch [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_DBYTE_WRAPPER_X*/dx_*/BP*] ] true
  set_dont_touch [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/ACX_*/BP*] ] true
  set_dont_touch [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/CSX_*/BP*] ] true
  set_dont_touch [get_nets -of_objects [get_pins		${DDR_HIER_PREFIX}/u_AC_WRAPPER_X*/DIFF_*/BP*] ] true


}
################################################################################
## 8. Misc
################################################################################

# [AX] removed since interfaces is tied-off
# set_false_path \
#  -from [get_ports awvalid_0] \
#  -to [get_ports cactive_ddrc] -comment "Specify false path between awvalid and cactive in xpi"
# set_false_path \
#  -from [get_ports arvalid_0] \
#  -to [get_ports cactive_ddrc] -comment "Specify false path between arvalid and cactive in xpi"
# set_false_path \
#  -from [get_ports wvalid_0] \
#  -to [get_ports cactive_ddrc] -comment "Specify false path between wvalid and cactive in xpi"
##-- [SS] Modified as dfi0_phyupd_req  dfi0_phymstr_req aren't ports
# set_false_path \
#  -through [get_pins i_uddrctl/dfi0_phyupd_req] \
#  -to [get_ports cactive_ddrc] -comment "Specify false path from dfi0_phyupd_req to cactive_ddrc because the path is asynchronous"
# set_false_path \
#  -through [get_pins i_uddrctl/dfi0_phymstr_req] \
#  -to [get_ports cactive_ddrc] -comment "Specify false path from dfi_phymstr_req to cactive_ddrc because the path is asynchronous"



##-- [SS] SRAM pin constraints
# [AX] replaced by ties
# set_case_analysis 1 [get_ports *_ADME[2]]
# set_case_analysis 0 [get_ports *_ADME[1]]
# set_case_analysis 0 [get_ports *_ADME[0]]

set all_memory_macros [get_cells -hier * -filter {is_memory_cell==true && (ref_name =~*rf*p* || ref_name =~*ra*p* || ref_name =~*ra1*p* || ref_name =~*rf1*p* || ref_name =~*rf2*p*)}]
# [AX] TODO check on SNPS database whether these are covered by lpddr_mbist.tcl exceptions or they are required to fix all timing violations
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~CRE1*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~CRE2*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~FCA1*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~FCA2*"] 7
# FRA and RREN only exist on the wrapper level, and go in to the macro through RRE1/2
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~FRA1*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~FRA2*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~RREN1*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~RREN2*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~RRE*"] 7
# set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name=~KCS*"] 7
# [AX] Tied in axelera wrappers 
# set_max_delay -from [get_ports {*_MCSWR}] 7
# set_max_delay -from [get_ports {*_MCSRD}] 7
# set_max_delay -from [get_ports {*_MCSW}] 7
# set_max_delay -from [get_ports {*_MCS}] 7
# [AX] Controlled/read by axelera quasis static registers
set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name==PRN"] 10.0
set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name==PDE"] 10.0
set_max_delay -through [get_pins -of_objects $all_memory_macros -filter "name==RET"] 10.0

# PCTL reset output relaxing
set_multicycle_path -setup 5 -through [get_pins ${INST_HIER}u_pctl/o_partition_rst_n[*]]
set_multicycle_path -hold  4 -through [get_pins ${INST_HIER}u_pctl/o_partition_rst_n[*]]

## AX PD TODO review if these case statements should propagate from the jtag controller instead.
set all_rfs [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf*p*}]
foreach_in_collection rf $all_rfs {
    set rfname [get_object_name $rf]
    set_case_analysis 1 [get_pins ${rfname}/ADME[2]]
    set_case_analysis 0 [get_pins ${rfname}/ADME[1]]
    set_case_analysis 0 [get_pins ${rfname}/ADME[0]]
    set_case_analysis 0 [get_pins ${rfname}/PDE]
    set_case_analysis 0 [get_pins ${rfname}/RET]
    set_case_analysis 0 [get_pins ${rfname}/DFTRAM]
    set_case_analysis 0 [get_pins ${rfname}/SE]
}
set all_srams [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*ra*p*}]
foreach_in_collection srams $all_srams {
    set sramname [get_object_name $srams]
    set_case_analysis 1 [get_pins ${sramname}/ADME[2]]
    set_case_analysis 0 [get_pins ${sramname}/ADME[1]]
    set_case_analysis 0 [get_pins ${sramname}/ADME[0]]
    set_case_analysis 0 [get_pins ${sramname}/PDE]
    set_case_analysis 0 [get_pins ${sramname}/RET]
    set_case_analysis 0 [get_pins ${sramname}/DFTRAM]
    set_case_analysis 0 [get_pins ${sramname}/SE]
}
set all_srams [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*ra1*p*}]
foreach_in_collection srams $all_srams {
    set sramname [get_object_name $srams]
    set_case_analysis 0 [get_pins ${sramname}/MCS[1]]
    set_case_analysis 1 [get_pins ${sramname}/MCS[0]]
    set_case_analysis 0 [get_pins ${sramname}/MCSW]
}
set all_rf1s [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf1*p*}]
foreach_in_collection rf1 $all_rf1s {
    set rf1name [get_object_name $rf1]
    set_case_analysis 0 [get_pins ${rf1name}/MCS[1]]
    set_case_analysis 1 [get_pins ${rf1name}/MCS[0]]
    set_case_analysis 0 [get_pins ${rf1name}/MCSW]
}
set all_rf2s [get_cells -hier  * -filter {is_memory_cell==true && ref_name =~*rf2*p*}]
foreach_in_collection rf2 $all_rf2s {
    set rf2name [get_object_name $rf2]
    set_case_analysis 0 [get_pins ${rf2name}/MCSRD[1]]
    set_case_analysis 1 [get_pins ${rf2name}/MCSRD[0]]
    set_case_analysis 0 [get_pins ${rf2name}/MCSWR[1]]
    set_case_analysis 1 [get_pins ${rf2name}/MCSWR[0]]
    set_case_analysis 0 [get_pins ${rf2name}/KCS]
}

## [AX] MCP to relax PHY pad bypass signals to 100MHz instead of having them at 300MHz (TDRCLK period)
set_multicycle_path -setup 3 -from [get_clocks TDRCLK] -through [get_pins u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/RxBypass*]
set_multicycle_path -setup 3 -from [get_clocks TDRCLK] -through [get_pins u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/TxBypass*]
set_multicycle_path -setup 2 -from [get_clocks TDRCLK] -through [get_pins u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/RxBypass*]
set_multicycle_path -setup 2 -from [get_clocks TDRCLK] -through [get_pins u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/i_DWC_lpddr5x_phy/TxBypass*]

# [AX] False path from functional clock through scan_DlyTestClk of PHY macros to scan_in
# TODO SNPS, why does case_analysis scan_mode 0 not disable the arcs from scan_DlyTestClk to scan_so in the PHY macros?
set_false_path -through [get_pins -hier */scan_DlyTestClk] -through [get_pins -hier */scan_so*] -through [get_pins -hier */scan_si*]
