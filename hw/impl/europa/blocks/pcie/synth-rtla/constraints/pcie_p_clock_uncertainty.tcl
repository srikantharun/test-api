############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_clock_uncertainty.tcl
# PIPE(UPCS+PHY) synthesis clocks properties setup
#
# ----------------------------------------------------------------------
# Copyright 2023 Synopsys, Inc.
#
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Read the Synopsys Statement on Inclusivity and Diversity at
# https://solvnetplus.synopsys.com/s/article/Synopsys-Statement-on-Inclusivity-and-Diversity
# ----------------------------------------------------------------------
#
#############################################################################################

## When picking in 3.0 labels remember to protect it in a variable such as !$remove_phy_func_clocks
#Added making the CDR Drift dictionary in uncertainity.tcl as con_vars is sourced earlier than the clocks.tcl
set dCDRDriftRXClocksTable [dict create]
for {set phy 0} {$phy < $nphys} {incr phy} {
 foreach lanes $phy_rx_lane_list {
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/pma/rx${lane}_ana_word_clk_i_8bit]]] > 0 } {

   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i_8bit       $RX_WCLK_DRIFT_MARGIN
  } else {
   dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i    $RX_WCLK_DRIFT_MARGIN
  }
  dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_div16p5_clk_i    $RX_WCLK_DRIFT_MARGIN
  dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_wclk            $RX_WCLK_DRIFT_MARGIN
  foreach clktype $rxgenclktype {
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_dwclk$clktype         $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_qwclk$clktype           $RX_QCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype          $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_qword_clk$clktype          $RX_QCLK_DRIFT_MARGIN
   set abc [dict get $dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_qwclk$clktype]
  }
  if { $usb4_supported } {
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i_sds       $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_dword_clk_i_sds     $RX_WCLK_DRIFT_MARGIN

  }
  if { $usb3_supported } {
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i_nonsds      $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_dword_clk_i_nonsds     $RX_WCLK_DRIFT_MARGIN

  }
  if { $tx_only_supported} {
   dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i       $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_dword_clk_i     $RX_WCLK_DRIFT_MARGIN

  }
  if { $pcie_supported } {
   dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i       $RX_WCLK_DRIFT_MARGIN
   dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_dword_clk_i     $RX_WCLK_DRIFT_MARGIN

   set abc [dict get $dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i]
   puts "i am here for  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_ana_word_clk_i got the vakue as $abc "
  }
  #dict set dCDRDriftRXClocksTable [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_dwclk*]         $RX_WCLK_DRIFT_MARGIN
  #dict set dCDRDriftRXClocksTable [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lanes}_asic_qwclk*]           $RX_QCLK_DRIFT_MARGIN
  ## When dig_* uncertanities would be added to the uncertanities file then add them here
  dict set dCDRDriftRXClocksTable  ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_word_clk           $RX_WCLK_DRIFT_MARGIN
  #if { !$integration } {
  # dict set dCDRDriftRXClocksTable ${phy_clk_prefix}rx${n}_asic_wclk   $RX_WCLK_DRIFT_MARGIN
  # dict set dCDRDriftRXClocksTable ${phy_clk_prefix}rx${n}_asic_dwclk  $RX_WCLK_DRIFT_MARGIN
  # dict set dCDRDriftRXClocksTable ${phy_clk_prefix}rx${n}_asic_qwclk  $RX_QCLK_DRIFT_MARGIN
  # }
 }
}


if { !$remove_upcs_scan_constraints } {
 #####SCAN CLOCKS###############
 #-- At speed scan clocks

 # Common per PHY
 ################################
 for {set phy 0} {$phy < $nphys} {incr phy} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 creating ASST clocks of phy $phy"
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_jtag_clk]    $JITTER_SCAN_JTAG    $DCU_SCAN_JTAG  $UNC_SCAN_HLD
 # set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb0_pclk]    $JITTER_SCAN_APB     $DCU_SCAN_APB   $UNC_SCAN_HLD
 # set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb1_pclk]    $JITTER_SCAN_APB     $DCU_SCAN_APB   $UNC_SCAN_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_fw_clk]    $JITTER_SCAN_FW      $DCU_SCAN_FW    $UNC_SCAN_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_cr_clk]     $JITTER_SCAN_CR      $DCU_SCAN_CR    $UNC_SCAN_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_dword_clk]   $JITTER_SCAN_DWORD $DCU_SCAN_DWORD  $UNC_SCAN_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_qword_clk]     $JITTER_SCAN_QWORD $DCU_SCAN_QWORD  $UNC_SCAN_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_occ_clk]      $JITTER_SCAN_OCC  $DCU_SCAN_OCC $UNC_SCAN_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_ref_clk]     $JITTER_SCAN_REF   $DCU_SCAN_REF  $UNC_SCAN_HLD

  if { !$jtag_rx_ana_dword_xf } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_word_clk]   $JITTER_SCAN_DWORD $DCU_SCAN_DWORD  $UNC_SCAN_HLD

  }
  if { $PMA_NAME == "c40" } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_tx_asic_clk]
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_rx_asic_clk]
  }
  #JIRA-P80001562-139515 Period kept as Mplla word clock as it has higher frequency for all modes
  if { $jtag_phy_scan_rx_dword } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_rx_dword_clk]    $JITTER_SCAN_DWORD $DCU_SCAN_DWORD  $UNC_SCAN_HLD

  }
 }

 # UPCS common scan clocks
 ################################
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pcs_clk]      $JITTER_SCAN_PCS_CLK $DCU_SCAN_PCS_CLK $UNC_SCAN_HLD
 if { !$tx_only_supported } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pma_clk]     $JITTER_SCAN_PCS_PMA_CLK $DCU_SCAN_PCS_PMA_CLK $UNC_SCAN_HLD
 } else {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_rd_clk]    $JITTER_SCAN_PCS_FIFO_RD $DCU_SCAN_PCS_FIFO_RD $UNC_SCAN_HLD

 }
 if { $hdmi_supported && $hdmi_54b_support } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_wr_clk]     $JITTER_SCAN_PCS_FIFO_WR $DCU_SCAN_PCS_FIFO_WR $UNC_SCAN_HLD

 }
 if { $pclk_as_phy_input } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_max_pclk]     $JITTER_SCAN_PCS_MAX_PCLK $DCU_SCAN_PCS_MAX_PCLK $UNC_SCAN_HLD

  if {  ($usb3_supported || $pcie_supported) && $pcs_scan_nonsds_pclk } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_in_pclk_nonsds_clk]  $JITTER_SCAN_PCS_NONSDS_PCLK $DCU_SCAN_PCS_NONSDS_PCLK $UNC_SCAN_HLD

  }
 } else {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pclk]      $JITTER_SCAN_PCS_PCLK $DCU_SCAN_PCS_PCLK $UNC_SCAN_HLD

 }
 if { !$tx_only_supported && $pcs_scan_rx_clk} {
  # Rx scan clock used for non-serdes rx-datapath
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_rx_clk_div]   $JITTER_SCAN_PCS_RX $DCU_SCAN_PCS_RX $UNC_SCAN_HLD
 }

 ##-- UPCS per lane -TX clocks
 ################################
 if { $pclk_as_phy_input } {
  if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
   for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
    foreach lane $pcs_lanes($link_num) {
     puts "\[Constraints Debug\] Info: [file tail [info script]] 2 creating ASST clocks of upcs lane $lane of link $link_num"
     # per upcs lane scan clock for all protocols
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_lane${lane}_in_pclk]     $JITTER_SCAN_PCS_IN_PCLK $DCU_SCAN_PCS_IN_PCLK $UNC_SCAN_HLD
    }
   }
  }
 }

 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]     $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
 ################################
 # GENERATED CLOCKS
 ################################

 ##-- Scan Generated clocks

 #####SCAN CLOCKS###############

 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  foreach lane $pcs_lanes($link_num) {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 3 creating generated clocks of shift clocks of upcs lane $lane of link $link_num"
   if { $pcie_supported } {
    # PCIe - Internal generated clocks per UPCS lane
    # Clocks - Mpll, Maxpclk, pma_clk(txX_clk), pcs_clk
    if { !$serdes_mode } {
     # Scan shift clock is created at flop output to meet shift timing arc for that flop,
     # Divide by 1 causes issues in FC, tool only considers comb arc.
     # Since frequency does not matter in this case as this clock does not go to D pin of any flop, it only goes to SI pin
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_scan_shift_clk]    $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
     # Generate scan shift clock is created at flop output to meet shift timing arc for that flop,
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_scan_shift_clk]   $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    }
    if { $pclk_as_phy_input } {
     #-- MAXPCLK
     # Scan shift clock is created at flop output to meet shift timing arc for that flop,
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_scan_shift_clk]  $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    } else {
     #-- OUTPUT PCLK
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_scan_shift_clk]    $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    }
   }
   if { $any_usb_supported } {
    # Functional clocks are generated at Q pin of these flops due to which CK->SI pathbrekas
    # Therefore, Scan clocks generated to meet timing of for scan shift path
    if { $usb3_supported || ($hdmi_supported && $hdmi_54b_support) } {
     # for tx only supported products no generated divided clocks are created, no scan shift arc break
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_div_flop_scan_shift_clk]    $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_div_flop_scan_shift_clk]    $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    }
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_div_flop_scan_shift_clk]   $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    if { $hdmi_supported && $hdmi_2p1_ctrl } {
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_maxpclk_16bit_deepclr_div2_flop_scan_shift_clk]   $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_10uiclk_16bit_deepclr_div2_flop_scan_shift_clk]    $JITTER_SCAN_SHIFT  $DCU_SCAN_SHIFT $UNC_SCAN_HLD
    }
   }
  }
 }
}

################################
# PRIMARY CLOCKS
################################
#####FUNCTIONAL CLOCKS##########

# Common per PHY
################################
set proto_type ""
for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 4 creating functionals clocks of phy $phy"
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk]      $JITTER_JTAG $DCU_JTAG $UNC_HLD
 #set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy_bs_cdr]  $JITTER_BS   $DCU_BS   $UNC_HLD
 #set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy_bs_udr]    $JITTER_BS   $DCU_BS   $UNC_HLD
 #set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_apb0_pclk]  $JITTER_APB  $DCU_APB  $UNC_HLD
 #set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_apb1_pclk]  $JITTER_APB  $DCU_APB  $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy_fw_clk]   $JITTER_FW   $DCU_FW   $UNC_HLD
 if { $usb4v2_supported } {
  set proto_type "nrz"
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_word_clk_pam3i]
 }
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_word_clk_${proto_type}i]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div_clk_i]     $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div16p5_clk_i]  $JITTER_MPLLAD16P5 $DCU_MPLLAD16P5 $UNC_HLD

 if { $dp20_supported } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_dp20_i]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
 }
 if { $dp14_supported} {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_dp14_i ]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
 }
 if { $hdmi_supported} {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_hdmi_i]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
 }
 if { ($usb3_supported) && !$dwc_dpalt_phy } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_i]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

 }
 if { $pcie_supported } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_i]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

 }
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_div_clk_i ] $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD

 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_clk_i]      $JITTER_REF    $DCU_REF   $UNC_HLD

 # Create an OCC clock on the same pin - this will NOT be divided by 2
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i]   $JITTER_REF    $DCU_REF   $UNC_HLD

 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_hdmi_div_clk_i]  $JITTER_HDMIBDIV   $DCU_MPLLBHDMI $UNC_HLD
 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy*/${pma_inst_name}/dco_ana_clkcal]]] > 0 } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcal]   $JITTER_DCO  $DCU_DCO $UNC_HLD
  }
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy*/${pma_inst_name}/dco_ana_clkcco]]] > 0 } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcco]   $JITTER_DCO  $DCU_DCO $UNC_HLD
  }
 }
 #--Per Phy tx
 ################################
 foreach lane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 5 creating functionals clocks of tx ${lane} of phy $phy"
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/${pma_inst_name}/tx${lane}_ana_word_clk_i]]] > 0 } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx${lane}_ana_word_clk_i] $JITTER_TXDW $DCU_TXDW  $UNC_HLD
  }
 }

 #--Per Phy rx
 ################################
 foreach lane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 6 creating functionals clocks of rx $rxlane of phy $phy"
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/pma/rx${lane}_ana_word_clk_i_8bit]]] > 0 } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i_8bit]  *
   # Create a jira for c40 clocks assign to AB and move on
  } else {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i]   $JITTER_RXDW $DCU_RXDW  $UNC_RX_HLD
  }
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_div16p5_clk_i]  $JITTER_RXD16P5  $DCU_RXD16P5 $UNC_RX_HLD

  # Multiple variants are defined for dword clock to meet timing requirement for serdes and non-serdes Rx path
  if { $usb4_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i_sds]   $JITTER_RXDW     $DCU_RXDW    $UNC_RX_HLD

  }
  if { $usb3_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i_nonsds]  $JITTER_RXDW     $DCU_RXDW    $UNC_RX_HLD

  }

  # Single clock is enough to meet timing requirement for Display PHYs
  if { $tx_only_supported} {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i]    $JITTER_RXDW     $DCU_RXDW    $UNC_RX_HLD

  }
  if { $pcie_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i]   $JITTER_RXDW     $DCU_RXDW    $UNC_RX_HLD

  }
  if { $jtag_mphy_support && !$dwc_dpalt_phy } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_clk_pwm_i]    $JITTER_MPWMR $DCU_RXPWM   $UNC_RX_HLD
  }
  if { $usb4v2_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_div28_clk_i]     *
   # AB Sir to add
  }
 }
}

##-- UPCS per lane
################################
if { $pclk_as_phy_input } {
 if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
  for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
   foreach lane $pcs_lanes($link_num) {
    puts "\[Constraints Debug\] Info: [file tail [info script]] 7 creating clocks of input pclks of upcs lane $lane of link $link_num"
    if { $usb3_supported } {
     if {$dwc_dpalt_phy} {
      set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_usb3_g1]         $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
      set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_usb3_g2]         $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
     } else {
      set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_usb3_g1]         $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD
      set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_usb3_g2]         $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
     }
    }
    if { $serdes_supported } {
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_serdes]    $JITTER_PCLK_SERDES $DCU_PCLK_SERDES   $UNC_HLD
    }
    if { $any_usb_supported } {
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_refclk]     $JITTER_REF     $DCU_REF    $UNC_HLD
    }
    if { $hdmi_supported  && $hdmi_54b_support } {
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pclk_hdmififo]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
    }
    if { $pcie_supported } {
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g12_phy$clksrc($link_num)] $JITTER_MPLLBW      $DCU_MPLLBW     $UNC_HLD
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g34_phy$clksrc($link_num)] $JITTER_MPLLAW      $DCU_MPLLAW     $UNC_HLD
     set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_refclk]  $JITTER_REF     $DCU_REF    $UNC_HLD

    }
   }
  }
 }
}

################################
# GENERATED CLOCKS
################################
#####FUNCTIONAL CLOCKS##########

##-- Functional Generated clocks

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 8 creating generated clocks of functional clocks for phy $phy"
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_fr_clk] $JITTER_REF    $DCU_REF   $UNC_HLD


 # timing arc and clock generating ref_ana_clk_i -> ref_div2_clk_i already exists in PMA lib.
 # Override it to enforce only timing arcs ref_ana_clk_i -> ref_div2_clk_i.
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_div2_clk_i] $JITTER_REF     $DCU_REF    $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_clk_i]  $JITTER_REF     $DCU_REF    $UNC_HLD



 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco] $JITTER_DCO      $DCU_DCO   $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcal] $JITTER_DCO $DCU_DCO $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clk_i] $JITTER_DCO      $DCU_DCO   $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_1_i]  $JITTER_DCO      $DCU_DCO   $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_2_i] $JITTER_DCO      $DCU_DCO   $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_3_i]  $JITTER_DCO      $DCU_DCO   $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_bit_clk_i]  $JITTER_DCO    $DCU_DCO $UNC_HLD

  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_word_clk_i]  $JITTER_DCO    $DCU_DCO $UNC_HLD
 }
 # Re-generated removed clocks here w.r.t to each clock created on mpllb_ana_word_clk_i
 set mpllbgenclk        [list dword qword oword word_fr]
 set mpllbgendiv        [list 2     4     8      1     ]
 set mpllb_word_fr_clk_name [get_bitblasted_signal mpllb_word_fr_clk $jtag_pma_bit_blasted]
 set mpllbgenclkpin     [list mpllb_dword_clk_i mpllb_qword_clk_i mpllb_oword_clk_i ${mpllb_word_fr_clk_name}]
 foreach genclk $mpllbgenclk genclkpin $mpllbgenclkpin gendiv $mpllbgendiv {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 9 creating generated clock variants of functional clocks for mpllb $genclk on pin $genclkpin with div factor $gendiv for phy $phy"
  if { $dp20_supported  } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_${genclk}_clk_dp20_i]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
  if { $dp14_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_${genclk}_clk_dp14_i]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
  if { $hdmi_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_${genclk}_clk_hdmi_i]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
  if { $pcie_supported || ($usb3_supported && !$dwc_dpalt_phy)} {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_${genclkpin}]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
 }

 if { $usb4v2_supported } {
  set data_rate      [list _nrz _pam3]
 } else {
  set data_rate      [list _]
 }
 set mpllagenclk    [list dword qword oword word_fr]
 set mpllagendiv    [list 2     4     8      1     ]
 set mpllaclksufix  [list clk_i clk_i clk_i clk]

 foreach drate $data_rate {
  foreach genclk $mpllagenclk gendiv $mpllagendiv gensufix $mpllaclksufix {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 10 creating generated clock variants of functional clocks for mplla $genclk with suffix $gensufix with div factor $gendiv and signaling $drate for phy $phy"
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_${genclk}_clk${drate}i]   $JITTER_MPLLAW      $DCU_MPLLAW     $UNC_HLD

  }
 }
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div33_clk_i]  $JITTER_MPLLAD16P5  $DCU_MPLLAD16P5 $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div66_clk_i]  $JITTER_MPLLAD16P5  $DCU_MPLLAD16P5 $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div_fr_clk]   $JITTER_MPLLADIV    $DCU_MPLLADIV   $UNC_HLD
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_div_fr_clk]  $JITTER_MPLLBDIV    $DCU_MPLLBDIV   $UNC_HLD


 # Per lane per PHY
 # Remove lib generated clocks based off rxX_ana_dword_clk
 # Re-generated those clocks here w.r.t to each clock created on rx_ana_dword_clk
 if { $usb4_supported } {
  set rxgenclktype    [list _sds  _nonsds]
 } elseif { $usb3_supported } {
  set rxgenclktype    [list _nonsds]
 } elseif { $pcie_supported || $tx_only_supported } {
  set rxgenclktype    [list ""]
 }
 foreach lane $phy_rx_lane_list {
  foreach clktype $rxgenclktype {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 11 creating generated clock variants of functional clocks for rx $lane of type $clktype for phy $phy"
   if { $PMA_NAME == "c40" || $jtag_pma_new_timing_arcs } {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype] $JITTER_RXDW    $DCU_RXDW $UNC_RX_HLD
   } else {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype] $JITTER_RXDW    $DCU_RXDW $UNC_RX_HLD
   }
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_qword_clk$clktype] $JITTER_RXDW    $DCU_RXDW $UNC_RX_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_dwclk$clktype]    $JITTER_RXDW    $DCU_RXDW   $UNC_RX_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_qwclk$clktype]    $JITTER_RXDW    $DCU_RXDW   $UNC_RX_HLD
   if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_owclk]]] > 0 } {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_oword_clk$clktype] *
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_owclk$clktype]    *
    # To be added by AB sir
   }
  }
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_word_clk]  $JITTER_RXDW    $DCU_RXDW $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_wclk]  $JITTER_RXDW    $DCU_RXDW   $UNC_RX_HLD
  if { $jtag_mphy_support && !$dwc_dpalt_phy } {
   if { $jtag_pma_new_timing_arcs } {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_clk_pwm] $JITTER_MPWMR $DCU_RXPWM $UNC_HLD
   } else {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_clk_pwm]  $JITTER_MPWMR $DCU_RXPWM $UNC_HLD
   }
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_pwm_clk_i]   $JITTER_MPWMR $DCU_RXPWM $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_pwm_word_clk_i] $JITTER_MPWMR $DCU_RXPWM $UNC_HLD
  }
 }
 set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk_n]  $JITTER_JTAG  $DCU_JTAG $UNC_HLD
}

foreach lane $pipe_lane_list {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 12 creating generated clocks for upcs lane $lane"
 # USB4, Display PHY - Internal generated clocks per UPCS lane
 # Clocks - Mpll, Maxpclk, pma_clk(txX_clk), pcs_clk
 #set pcs_lane_dp20_clks_
 if { $dp14_supported} {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp14_b]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp14_b] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
 }
 if { $dp20_supported } {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp20_a] $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp20_b] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp20_a]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp20_b]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
 }
 if { $hdmi_supported} {
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_hdmi_b]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_hdmi_b] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  if {  $hdmi_54b_support } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_hdmi_div2_b]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_hdmi_div2_b] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   # creating divby3 for FRL HDMI with macro mode
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpllb_hdmi_maxpclk_frlclk] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
  if { $hdmi_2p1_ctrl } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_maxpclk_16bit_deepclr_div2_hdmi_clk]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   if { $hdmi_max_pclk_final_div == 1 } {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpllclk_16bit_deepclr_div2_hdmi_clk]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   }
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_10uiclk_16bit_deepclr_div2_hdmi_clk] $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  }
 }
 if { $usb3_supported  } {

  if { $usb4_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb4_g23]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
  }

  if { $usb4v2_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb4_g4]  *
   ## To be added by AB sir
  }

  #if { $usb3_supported && !$dwc_dpalt_phy } {
  # set nom_usb3_opt_mpllb 1
  #} else {
  # set nom_usb3_opt_mpllb 0
  #}
  if { $nom_usb3_opt_mpllb } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g1]    $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g2]    $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g2]   $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g1] $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g2]           $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g1]           $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g1]   $JITTER_MPLLBDIV   $DCU_MPLLBDIV  $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g2]    $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD
  } else {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g1]   $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g2]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g2]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g1] $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g2]        $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g1]        $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g1]    $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
   set_clk_unc_info  [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g2]    $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
  }

  if { $nom_usb3_opt_mpllb } {
   if { $usb3_final_div_g2 == 1 } {
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g1_icg]      $JITTER_MPLLADIV   $DCU_MPLLADIV $UNC_HLD
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g2_icg]    $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
   }
  }

  if { $usb4_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_usb4_g23]        $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
  }
  if { $usb4v2_supported } {
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_usb4_g4] *
   # AB sir to add
  }
 }
}

if { $pcie_supported } {
 # PCIe - Internal generated clocks per UPCS lane
 # Clocks - Mpll, Maxpclk, pma_clk(txX_clk), pcs_clk
 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  foreach lane $pcs_lanes($link_num) {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 13 creating generated clocks for pcie of upcs lane $lane in link $link_num"
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]   $JITTER_MPLLBW      $DCU_MPLLBW     $UNC_HLD
   set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
   # Clocks defined for PCIe Non-Serdes arch for both Pclk as Phy Input/Output modes
   if { !$serdes_mode } {
    #-- PMA CLK
    # Generated PMA clock of div1 defined at mux output inside divider for rate g{3,4}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div1_icg_phy$clksrc($link_num)]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
    # Divided version of Pma clock (div2) defined at flop output inside divider for rate g{3,4}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num)]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
    # Divided version of Pma clock (div2) defined at flop output inside divider for rate g{1,2}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g12_div2_flop_phy$clksrc($link_num)]  $JITTER_MPLLBW      $DCU_MPLLBW     $UNC_HLD
    #-- PCS CLK
    # Generated PCS clock of div1 defined at mux output inside divider for rate g{3,4}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div1_icg_phy$clksrc($link_num)]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
    # Divided version of Pcs clock (div2) defined at flop output inside divider for rate g{3,4}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD
    # Divided version of Pcs clock (div2) defined at flop output inside divider for rate g{1,2}
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g12_div2_flop_phy$clksrc($link_num)]  $JITTER_MPLLBW      $DCU_MPLLBW     $UNC_HLD
   }
   if { $pclk_as_phy_input } {
    #-- MAXPCLK
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_div1_icg_phy$clksrc($link_num)]  $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD

    # Divided version of MaxPclk defined at flop output inside divider for rate g{3,4}
    # Divide factor is calculated based on input arguments min supported pipe_width, max_pclk_div_ratio
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_nondiv1_flop_phy$clksrc($link_num)]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD

    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_div1_icg_phy$clksrc($link_num)]    $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

    # Divided version of MaxPclk defined at flop output inside divider for rate g{1,2}
    # Divide factor is calculated based on input arguments min supported pipe_width, max_pclk_div_ratio
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_nondiv1_flop_phy$clksrc($link_num)]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

   } else {
    #-- OUTPUT PCLK
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_div1_icg_phy$clksrc($link_num)]    $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD

    # Divided version of Output Pclk defined at flop output inside divider for rate g{1,2}
    # Divide factor is calculated based on input arguments min supported pipe_width
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_nondiv1_flop_phy$clksrc($link_num)]   $JITTER_MPLLAW     $DCU_MPLLAW   $UNC_HLD

    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_div1_icg_phy$clksrc($link_num)]  $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

    # Divided version of Output Pclk defined at flop output inside divider for rate g{3,4}
    # Divide factor is calculated based on input arguments min supported pipe_width
    set_clk_unc_info [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_nondiv1_flop_phy$clksrc($link_num)]     $JITTER_MPLLBW     $DCU_MPLLBW    $UNC_HLD

   }
  }
 }
}

if { $DC_SHELL || $flow == "syn"} {
 # Clock network latency on pma rx clock to mimick latencies values in PMA lib when synthesis is run on pre CTS netlist
 # Post CTS actual latencies values to be applied
 # Referred from PHY constraints for USB4v2
 #
 #
 # JIRA P80001562-493704 - set clock network delay on apb0_pclk/fw_clk/scan_cr_clk pin to avoid timing violations on cr_reg_rd_data_d_reg
 set apb0_fw_scan_cr_clk_existed [get_clocks -quiet [list ${SNPS_CLOCK_PREFIX}phy?_apb0_pclk ${SNPS_CLOCK_PREFIX}phy?_fw_clk ${SNPS_CLOCK_PREFIX}phy?_scan_cr_clk]]
 if {[sizeof_collection $apb0_fw_scan_cr_clk_existed] > 0 } {
  set_clock_latency $APB0_FW_SCAN_CR_CLOCK_LATENCY $apb0_fw_scan_cr_clk_existed
 }

 for {set phy 0} {$phy < $nphys} {incr phy} {

  foreach rxlane $phy_rx_lane_list {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 6 adding clock latency in rx datapath based on pma latency to model ctl balancing for rx $rxlane of phy $phy"
   set rx_clk_name [get_bitblasted_signal rx${rxlane}_clk $jtag_pma_bit_blasted]
   if { $usb4_supported && $PMA_NAME == "c40" } {
    set pma_rx_latency [expr {0.900 * $TUNIT}]
    set_clock_latency $pma_rx_latency -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_wclk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    set_clock_latency $pma_rx_latency -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_?wclk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    if { !$remove_upcs_scan_constraints } {
     set_clock_latency $pma_rx_latency -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan*clk] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    }
    set_clock_latency $pma_rx_latency -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_div*clk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
   } else {
    set_clock_latency [expr {$RX_ASIC_WCLK_CLOCK_LATENCY * $TUNIT}] -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_wclk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    set_clock_latency [expr {$RX_ASIC_DWCLK_CLOCK_LATENCY * $TUNIT}] -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_dwclk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    set_clock_latency [expr {$RX_ASIC_QWCLK_CLOCK_LATENCY * $TUNIT}] -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_qwclk*] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    if { !$remove_upcs_scan_constraints } {
     set_clock_latency [expr {$SCAN_RX_CLOCK_LATENCY * $TUNIT}] -clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_*_dword_clk] [get_pins [prefixing $hiervar  phy${phy}/${pma_inst_name}/${rx_clk_name}]]
    }
   }
  }

  foreach txlane $phy_tx_lane_list {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 7 adding clock latency in tx datapath based on pma latency to model ctl blaancing for tx $txlane of phy $phy"
   set tx_clk_name [get_bitblasted_signal tx${txlane}_clk $jtag_pma_bit_blasted]
   set_clock_latency [expr {0.050 * $TUNIT}] [get_pins [prefixing $hiervar phy${phy}/pma/${tx_clk_name}]]
  }

  # set clock network delay on pma/cr_para_clk pin to avoid timing violations on pma/cr_para_addr
  set_clock_latency [expr {$PMA_CR_PARA_CLOCK_LATENCY * $TUNIT}] [get_pins [prefixing $hiervar phy${phy}/pma/cr_para_clk]]
 }
}    ;#end of DC_SHELL

