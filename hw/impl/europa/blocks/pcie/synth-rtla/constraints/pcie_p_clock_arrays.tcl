############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_clock_arrays.tcl
#
# PIPE(UPCS+PHY) synthesis all clock arrays definitions
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

#clock collection arrays
if { $usb3_supported || $tx_only_supported } {
 if { $pclk_as_phy_input && $usb3_supported } {
  if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
   lappend lane_usb3_g1_pclks  ${SNPS_CLOCK_PREFIX}lane*_pclk_usb3_g1
   lappend lane_usb3_g2_pclks  ${SNPS_CLOCK_PREFIX}lane*_pclk_usb3_g2
   append_to_collection ip_all_func_pclks [get_clocks $lane_usb3_g1_pclks]
   append_to_collection ip_all_func_pclks [get_clocks $lane_usb3_g2_pclks]
  }
 }

 foreach lane $pipe_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 creating arrays for pipe lane $lane"
  if { $dp20_supported } {
   lappend pcs_lane_dp20_a_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp20_a
   lappend pcs_lane_dp20_a_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp20_a
   lappend pcs_lane_dp20_b_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp20_b
   lappend pcs_lane_dp20_b_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp20_b
  }
  if { $dp14_supported } {
   lappend pcs_lane_dp14_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_dp14_b
   lappend pcs_lane_dp14_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_dp14_b
  }
  if { $hdmi_supported } {
   lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_hdmi_b
   lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_hdmi_b
   if {  $hdmi_54b_support } {
    lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pma_hdmi_div2_b
    lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_hdmi_div2_b
   }
   if { $hdmi_2p1_ctrl } {
    lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_10uiclk_16bit_deepclr_div2_hdmi_clk
    lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_maxpclk_16bit_deepclr_div2_hdmi_clk
    if { $hdmi_max_pclk_final_div == 1 } {
     lappend pcs_lane_hdmi_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpllclk_16bit_deepclr_div2_hdmi_clk
    }
   }
  }
  if { $usb3_supported } {
   lappend pcs_lane_usb3_g1_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g1
   lappend pcs_lane_usb3_g1_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g1*
   lappend pcs_lane_usb3_g1_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g1
   lappend pcs_lane_usb3_g1_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g1
   lappend pcs_lane_usb3_g2_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb3_g2
   lappend pcs_lane_usb3_g2_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g2*
   lappend pcs_lane_usb3_g2_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pma_clk_usb3_g2
   lappend pcs_lane_usb3_g2_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_pcs_clk_usb3_g2
   if {!$pclk_as_phy_input} {
    append_to_collection ip_all_func_pclks [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g1*]
    append_to_collection ip_all_func_pclks [get_clocks ${SNPS_CLOCK_PREFIX}lane${lane}_${pclk_out_name}_int_usb3_g2*]
   }
  }
  if { $usb4_supported } {
   lappend pcs_lane_usb4_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb4_g23
   lappend pcs_lane_usb4_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_usb4_g23
  }
  if { $usb4v2_supported } {
   lappend pcs_lane_usb4_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_mpll_usb4_g4
   lappend pcs_lane_usb4_clks_(${lane}) ${SNPS_CLOCK_PREFIX}lane${lane}_max_pclk_int_usb4_g4
  }
 }
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 2 creating clock arrays for phy $phy"
 #mplla div clk
 append_to_collection all_mplla_div_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div_clk_i \
                                                                           ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div_fr_clk]]]
 if {$usb3_supported && $dwc_dpalt_phy} {
  foreach lane $pipe_lane_list {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 3 creating mplla_div_clock array for phy $phy for upcs lane $lane "
   append_to_collection all_mplla_div_clocks_($phy) [get_clocks [concat $pcs_lane_usb3_g1_clks_($lane) ]]
  }
  append_to_collection all_mplla_div_clocks_($phy) [get_clocks [concat $lane_usb3_g1_pclks]]
 }

 #mpllb div clk
 append_to_collection all_mpllb_div_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_div_clk_i \
                                                                           ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_div_fr_clk]]]
 if {$usb3_supported && !$dwc_dpalt_phy} {
  foreach lane $pipe_lane_list {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 4 creating mpllb_div_clock array for phy $phy for upcs lane $lane "
   append_to_collection all_mpllb_div_clocks_($phy) [get_clocks [concat $pcs_lane_usb3_g1_clks_($lane) ]]
  }
  if { $pclk_as_phy_input } {
   append_to_collection all_mpllb_div_clocks_($phy) [get_clocks [concat $lane_usb3_g1_pclks]]
  }
 }

 #mplla word clk
 append_to_collection all_mplla_word_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_word_clk*i \
                                                                            ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_word_fr_clk* \
                                                                            ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_?word_clk*i]]]
 if {$usb3_supported && $dwc_dpalt_phy} {
  append_to_collection all_mplla_word_clocks_($phy) [get_clocks [concat $lane_usb3_g2_pclks]]
 }

 foreach lane $pipe_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 5 creating mplla_word_clock array for phy $phy for upcs lane $lane "
  if {$usb3_supported && $dwc_dpalt_phy} {
   append_to_collection all_mplla_word_clocks_($phy) [get_clocks [concat $pcs_lane_usb3_g2_clks_($lane)]]
  }
  if {$usb4_supported} {
   append_to_collection all_mplla_word_clocks_($phy) [get_clocks [concat $pcs_lane_usb4_clks_($lane) ]]
  }
  if {$dp20_supported} {
   append_to_collection all_mplla_word_clocks_($phy) [get_clocks [concat $pcs_lane_dp20_a_clks_($lane)]]
  }
 }

 #mpllb word clk
 append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk*i \
                                                                            ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_word_fr_clk* \
                                                                            ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_?word_clk*i]]]
 if {$usb3_supported && !$dwc_dpalt_phy} {
  if { $pclk_as_phy_input } {
   append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat $lane_usb3_g2_pclks]]
  }
 }

 foreach lane $pipe_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 6 creating mpllb_word_clock array for phy $phy for upcs lane $lane "
  if {$usb3_supported && !$dwc_dpalt_phy} {
   append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat $pcs_lane_usb3_g2_clks_($lane)]]
  }
  if {$dp20_supported} {
   append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat $pcs_lane_dp20_b_clks_($lane)]]
  }
  if { $dp14_supported } {
   append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat $pcs_lane_dp14_clks_($lane)]]
  }
  if { $hdmi_supported } {
   append_to_collection all_mpllb_word_clocks_($phy) [get_clocks [concat $pcs_lane_hdmi_clks_($lane)]]
  }
 }

 #mplla div16p5 clk
 append_to_collection all_mplla_div16p5_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div16p5_clk_i \
                                                                               ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div33_clk_i \
                                                                               ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div66_clk_i]]]

 #mpllb hdmi div clk
 append_to_collection all_mpllb_hdmi_div_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_hdmi_div_clk_i]
 if {  $hdmi_54b_support } {
  append_to_collection all_mpllb_hdmi_div_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}lane*_mpllb_hdmi_maxpclk_frlclk]
 }

 #txX_ana_word clk
 append_to_collection all_tx_ana_word_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx?_ana_word_clk_i]

 #rxX_ana_div16p5 clk
 append_to_collection all_rx_ana_div16p5_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx?_ana_div16p5_clk_i]

 #ref clk
 append_to_collection all_ref_clocks_($phy) [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_clk_i \
                                                             ${SNPS_CLOCK_PREFIX}phy${phy}_ref_div2_clk_i \
                                                             ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_clk_i \
                                                             ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i \
                                                             ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_fr_clk]]


 append_to_collection all_fw_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy_fw_clk]
 append_to_collection all_apb0_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}apb_pclk*]
 if { $sync_apb0_fw } {
  append_to_collection all_apb0_clocks_($phy) $all_fw_clocks_($phy)
 }
#F append_to_collection all_apb1_clocks_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_apb1_pclk]
# append_to_collection all_bs_cdr_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy_bs_cdr]
# append_to_collection all_bs_udr_($phy) [get_clocks ${SNPS_CLOCK_PREFIX}phy_bs_udr]
 append_to_collection all_func_jtag_($phy) [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk_n]]


 append_to_collection ip_all_func_clocks_with_embedded_asst_clks [get_clocks $all_fw_clocks_($phy)]
 append_to_collection ip_all_func_clocks_with_embedded_asst_clks [get_clocks $all_apb0_clocks_($phy)]
# append_to_collection ip_all_func_clocks_with_embedded_asst_clks [get_clocks $all_apb1_clocks_($phy)]
 append_to_collection ip_all_func_clocks_with_embedded_asst_clks [get_clocks $all_func_jtag_($phy)]

 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  append_to_collection all_mphy_clocks_($phy) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}phy${phy}_rx*_ana_clk_pwm_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcal \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcal \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_rx*_dig_clk_pwm \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_rx*_pwm_clk_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_bit_clk_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clk_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_*_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_word_clk_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_rx*_pwm_word_clk_i \
                                                                       ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcco]]]
 }
}


if {$pcie_supported } {
 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 7 creating clock arrays for phy $phy for upcs link number $link_num "
  if { !$serdes_mode } {
   append_to_collection all_mplla_word_clocks_($clksrc($link_num)) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_*_mpll_pcie_g34_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pma_clk_g34_div1_icg_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pma_clk_g34_div2_flop_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pcs_clk_g34_div1_icg_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pcs_clk_g34_div2_flop_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_*g34_*phy$clksrc($link_num)    \
																																														core_clk_g34]]]

   append_to_collection all_mpllb_word_clocks_($clksrc($link_num)) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_*_mpll_pcie_g12_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pma_clk_g12_div2_flop_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*_pcs_clk_g12_div2_flop_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_*g12_*phy$clksrc($link_num)\
																																														core_clk_g12]]]
  } else {  ;#serdes arch works with pclk as phy input clocking
   append_to_collection all_mplla_word_clocks_($clksrc($link_num)) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_*_mpll_pcie_g34_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_g34_div1_icg_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_g34_nondiv1_flop_phy$clksrc($link_num)]]]
   append_to_collection all_mpllb_word_clocks_($clksrc($link_num)) [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_*_mpll_pcie_g12_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_g12_div1_icg_phy$clksrc($link_num) \
                                                                                            ${SNPS_CLOCK_PREFIX}link${link_num}_*pclk_g12_nondiv1_flop_phy$clksrc($link_num)]]]
  }
 }
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 8 creating all clock aggregated array for phy $phy "
 if { !$sync_apb0_fw } {
  append_to_collection all_clocks_collection $all_fw_clocks_($phy)
 }
 append_to_collection all_clocks_collection $all_apb0_clocks_($phy)
 append_to_collection all_clocks_collection $all_apb1_clocks_($phy)
 append_to_collection all_clocks_collection $all_func_jtag_($phy)
 append_to_collection all_clocks_collection $all_bs_cdr_($phy)
 append_to_collection all_clocks_collection $all_bs_udr_($phy)
 append_to_collection all_clocks_collection $all_ref_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mplla_div_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mpllb_div_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mpllb_word_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mplla_word_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mplla_div16p5_clocks_(${phy})
 append_to_collection all_clocks_collection $all_mpllb_hdmi_div_clocks_(${phy})
 append_to_collection all_clocks_collection $all_tx_ana_word_clocks_($phy)
 append_to_collection all_clocks_collection $all_rx_ana_div16p5_clocks_($phy)
 append_to_collection all_clocks_collection $all_mphy_clocks_($phy)
}


if { $pclk_as_phy_input } {
 if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
  if { $serdes_supported } {
   append_to_collection all_clocks_collection [get_clocks *lane?_pclk_serdes]
   append_to_collection ip_all_func_pclks [get_clocks *lane?_pclk_serdes]
  }
  append_to_collection all_clocks_collection [get_clocks *lane*_pclk_refclk]
  append_to_collection ip_all_func_pclks [get_clocks *lane?_pclk_refclk]
  if { $hdmi_supported  && $hdmi_54b_support } {
   append_to_collection all_clocks_collection [get_clocks *lane?_pclk_hdmififo]
   append_to_collection ip_all_func_pclks [get_clocks *lane?_pclk_hdmififo]
  }
  if { $pcie_supported } {
   if { $serdes_mode } {
    append_to_collection all_clocks_collection [get_clocks *lane*_pclk_pcie_g12_phy*]
    append_to_collection all_clocks_collection [get_clocks *lane*_pclk_pcie_g34_phy*]
   }
   append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_pcie_g12_phy*]
   append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_pcie_g34_phy*]
  }
 }
} else {
 if { $pcie_supported } {
  append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_g12_div1_icg_phy*]
  append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_g12_nondiv1_flop_phy*]
  append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_g34_div1_icg_phy*]
  append_to_collection ip_all_func_pclks [get_clocks *lane*_pclk_g34_nondiv1_flop_phy*]
	#F
  append_to_collection ip_all_func_pclks [get_clocks *core_clk_g12*]
  append_to_collection ip_all_func_pclks [get_clocks *core_clk_g34*]
 }
}

#F
set ip_all_core_clks [get_clocks  *core_clk_g12*]
append_to_collection ip_all_core_clks [get_clocks *core_clk_g34*]


if { $pclk_as_phy_input } {
 append_to_collection ip_all_func_clocks_with_embedded_asst_clks [get_clocks $ip_all_func_pclks]
}

#    TX MPLL RD CLK SIDE                               RX WR CLK SIDE (all_rx_wr_clk)
#            A                                               B (wr_clk_rest)
#    MPLL*WORD*CLK                                     ALL OTHER RX CLKS
#    MPLL*GLCM*CLK
#    MPLL*WORD*FR*CLK
#    MAXPCLK
#
#           C                                               D (wr_clk)
#    PMA CLK                                           RX_ASIC_DWCLK*
#    PCS CLK
#    IN PCLK
# Collection of pcs/${pma_inst_name}/pclk of usb3-g2, pcie-g3,g4
if { $pcie_supported && !$serdes_mode} {
 #C
 append_to_collection upcs_mpll_estore_rd_clk      [get_clocks [list *lane*pcs_clk_g34* *lane*pma_clk_g34* *lane*pclk*g34* core_clk_g34]]
 #D
 append_to_collection upcs_rx_estore_wr_clk        [get_clocks *phy*rx*asic_dwclk*]
}


#B + D
set num_rx 0
for {set phy 0} {$phy < $nphys} {incr phy} {
 foreach lane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 9 creating rx clock array for phy $phy and upcs rx $lane "
  set rx_clks($num_rx) [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i \
                                        ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i* \
                                        ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_word_clk* \
                                        ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_?word_clk* \
                                        ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_wclk* \
                                        ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_?wclk*]]
  #echo "num_rx = $num_rx, phy =$phy, rx =$lane"
  append_to_collection all_estore_related_rx_wr_clks $rx_clks($num_rx)
  set num_rx [expr {$num_rx + 1}]
 }

 puts "\[Constraints Debug\] Info: [file tail [info script]] 10 creating estore clock arrays for phy $phy"
 # A + C
 if { $usb3_supported  && !$dwc_dpalt_phy} {
  append_to_collection all_estore_related_mpll_rd_clks $all_mpllb_word_clocks_($phy)
 } else { ;#pcie, usb3 dpalt
  append_to_collection all_estore_related_mpll_rd_clks $all_mplla_word_clocks_($phy)
 }

 #A
 append_to_collection tx_mpll_estore_rd_clks_rest [remove_from_collection $all_estore_related_mpll_rd_clks $upcs_mpll_estore_rd_clk]

 # List all rx clocks except rx?_asic_dwclk rxclk as it is propogating to estore
 #B
 append_to_collection rx_estore_wr_clks_rest [remove_from_collection $all_estore_related_rx_wr_clks $upcs_rx_estore_wr_clk]

}
#A + B + C + D
append_to_collection all_tx_rx_estore_clks $all_estore_related_rx_wr_clks
append_to_collection all_tx_rx_estore_clks $all_estore_related_mpll_rd_clks


append_to_collection all_clocks_collection $all_estore_related_rx_wr_clks

if { !$remove_upcs_scan_constraints } {
 if { $pcie_supported} {
  append_to_collection ip_all_shift_clks [get_clocks ${SNPS_CLOCK_PREFIX}*lane*_scan_shift_clk]
 } else {
  append_to_collection ip_all_shift_clks [get_clocks ${SNPS_CLOCK_PREFIX}lane*_div*_flop_scan_shift_clk]
 }
 append_to_collection ip_all_shift_clks [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]
 # Scan shift clocks are physically exclusive with all other scan clocks
 append_to_collection scan_clocks_all [get_clocks $ip_all_shift_clks]
 append_to_collection all_clocks_collection [get_clocks $ip_all_asst_clks]
 append_to_collection scan_clocks_all [get_clocks $ip_all_asst_clks]
 append_to_collection all_clocks_collection [get_clocks $ip_all_shift_clks]
 append_to_collection ip_all_func_clocks [remove_from_collection $all_clocks_collection $scan_clocks_all]
} else {
 append_to_collection ip_all_func_clocks [get_clocks $all_clocks_collection]
}

