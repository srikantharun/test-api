############################################################################################
#
# DWC_pcie_subsystem_ns_clocks.tcl
## synthesis all clocks definitions
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

################################
# PRIMARY CLOCKS
################################


if { !$remove_upcs_scan_constraints } {
 #####SCAN CLOCKS###############
 #-- At speed scan clocks

 # Common per PHY
 ################################
 for {set phy 0} {$phy < $nphys} {incr phy} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 creating ASST clocks of phy $phy"
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_jtag_clk                       -period [freq2per $JTAG_CLK_FREQ]              [prefixing $hiervar_ phy${phy}_jtag_tck]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_jtag_clk]
  append_to_collection ip_all_asst_clks_on_func_ports [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_jtag_clk]
 # create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb0_pclk                      -period [freq2per $APB_CLK_FREQ]               [prefixing $hiervar_ phy${phy}_apb0_pclk]
  #append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb0_pclk]
  #append_to_collection ip_all_asst_clks_on_func_ports [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb0_pclk]
  #create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb1_pclk                      -period [freq2per $APB_CLK_FREQ]               [prefixing $hiervar_ phy${phy}_apb1_pclk]
  #append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb1_pclk]
 # append_to_collection ip_all_asst_clks_on_func_ports [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_apb1_pclk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_fw_clk                         -period [freq2per $FW_CLK_FREQ]                [prefixing $hiervar_ phy_fw_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_fw_clk]
  append_to_collection ip_all_asst_clks_on_func_ports [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_fw_clk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_cr_clk                         -period [freq2per $CR_CLK_FREQ]                [prefixing $hiervar_ phy${phy}_scan_cr_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_cr_clk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_dword_clk                 -period [freq2per $MPLLA_WCLK_FREQ]            [prefixing $hiervar_ phy${phy}_scan_mpll_dword_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_dword_clk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_qword_clk                 -period [freq2per [expr {$MPLLA_WCLK_FREQ/2}]] [prefixing $hiervar_ phy${phy}_scan_mpll_qword_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_qword_clk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_occ_clk                        -period [freq2per $SCAN_OCC_FREQ]              [prefixing $hiervar_ phy${phy}_scan_occ_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_occ_clk]
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_ref_clk                        -period [freq2per $SCAN_REF_CLK_FREQ]          [prefixing $hiervar_ phy${phy}_scan_ref_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_ref_clk]
  if { !$jtag_rx_ana_dword_xf } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_word_clk                  -period [freq2per $MPLLA_WCLK_FREQ]            [prefixing $hiervar_ phy${phy}_scan_mpll_word_clk]
   append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_mpll_word_clk]
  }

  #JIRA-P80001562-139515 Period kept as Mplla word clock as it has higher frequency for all modes
  if { $jtag_phy_scan_rx_dword } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_scan_rx_dword_clk                   -period [freq2per $SCAN_RX_DWCLK_FREQ]            [prefixing $hiervar_ phy${phy}_scan_rx_dword_clk]
   append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_scan_rx_dword_clk]
  }
 }

 # UPCS common scan clocks
 ################################
 create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_pcs_clk                              -period [freq2per $MPLLA_WCLK_FREQ]            [prefixing $hiervar_ pcs_scan_pcs_clk]
 append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pcs_clk]
# if { !$tx_only_supported } {
  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_pma_clk                              -period [freq2per $SCAN_PMA_CLK_FREQ]          [prefixing $hiervar_ pcs_scan_pma_clk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pma_clk]
# } else {
#  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_rd_clk                          -period [freq2per $SCAN_PMA_CLK_FREQ]          [prefixing $hiervar_ pcs_scan_fifo_rd_clk]
#  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_rd_clk]
# }
# if { $hdmi_supported && $hdmi_54b_support } {
#  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_wr_clk                          -period [freq2per $PCLK_HDMIFIFO_FREQ]         [prefixing $hiervar_ pcs_scan_fifo_wr_clk]
#  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_fifo_wr_clk]
# }
# if { $pclk_as_phy_input } {
#  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_max_pclk                             -period [freq2per $SCAN_MAX_PCLK_FREQ]         [prefixing $hiervar_ pcs_scan_max_pclk]
#  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_max_pclk]
#  if {  ($usb3_supported || $pcie_supported) && $pcs_scan_nonsds_pclk } {
#   create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_in_pclk_nonsds_clk                   -period [freq2per $SCAN_PCLK_NONSDS_FREQ]      [prefixing $hiervar_ pcs_scan_in_pclk_nonsds_clk]
#   append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_in_pclk_nonsds_clk]
#  }
# } else {
  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_pclk                                 -period [freq2per $SCAN_PCLK_OUT_FREQ]         [prefixing $hiervar_ pcs_scan_pclk]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_pclk]
# }
#F Check
 	if { !$tx_only_supported && $pcs_scan_rx_clk} {
  # Rx scan clock used for non-serdes rx-datapath
  create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_rx_clk_div                           -period [freq2per $SCAN_PCS_RX_CLK_DIV_FREQ]   [prefixing $hiervar_ pcs_scan_rx_clk_div]
  append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_rx_clk_div]
 }

 ##-- UPCS per lane -TX clocks
 ################################
# if { $pclk_as_phy_input } {
#  if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
#   for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
#    foreach lane $pcs_lanes($link_num) {
#     puts "\[Constraints Debug\] Info: [file tail [info script]] 2 creating ASST clocks of upcs lane $lane of link $link_num"
#     # per upcs lane scan clock for all protocols
#     create_clock -add -name ${SNPS_CLOCK_PREFIX}pcs_scan_lane${lane}_in_pclk                  -period [freq2per $SCAN_PCLK_IN_FREQ]          [prefixing $hiervar_ pipe_lane${lane}_in_pclk]
#     append_to_collection ip_all_asst_clks [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_lane${lane}_in_pclk]
#     append_to_collection ip_all_asst_clks_on_func_ports [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_lane${lane}_in_pclk]
#    }
#   }
#  }
# }

 create_clock -add -name ${SNPS_CLOCK_PREFIX}scan_shift_clk                                -period [freq2per $SCAN_SHIFT_FREQ]                                 $scan_shift_clk_list
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
     create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_scan_shift_clk                                   \
         -source       [prefixing $hiervar_ pcs_scan_clk]                                                                     \
         -master       [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]                                                      \
         -divide_by    2                           $lane_pma_clk_src_flop_pin_($lane)
     # Generate scan shift clock is created at flop output to meet shift timing arc for that flop,
     create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_scan_shift_clk                                   \
         -source       [prefixing $hiervar_ pcs_scan_clk]                                                                     \
         -master       [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]                                                      \
         -divide_by    2                           $lane_pcs_clk_src_flop_pin_($lane)
    }
#    if { $pclk_as_phy_input } {
#     #-- MAXPCLK
#     # Scan shift clock is created at flop output to meet shift timing arc for that flop,
#     create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_scan_shift_clk                               \
#         -source       [prefixing $hiervar_ pcs_scan_clk]                                                                     \
#         -master       [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]                                                      \
#         -divide_by    2                           $lane_max_pclk_int_flop_pin_($lane)
#    } else {
     #-- OUTPUT PCLK
     create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_scan_shift_clk                                  \
         -source       [prefixing $hiervar_ pcs_scan_clk]                                                                     \
         -master       [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk]                                                      \
         -divide_by    2                           $lane_pclk_src_flop_pin_($lane)
#    }
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
 
 create_clock [get_ports tck] -name ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk  -period [freq2per $JTAG_CLK_FREQ]
 create_clock [get_ports bisr_clk] -name bisr_clk -period $ref_clk_period -waveform [list 0 [expr {$ref_clk_period/2}]]
# create_clock -add -name ${SNPS_CLOCK_PREFIX}phy_bs_cdr                              -period [freq2per $BS_CLK_FREQ]                [prefixing $hiervar_ phy_bs_cdr]
# create_clock -add -name ${SNPS_CLOCK_PREFIX}phy_bs_udr                              -period [freq2per $BS_CLK_FREQ]                [prefixing $hiervar_ phy_bs_udr]
# create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_apb0_pclk                           -period [freq2per $APB_CLK_FREQ]               [prefixing $hiervar_ phy${phy}_apb0_pclk]
# create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_apb1_pclk                           -period [freq2per $APB_CLK_FREQ]               [prefixing $hiervar_ phy${phy}_apb1_pclk]
# create_clock -add -name ${SNPS_CLOCK_PREFIX}phy_fw_clk                              -period [freq2per $FW_CLK_FREQ]                [prefixing $hiervar_ phy_fw_clk]

 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_word_clk_${proto_type}i   -period [freq2per $MPLLA_WCLK_FREQ]            [prefixing $hiervar  phy${phy}/${pma_inst_name}/mplla_ana_word_clk_i]
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div_clk_i                 -period [freq2per $MPLLA_DIV_FREQ]             [prefixing $hiervar  phy${phy}/${pma_inst_name}/mplla_ana_div_clk_i]
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div16p5_clk_i             -period [freq2per $MPLLA_DIV16P5_FREQ]         [prefixing $hiervar  phy${phy}/${pma_inst_name}/mplla_ana_div16p5_clk_i]

 if { $pcie_supported } {
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_i                -period [freq2per $MPLLB_WCLK_FREQ_PCIE]       [prefixing $hiervar  phy${phy}/${pma_inst_name}/mpllb_ana_word_clk_i]
 }
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_div_clk_i                 -period [freq2per $MPLLB_DIV_FREQ]             [prefixing $hiervar  phy${phy}/${pma_inst_name}/mpllb_ana_div_clk_i]
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_clk_i                       -period [freq2per $REF_ANA_FREQ]               [prefixing $hiervar  phy${phy}/${pma_inst_name}/ref_ana_clk_i]
 # Create an OCC clock on the same pin - this will NOT be divided by 2
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i                   -period [freq2per $REF_ANA_OCC_FREQ]           [prefixing $hiervar  phy${phy}/${pma_inst_name}/ref_ana_clk_i]
 create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_hdmi_div_clk_i                -period [freq2per $HDMI_DIV_FREQ]              [prefixing $hiervar  phy${phy}/${pma_inst_name}/mpllb_hdmi_div_clk_i]
#F- Attention
 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy*/${pma_inst_name}/dco_ana_clkcal]]] > 0 } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcal                      -period [freq2per $DCO_CLK_CAL_FREQ]           [prefixing $hiervar  phy${phy}/${pma_inst_name}/dco_ana_clkcal]
  }
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy*/${pma_inst_name}/dco_ana_clkcco]]] > 0 } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcco                      -period [freq2per $DCO_CLK_CCO_FREQ]           [prefixing $hiervar  phy${phy}/${pma_inst_name}/dco_ana_clkcco]
  }
 }
 #--Per Phy tx
 ################################
 foreach lane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 5 creating functionals clocks of tx $txlane of phy $phy"
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/${pma_inst_name}/tx${lane}_ana_word_clk_i]]] > 0 } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx${lane}_ana_word_clk_i            -period [freq2per $TX_WCLK_FREQ]               [prefixing $hiervar  phy${phy}/${pma_inst_name}/tx${lane}_ana_word_clk_i]
  }
 }

 #--Per Phy rx
 ################################
 foreach lane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 6 creating functionals clocks of rx $rxlane of phy $phy"
  if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/pma/rx${lane}_ana_word_clk_i_8bit]]] > 0 } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i_8bit       -period [freq2per $RX_WCLK_FREQ]               [prefixing $hiervar  phy${phy}/pma/rx${lane}_ana_word_clk_i_8bit]
  } else {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i            -period [freq2per $RX_WCLK_FREQ]               [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_word_clk_i]
  }
  create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_div16p5_clk_i         -period [freq2per $RX_DIV16P5_FREQ]            [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_div16p5_clk_i]

  # Multiple variants are defined for dword clock to meet timing requirement for serdes and non-serdes Rx path
#  if { $usb4_supported } {
#   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i_sds       -period [freq2per $RX_DWCLK_FREQ]              [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]
#  }
#  if { $usb3_supported } {
#   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i_nonsds    -period [freq2per $RX_DWCLK_NONSDS_FREQ]       [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]
#  }

  # Single clock is enough to meet timing requirement for Display PHYs
  if { $tx_only_supported} {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i           -period [freq2per $RX_DWCLK_NONSDS_FREQ]       [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]
  }
  if { $pcie_supported } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i           -period [freq2per $RX_DWCLK_FREQ]              [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]
  }
  if { $jtag_mphy_support && !$dwc_dpalt_phy } {
   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_clk_pwm_i             -period [freq2per $RX_ANA_PWM_FREQ]            [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_clk_pwm_i]
  }
#  if { $usb4v2_supported } {
#   create_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_div28_clk_i           -period [freq2per $RX_TRIT_DIV28_FREQ]         [prefixing $hiervar  phy${phy}/${pma_inst_name}/rx${lane}_ana_div28_clk_i]
#  }
 }
}

##-- UPCS per lane
################################


################################
# GENERATED CLOCKS
################################
#####FUNCTIONAL CLOCKS##########

##-- Functional Generated clocks

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 8 creating generated clocks of functional clocks for phy $phy"
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_fr_clk \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_clk_i] \
     -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i] \
     -divide_by    1   -combinational  [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_dig_fr_clk]

 # timing arc and clock generating ref_ana_clk_i -> ref_div2_clk_i already exists in PMA lib.
 # Override it to enforce only timing arcs ref_ana_clk_i -> ref_div2_clk_i.
 # PT_SHELL: -master_clock must use with -add
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_div2_clk_i \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_clk_i] \
     -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_clk_i] \
     -divide_by    2     [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_div2_clk_i]
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_clk_i \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_div2_clk_i] \
     -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_div2_clk_i] \
     -divide_by    1 -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_dig_clk_i]


 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/dco_ana_clkcco] \
      -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcco] \
      -divide_by    1   -combinational  [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcco]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcal \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/dco_ana_clkcal] \
      -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_dco_ana_clkcal] \
      -divide_by    1   -combinational  [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcal]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clk_i       \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcco]  \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco ]      \
      -divide_by    1  -combinational   [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_clk_i]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_1_i       \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcco]  \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco ]      \
      -divide_by    2     [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_clks_1_i]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_2_i       \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcco]  \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco ]      \
      -divide_by    4     [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_clks_2_i]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clks_3_i       \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_ana_dco_clkcco]  \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_dco_clkcco ]      \
      -divide_by    8     [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_clks_3_i]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_bit_clk_i    \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_clk_i]          \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_clk_i ] \
      -edges        $TX_PWM_BIT_CLK_EDGE [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_bit_clk_i]

  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_word_clk_i    \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_bit_clk_i]          \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx_pwm_bit_clk_i ] \
      -edges        $TX_PWM_WCLK_EDGE [prefixing $hiervar phy${phy}/${pma_inst_name}/tx_pwm_word_clk_i]
 }
 # Re-generated removed clocks here w.r.t to each clock created on mpllb_ana_word_clk_i
 set mpllbgenclk        [list dword qword oword word_fr]
 set mpllbgendiv        [list 2     4     8      1     ]
 set mpllb_word_fr_clk_name [get_bitblasted_signal mpllb_word_fr_clk $jtag_pma_bit_blasted]
 set mpllbgenclkpin     [list mpllb_dword_clk_i mpllb_qword_clk_i mpllb_oword_clk_i ${mpllb_word_fr_clk_name}]
 foreach genclk $mpllbgenclk genclkpin $mpllbgenclkpin gendiv $mpllbgendiv {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 9 creating generated clock variants of functional clocks for mpllb $genclk on pin $genclkpin with div factor $gendiv for phy $phy"

  if { $pcie_supported || ($usb3_supported && !$dwc_dpalt_phy)} {
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_${genclkpin}       \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mpllb_ana_word_clk_i]             \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_word_clk_i ]                                \
       -divide_by    ${gendiv}                   [prefixing $hiervar phy${phy}/${pma_inst_name}/${genclkpin}]
  }
 }

# if { $usb4v2_supported } {
#  set data_rate      [list _nrz _pam3]
# } else {
  set data_rate      [list _]
# }
 set mpllagenclk    [list dword qword oword word_fr]
 set mpllagendiv    [list 2     4     8      1     ]
 set mpllaclksufix  [list clk_i clk_i clk_i clk]

 foreach drate $data_rate {
  foreach genclk $mpllagenclk gendiv $mpllagendiv gensufix $mpllaclksufix {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 10 creating generated clock variants of functional clocks for mplla $genclk with suffix $gensufix with div factor $gendiv and signaling $drate for phy $phy"
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_${genclk}_clk${drate}i    \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_ana_word_clk_i]             \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_word_clk${drate}i ]                             \
       -divide_by    ${gendiv}                   [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_${genclk}_${gensufix}]
  }
 }
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div33_clk_i    \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_ana_div16p5_clk_i]             \
     -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div16p5_clk_i ]                             \
     -divide_by    2                   [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_div33_clk_i]
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div66_clk_i    \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_ana_div16p5_clk_i]             \
     -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div16p5_clk_i ]                             \
     -divide_by    4                   [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_div66_clk_i]
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_div_fr_clk    \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_ana_div_clk_i]             \
     -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mplla_ana_div_clk_i ]                             \
     -divide_by    1 -combinational    [prefixing $hiervar phy${phy}/${pma_inst_name}/mplla_div_fr_clk]
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_div_fr_clk    \
     -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/mpllb_ana_div_clk_i]             \
     -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_mpllb_ana_div_clk_i ]                             \
     -divide_by    1 -combinational    [prefixing $hiervar phy${phy}/${pma_inst_name}/mpllb_div_fr_clk]


 # Per lane per PHY
 # Remove lib generated clocks based off rxX_ana_dword_clk
 # Re-generated those clocks here w.r.t to each clock created on rx_ana_dword_clk
# if { $usb4_supported } {
#  set rxgenclktype    [list _sds  _nonsds]
# } elseif { $usb3_supported } {
#  set rxgenclktype    [list _nonsds]
# } elseif { $pcie_supported || $tx_only_supported } {
  set rxgenclktype    [list ""]
# }
 foreach lane $phy_rx_lane_list {
  foreach clktype $rxgenclktype {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 11 creating generated clock variants of functional clocks for rx $lane of type $clktype for phy $phy"
   if { $PMA_NAME == "c40" || $jtag_pma_new_timing_arcs } {
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]        \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i$clktype] \
        -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_dword_clk] -invert
   } else {
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_ana_dword_clk_i]        \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_dword_clk_i$clktype] \
        -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_dword_clk]
   }
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_qword_clk$clktype \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_dword_clk]          \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype ] \
       -divide_by    2                           [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_qword_clk]
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_dwclk$clktype    \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_dword_clk]          \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype ] \
       -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_dwclk]
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_qwclk$clktype    \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_qword_clk]          \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_qword_clk$clktype ] \
       -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_qwclk]
   if { [sizeof_collection [get_pins -quiet [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_owclk]]] > 0 } {
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_oword_clk$clktype \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_dword_clk]          \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_dword_clk$clktype ] \
        -divide_by    4                           [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_oword_clk]
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_owclk$clktype    \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_oword_clk]          \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_oword_clk$clktype ] \
        -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_owclk]
   }
  }
  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_word_clk    \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_ana_word_clk_i]          \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_word_clk_i ] \
      -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_word_clk]
  create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_asic_wclk    \
      -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_word_clk]          \
      -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_word_clk ] \
      -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_asic_wclk]
  if { $jtag_mphy_support && !$dwc_dpalt_phy } {
   if { $jtag_pma_new_timing_arcs } {
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_clk_pwm    \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_ana_clk_pwm_i]          \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_clk_pwm_i ] \
        -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_clk_pwm] -invert
   } else {
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_clk_pwm    \
        -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_ana_clk_pwm_i]          \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_ana_clk_pwm_i ] \
        -divide_by    1    -combinational     [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_clk_pwm]
   }
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_pwm_clk_i    \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_dig_clk_pwm]          \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_dig_clk_pwm ] \
       -edges        $RX_PWM_CLK_EDGE \
       -edge_shift   $RX_PWM_CLK_EDGE_SHIFT [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_pwm_clk_i]
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_pwm_word_clk_i    \
       -source       [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_pwm_clk_i]          \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${lane}_pwm_clk_i ] \
       -edges        $RX_PWM_WCLK_EDGE [prefixing $hiervar phy${phy}/${pma_inst_name}/rx${lane}_pwm_word_clk_i]

  }
 }
 create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk_n                                                             \
     -source       [prefixing $hiervar_ phy${phy}_jtag_tck]                                         \
     -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_jtag_clk]                                                  \
     -divide_by    1     -combinational   $jtag_clk_p_n_src_pin_($phy) -invert
}



if { $pcie_supported } {
 # PCIe - Internal generated clocks per UPCS lane
 # Clocks - Mpll, Maxpclk, pma_clk(txX_clk), pcs_clk
 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  foreach lane $pcs_lanes($link_num) {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 13 creating generated clocks for pcie of upcs lane $lane in link $link_num"
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)                  \
       -source       [prefixing $hiervar phy$clksrc($link_num)/${pma_inst_name}/mpllb_ana_word_clk_i] \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy$clksrc($link_num)_mpllb_ana_word_clk_i]                          \
       -divide_by    1     -combinational         $lane_mpll_word_clk_src_pin_($lane)
   create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)                  \
       -source       [prefixing $hiervar phy$clksrc($link_num)/${pma_inst_name}/mplla_ana_word_clk_i] \
       -master       [get_clocks ${SNPS_CLOCK_PREFIX}phy$clksrc($link_num)_mplla_ana_word_clk_${proto_type}i]             \
       -divide_by    1     -combinational        $lane_mpll_word_clk_src_pin_($lane)
   # Clocks defined for PCIe Non-Serdes arch for both Pclk as Phy Input/Output modes
   if { !$serdes_mode } {
    #-- PMA CLK
    # Generated PMA clock of div1 defined at mux output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div1_icg_phy$clksrc($link_num)               \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    1     -combinational        $lane_pma_clk_src_icg_pin_($lane)
    # Divided version of Pma clock (div2) defined at flop output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    2              $lane_pma_clk_src_flop_pin_($lane)
    # Divided version of Pma clock (div2) defined at flop output inside divider for rate g{1,2}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g12_div2_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
        -divide_by    2                           $lane_pma_clk_src_flop_pin_($lane)
    #-- PCS CLK
    # Generated PCS clock of div1 defined at mux output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div1_icg_phy$clksrc($link_num)               \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    1     -combinational         $lane_pcs_clk_src_icg_pin_($lane)
    # Divided version of Pcs clock (div2) defined at flop output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    2                           $lane_pcs_clk_src_flop_pin_($lane)
    # Divided version of Pcs clock (div2) defined at flop output inside divider for rate g{1,2}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g12_div2_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
        -divide_by    2                           $lane_pcs_clk_src_flop_pin_($lane)
   }
#   if { $pclk_as_phy_input } {
#    #-- MAXPCLK
#    # Generated MaxPclk clock of div1 (based of MPLL clock as master clock) defined at mux output inside divider for rate g{3,4}
#    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_div1_icg_phy$clksrc($link_num)               \
#        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
#        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
#        -divide_by    1    -combinational         $lane_max_pclk_int_icg_pin_($lane)
#    lappend pcs_lane_pcie_g34_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_div1_icg_phy$clksrc($link_num)
#
#    # Divided version of MaxPclk defined at flop output inside divider for rate g{3,4}
#    # Divide factor is calculated based on input arguments min supported pipe_width, max_pclk_div_ratio
#    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_nondiv1_flop_phy$clksrc($link_num)       \
#        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
#        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
#        -divide_by    $pcie4_max_pclk_non_div_g34 $lane_max_pclk_int_flop_pin_($lane)
#    lappend pcs_lane_pcie_g34_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g34_nondiv1_flop_phy$clksrc($link_num)
#
#    # Generated MaxPclk clock of div1 (based of MPLL clock as master clock) defined at mux output inside divider for rate g{1,2}
#    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_div1_icg_phy$clksrc($link_num)               \
#        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
#        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
#        -divide_by    1    -combinational          $lane_max_pclk_int_icg_pin_($lane)
#    lappend pcs_lane_pcie_g12_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_div1_icg_phy$clksrc($link_num)
#
#    # Divided version of MaxPclk defined at flop output inside divider for rate g{1,2}
#    # Divide factor is calculated based on input arguments min supported pipe_width, max_pclk_div_ratio
#    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_nondiv1_flop_phy$clksrc($link_num)       \
#        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
#        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
#        -divide_by    $pcie4_max_pclk_non_div_g12 $lane_max_pclk_int_flop_pin_($lane)
#    lappend pcs_lane_pcie_g12_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_max_pclk_g12_nondiv1_flop_phy$clksrc($link_num)
#
#   } else {
    #-- OUTPUT PCLK
    # Generated Output clock of div1 (based of MPLL clock as master clock) defined at mux output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_div1_icg_phy$clksrc($link_num)                  \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    1    -combinational       $lane_pclk_src_icg_pin_($lane)
    lappend pcs_lane_pcie_g34_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_div1_icg_phy$clksrc($link_num)

    # Divided version of Output Pclk defined at flop output inside divider for rate g{1,2}
    # Divide factor is calculated based on input arguments min supported pipe_width
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_nondiv1_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)]     \
        -divide_by    $pcie4_pclk_non_div_g34     $lane_pclk_src_flop_pin_($lane)
    lappend pcs_lane_pcie_g34_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g34_nondiv1_flop_phy$clksrc($link_num)

    # Generated Output clock of div1 (based of MPLL clock as master clock) defined at mux output inside divider for rate g{3,4}
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_div1_icg_phy$clksrc($link_num)                  \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
        -divide_by    1    -combinational       $lane_pclk_src_icg_pin_($lane)
    lappend pcs_lane_pcie_g12_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_div1_icg_phy$clksrc($link_num)

    # Divided version of Output Pclk defined at flop output inside divider for rate g{3,4}
    # Divide factor is calculated based on input arguments min supported pipe_width
    create_generated_clock -add -name ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_nondiv1_flop_phy$clksrc($link_num)          \
        -source       $lane_mpll_word_clk_src_pin_($lane)                                              \
        -master       [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)]     \
        -divide_by    $pcie4_pclk_non_div_g12     $lane_pclk_src_flop_pin_($lane)
    lappend pcs_lane_pcie_g12_pclks_(${lane}) ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_g12_nondiv1_flop_phy$clksrc($link_num)

#   }
  }
 }
}

### Partition clocks ###
###################################################################################################
# partition clocks 
###################################################################################################
# AO clocks
#ref_clk
create_clock [get_ports i_ref_clk] -name i_ref_clk -period $ref_clk_period -waveform [list 0 [expr {$ref_clk_period/2}]]
create_clock -name ref_clk_virt -period $ref_clk_period -waveform [list 0 [expr {$ref_clk_period/2}]]
set_clock_uncertainty -setup $ref_clk_unc_s [get_clocks [list i_ref_clk ref_clk_virt]]
set_clock_uncertainty -hold  $ref_clk_unc_h [get_clocks [list i_ref_clk ref_clk_virt]]
set_clock_latency -max $ref_clk_lt_s  [get_clocks [list i_ref_clk ref_clk_virt]]
set_clock_latency -min $ref_clk_lt_h  [get_clocks [list i_ref_clk ref_clk_virt]]
set_clock_latency -source 0 [get_clocks [list i_ref_clk ref_clk_virt]]

# AXI clocks
#ctrl_top_0
create_clock [get_ports i_pcie_init_mt_axi_clk] -name i_pcie_init_mt_axi_clk -period $mstr_aclk_period -waveform [list 0 [expr {$mstr_aclk_period/2}]]
create_clock -name mstr_aclk_virt -period $mstr_aclk_period -waveform [list 0 [expr {$mstr_aclk_period/2}]]
set_clock_uncertainty -setup $mstr_aclk_unc_s [get_clocks [list i_pcie_init_mt_axi_clk mstr_aclk_virt]]
set_clock_uncertainty -hold  $mstr_aclk_unc_h [get_clocks [list i_pcie_init_mt_axi_clk mstr_aclk_virt]]
set_clock_latency -max $mstr_aclk_lt_s  [get_clocks [list i_pcie_init_mt_axi_clk mstr_aclk_virt]]
set_clock_latency -min $mstr_aclk_lt_h  [get_clocks [list i_pcie_init_mt_axi_clk mstr_aclk_virt]]
set_clock_latency -source 0 [get_clocks [list i_pcie_init_mt_axi_clk mstr_aclk_virt]]

create_clock [get_ports i_pcie_targ_mt_axi_clk] -name i_pcie_targ_mt_axi_clk -period $slv_aclk_period -waveform [list 0 [expr {$slv_aclk_period/2}]]
create_clock -name slv_aclk_virt -period $slv_aclk_period -waveform [list 0 [expr {$slv_aclk_period/2}]]
set_clock_uncertainty -setup $slv_aclk_unc_s [get_clocks [list i_pcie_targ_mt_axi_clk slv_aclk_virt]]
set_clock_uncertainty -hold  $slv_aclk_unc_h [get_clocks [list i_pcie_targ_mt_axi_clk slv_aclk_virt]]
set_clock_latency -max $slv_aclk_lt_s         [get_clocks [list i_pcie_targ_mt_axi_clk slv_aclk_virt]] 
set_clock_latency -min $slv_aclk_lt_h         [get_clocks [list i_pcie_targ_mt_axi_clk slv_aclk_virt]]
set_clock_latency -source 0 [get_clocks [list i_pcie_targ_mt_axi_clk slv_aclk_virt]]

create_clock [get_ports i_pcie_targ_cfg_dbi_axi_clk] -name i_pcie_targ_cfg_dbi_axi_clk -period $dbi_aclk_period -waveform [list 0 [expr {$dbi_aclk_period/2}]]
create_clock -name dbi_aclk_virt -period $dbi_aclk_period -waveform [list 0 [expr {$dbi_aclk_period/2}]]
set_clock_uncertainty -setup $dbi_aclk_unc_s [get_clocks [list i_pcie_targ_cfg_dbi_axi_clk dbi_aclk_virt]]
set_clock_uncertainty -hold  $dbi_aclk_unc_h [get_clocks [list i_pcie_targ_cfg_dbi_axi_clk dbi_aclk_virt]]
set_clock_latency -max $dbi_aclk_lt_s  [get_clocks [list i_pcie_targ_cfg_dbi_axi_clk dbi_aclk_virt]] 
set_clock_latency -min $dbi_aclk_lt_h [get_clocks [list i_pcie_targ_cfg_dbi_axi_clk dbi_aclk_virt]]
set_clock_latency -source 0 [get_clocks [list i_pcie_targ_cfg_dbi_axi_clk dbi_aclk_virt]]

# APB clocks
#apb_pclk
create_clock [get_ports i_apb_pclk] -name i_apb_pclk -period $apb_pclk_period -waveform [list 0 [expr {$apb_pclk_period/2}]]
create_clock -name apb_pclk_virt -period $apb_pclk_period -waveform [list 0 [expr {$apb_pclk_period/2}]]
set_clock_uncertainty -setup $apb_pclk_unc_s [get_clocks [list i_apb_pclk apb_pclk_virt]]
set_clock_uncertainty -hold  $apb_pclk_unc_h [get_clocks [list i_apb_pclk apb_pclk_virt]]
set_clock_latency -max $apb_pclk_lt_s   [get_clocks [list i_apb_pclk apb_pclk_virt]]
set_clock_latency -min $apb_pclk_lt_h   [get_clocks [list i_apb_pclk apb_pclk_virt]]
set_clock_latency -source 0 [get_clocks [list i_apb_pclk apb_pclk_virt]]

# AUX clocks    
#aux_clk
create_clock [get_ports i_pcie_aux_clk] -name i_pcie_aux_clk -period $aux_clk_period -waveform [list 0 [expr ${aux_clk_period}/2]]
create_clock -name aux_clk_virt -period $aux_clk_period -waveform [list 0 [expr {$aux_clk_period/2}]]
set_clock_uncertainty -setup $aux_clk_unc_s [get_clocks [list i_pcie_aux_clk aux_clk_virt]]
set_clock_uncertainty -hold  $aux_clk_unc_h [get_clocks [list i_pcie_aux_clk aux_clk_virt]]
set_clock_latency 0         [get_clocks [list i_pcie_aux_clk aux_clk_virt]] 
set_clock_latency -source 0 [get_clocks [list i_pcie_aux_clk aux_clk_virt]]

# common async_clk
#async_clk_virt
create_clock -name async_clk_virt -period $async_clk_virt_period -waveform [list 0 [expr {$async_clk_virt_period/2}]] 
set_clock_uncertainty -setup $async_clk_virt_unc_s [get_clocks async_clk_virt]
set_clock_uncertainty -hold  $async_clk_virt_unc_h [get_clocks async_clk_virt]
set_clock_latency  -max $async_clk_lt_s   [get_clocks async_clk_virt] 
set_clock_latency  -min $async_clk_lt_h    [get_clocks async_clk_virt] 
set_clock_latency -source 0 [get_clocks async_clk_virt]

### PCTL ###
###################################################################################################
# PCTL clocks 
###################################################################################################
 set pcie_aux_clk_pin [get_pins u_pctl/g_clkdiv_3__u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
 create_generated_clock -add \
   -name         pcie_aux_clk \
   -source       [get_ports i_pcie_aux_clk] \
   -master_clock i_pcie_aux_clk \
   -divide_by    1 \
   $pcie_aux_clk_pin

 set pcie_init_mt_axi_aclk_pin [get_pins u_pctl/g_clkdiv_2__u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
 create_generated_clock -add \
   -name         pcie_init_mt_axi_aclk \
   -source       [get_ports i_pcie_init_mt_axi_clk] \
   -master_clock i_pcie_init_mt_axi_clk \
   -divide_by    1 \
   $pcie_init_mt_axi_aclk_pin

 set pcie_targ_mt_axi_aclk_pin [get_pins u_pctl/g_clkdiv_1__u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
 create_generated_clock -add \
   -name         pcie_targ_mt_axi_aclk \
   -source       [get_ports i_pcie_targ_mt_axi_clk] \
   -master_clock i_pcie_targ_mt_axi_clk \
   -divide_by    1 \
   $pcie_targ_mt_axi_aclk_pin

 set pcie_targ_cfg_dbi_axi_aclk_pin [get_pins u_pctl/g_clkdiv_0__u_clkdiv/u_clk_gate/u_tc_lib_clk_en/ECK ]
 create_generated_clock -add \
   -name         pcie_targ_cfg_dbi_axi_aclk \
   -source       [get_ports i_pcie_targ_cfg_dbi_axi_clk] \
   -master_clock i_pcie_targ_cfg_dbi_axi_clk \
   -divide_by    1 \
   $pcie_targ_cfg_dbi_axi_aclk_pin

### Subsystem level ###
###################################################################################################
# subsystem clockc
###################################################################################################
# AXI clocks
#ctrl_top_0
set mstr_aclk_pin [get_pins u_mstr_aclk_buf/u_tc_lib_clk_inv1/Y ]
create_generated_clock -add \
  -name         mstr_aclk \
  -source       $pcie_init_mt_axi_aclk_pin \
  -master_clock pcie_init_mt_axi_aclk \
  -divide_by    1 \
  $mstr_aclk_pin
set slv_aclk_pin [get_pins u_slv_aclk_buf/u_tc_lib_clk_inv1/Y ]
create_generated_clock -add \
  -name         slv_aclk \
  -source       $pcie_targ_mt_axi_aclk_pin \
  -master_clock pcie_targ_mt_axi_aclk \
  -divide_by    1 \
  $slv_aclk_pin
set dbi_aclk_pin [get_pins u_dbi_aclk_buf/u_tc_lib_clk_inv1/Y ]
create_generated_clock -add \
  -name         dbi_aclk \
  -source       $pcie_targ_cfg_dbi_axi_aclk_pin \
  -master_clock pcie_targ_cfg_dbi_axi_aclk \
  -divide_by    1 \
  $dbi_aclk_pin

# APB clocks
#apb_pclk
set apb_pclk_pin [get_pins u_apb_pclk_buf/u_tc_lib_clk_inv1/Y ]
create_generated_clock -add \
  -name         apb_pclk \
  -source       [get_ports i_apb_pclk] \
  -master_clock i_apb_pclk \
  -divide_by    1 \
  $apb_pclk_pin

# AUX clocks
#aux_clk
set aux_clk_pin [get_pins u_aux_clk_buf/u_tc_lib_clk_inv1/Y ]
create_generated_clock -add \
  -name         aux_clk \
  -source       $pcie_aux_clk_pin \
  -master_clock pcie_aux_clk \
  -divide_by    1 \
  $aux_clk_pin

# phy_fw_clk
set phy_fw_clk_pin [get_pins u_pcie_fast_axi_clk_d2/u_clk_mux2/u_tc_lib_clk_mux/Y ]
create_generated_clock -add \
  -name         phy_fw_clk \
  -source       $pcie_init_mt_axi_aclk_pin \
  -master_clock pcie_init_mt_axi_aclk \
  -divide_by    2 \
  $phy_fw_clk_pin

############################################################################################
# core clocks
############################################################################################
## _core_clk(500M)
set core_clk_src_pin [get_driver_cell_pin [get_pins ${pcie_clk_rst_inst}u_clk_gate_core_clk/clk_o]]
#link0_lane0_pclk_g12_nondiv1_mux_phy0
if { $protocol == "pcie4" } {
for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 #   foreach lane $pcs_lanes($link_num) {
      create_generated_clock -add \
        -name         core_clk_g12 \
        -source       $lane_pclk_src_muxout_pin_(0) \
        -master_clock [get_clocks link${link_num}_lane0_pclk_g12_nondiv1_flop_phy$clksrc($link_num)] \
        -divide_by    1 \
        $core_clk_src_pin
      
      create_generated_clock -add \
        -name         core_clk_g34 \
        -source       $lane_pclk_src_muxout_pin_(0) \
        -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane0_pclk_g34_nondiv1_flop_phy$clksrc($link_num)] \
        -divide_by    1 \
        $core_clk_src_pin
 #   }
  } 
} 
create_clock -name core_clk_virt -period 2.0
set_clock_uncertainty -setup $core_clk_unc_s [get_clocks core_clk_virt]
set_clock_uncertainty -hold  $core_clk_unc_h [get_clocks core_clk_virt]
set_clock_latency -max $core_clk_lt_s [get_clocks core_clk_virt] 
set_clock_latency -min $core_clk_lt_h [get_clocks core_clk_virt] 
set_clock_latency -source 0 [get_clocks core_clk_virt]

#mac_scan_coreclk
set mac_scan_coreclk_pin [get_pins u_phy0_mplla_word_fr_clk_d2/u_clk_mux2/u_tc_lib_clk_mux/Y]
create_generated_clock -add \
  -name         mac_scan_coreclk \
  -source       [prefixing $hiervar phy0/pma/mplla_ana_word_clk_i] \
  -master_clock [get_clocks ${SNPS_CLOCK_PREFIX}phy0_mplla_ana_word_clk_i] \
  -divide_by    2 \
  $mac_scan_coreclk_pin

###################################################################################################

