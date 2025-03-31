############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_clock_queries_pre_stop_clocks.tcl
#
# PIPE(UPCS+PHY) synthesis 1st implicit timing update required to query clocks and their periods reaching on different pins for stop propagations and io constraints
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

if { !$dwc_dpalt_phy || $pcie_supported } {
 #for nominal products this path is not a loop
 #https://jira.internal.synopsys.com/browse/P80001562-406288
 set fw_clk_int_mux_sel [get_pins -quiet [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/DPALT_PHY_0_mphy_mux*fw_clk_int_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_s_pin]]
 if { [sizeof_collection $fw_clk_int_mux_sel] > 0  } {
  set_disable_timing $fw_clk_int_mux_sel
 }
}

# Disable timing through the output of the AND gate that controls
# ref_dig_clk isolation.  The ref_clk is guaranteed to be off at this
# point so there is no valid path here.  The tool however will see
# combinational paths that are not real
set_disable_timing [get_pins [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/isolate_ref_dig_clk_or/bcm_or/$or_src_inst_name/$or_src_z_pin]]

# Disable timing path through the isolate_en_int to break the timing loop from

# mpll{a,b}_force_ack_i through this pin.
# The input pin toggles when clock is off, synchronous timing check through this pin is
# unnecessary.
set_disable_timing [get_pins [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/isolate_en_or/bcm_or/$or_src_inst_name/$or_src_z_pin]]

# To disable the timing through isolation control signal
if { [sizeof_collection [get_pins -quiet [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_ovrd_mux/z]]] > 0 } {
 set_disable_timing [get_pins [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_ovrd_mux/gen_mux_0__bcm_mx_inst/$mx_src_inst_name/$mx_src_out_pin]]
} else {
 set_disable_timing [get_pins [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_hand_gen_and16/and_inst14/and2/bcm_and_inst/$and_src_inst_name/$and_src_z_pin]]
}

if { $GCA_SHELL || $PT_SHELL || $DC_SHELL } {
 for {set phy 0} {$phy < $nphys} {incr phy} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 disabling timing for phy $phy arcs"
  # to disable the timing loop in ref clk en logic through reset path
  # To disable the timing through RST to Q pin of register handshake_refclk_en_phy0_reg
  # To break comboLoop, It does not cause loop to go in infinite state.
  set_disable_timing [get_cells [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/phy${phy}_ref_clk_en_flop_inst/$dff_prstn_src_inst_name]] -from $dff_prstn_src_prst_n_pin -to Q
 }
}

##1st explicit/implicit timing update
if { $DC_SHELL } {
 # clocks and uncertainties are set, now queries about clocks and period attributes can be done together which then can be used inside clock exceptions and io constraints
 update_timing
}


for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 3 identifying clocks to stop for upcs lane $lane of link $link_num"
  #scan clocks are stopped seperately
  if { $pcie_supported } {
   set mpll_glcm_not_clksrc_clks_($lane) [filter_collection [get_clocks *phy*mpll*_word*] "full_name !~ *scan* && full_name !~ *_fr_clk* && full_name !~ *phy$clksrc($link_num)*"]
   set mplla_div_not_clksrc_clks_($lane) [filter_collection [get_clocks *phy*mplla*_div_clk*] "full_name !~ *scan* && full_name !~ *_fr_clk* && full_name !~ *phy$clksrc($link_num)*"]
   set mpllb_div_not_clksrc_clks_($lane) [filter_collection [get_clocks *phy*mpllb*_div_clk*] "full_name !~ *scan* && full_name !~ *_fr_clk* && full_name !~ *phy$clksrc($link_num)*"]
   set ref_not_clksrc_clks_($lane) [filter_collection [get_clocks *phy*ref_dig_clk*] "full_name !~ *scan* && full_name !~ *_fr_clk* && full_name !~ *phy$clksrc($link_num)*"]
  }
  set mpll_glcm1_clks_($lane) [filter_collection [get_attribute $lane_mpll_word_clk_src_pin_($lane) clocks] "full_name !~ *scan*"]
  set mpll_glcm2_clks_($lane) [filter_collection [get_attribute $mpll_glcm2_out_($lane) clocks] "full_name !~ *div_clk*"]
  set mpll_glcm2_div_clks_($lane) [filter_collection [get_attribute $mpll_glcm2_out_($lane) clocks] "full_name =~ *div_clk*"]
 }
 foreach lane $pcs_lanes_in_link($link_num) {
  if { !$tx_only_supported} {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 4 identifying clocks to stop for upcs clock controller $lane of link $link_num"
   set rx_clks_on_nonsds_buf_($lane) [filter_collection [get_attribute $rx_clk_buf_inst_($lane) clocks] "full_name !~ *scan*"]
  }
 }
}

# get periods of all clocks in the design in form of array so as it can be accessed without implicit timing updates
foreach_in_collection clk $all_clocks_collection {
 set clk_name [get_attribute $clk full_name]
 set clk_period [get_attribute $clk period]
 set period($clk_name) $clk_period
 puts "\[Constraints Debug\] Info: [file tail [info script]] 5 creating clock name and period array for $clk_name with period $clk_period"
}

######################################################
##all clk muxes with scan_mode only used as selection
for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 6 listing stop pins and clocks to stop array for scan_func_mux_instances for upcs lane $lane of link $link_num"
  lappend scan_func_mux_instances \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  if { $pcs_scan_rx_clk && !$tx_only_supported } {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/lane${lane}/rx/rx_clk_div1_or_div2_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { $hdmi_supported && $hdmi_2p1_ctrl } {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/i_hdmi_pixel_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { $pclk_as_phy_input } {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pclk_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/max_pclk_int_div_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pllclk_refclk_sel_inst/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  } else {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { !$perlink_clk_arch } {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  } else {
   lappend scan_func_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
 }
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 7 listing stop pins and clocks to stop array for scan_func_mux_instances categories for phy $phy"
 lappend scan_func_mux_instances [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_clk_n_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
     [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/cr_int_clk_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
     [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/creg_clk_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 foreach lane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 8 listing stop pins and clocks to stop array for scan_func_mux_instances categories for tx $lane of phy $phy"
  lappend scan_func_mux_instances [prefixing $hiervar phy${phy}/pcs_raw/lane${lane}_tx/tx_fw_xface/tx_clk_s_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 }
}


######################################################
#all clk muxes with scan_clk_sel only used as selection
if { $pcs_scan_rx_clk && !$tx_only_supported } {
 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  foreach lane $pcs_lanes($link_num) {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 9 listing stop pins and clocks to stop array for scan_scan_mux_instances for upcs lane $lane of link $link_num"
   lappend scan_scan_mux_instances [prefixing $hiervar pcs/lane${lane}/rx/scan_rx_clk_div_int_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
 }
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 foreach lane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 10 listing stop pins and clocks to stop array for scan_scan_mux_instances categories for tx $lane of phy $phy"
  lappend scan_scan_mux_instances [prefixing $hiervar phy${phy}/pcs_raw/lane${lane}_tx/tx_fw_xface/scan_tx_clk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 }
 lappend scan_scan_mux_instances [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/scan_cr_clk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
}

lappend scan_scan_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/scan_pcs_clk_int_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
    [prefixing $hiervar pcs/upcs_clk_ctl/scan_${pclk_out_name}_int_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
    [prefixing $hiervar pcs/upcs_clk_ctl/scan_pma_clk_int_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]

if { $pclk_as_phy_input && $pcs_scan_nonsds_pclk &&  ($usb3_supported || $pcie_supported || ($hdmi_supported && $hdmi_54b_support)) } {
 lappend scan_scan_mux_instances [prefixing $hiervar pcs/upcs_clk_ctl/scan_in_pclk_nonsds_clk_int_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
}


######################################################
#all clk muxes with scan_mode and/or some functional signal as selection
#all clk muxes with active d1 when scan_mode is 1
for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 11 listing stop pins and clocks to stop array for misc_mux_inst_d1 for upcs lane $lane of link $link_num"
  if { $hdmi_supported && $hdmi_2p1_ctrl } {
   lappend misc_mux_inst_d1 \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_hdmi_prepclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pixel_clk_src_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { ($usb3_supported && !$dwc_dpalt_phy) || $pcie_supported } {
   lappend misc_mux_inst_d1 [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/usb_glcm_clk_a_mpll_word_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { !$pclk_as_phy_input } {
   lappend misc_mux_inst_d1 [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/max_pclk_clk_mux_hand/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  lappend misc_mux_inst_d1 [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_clk_mux_hand_0/bcm_ck_mx_inst/$ck_mx_src_inst_name]
 }
}
for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 12 listing stop pins and clocks to stop array for misc_mux_inst_d1 categories for phy $phy"
 lappend misc_mux_inst_d1 [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_creg_clk_mux/bcm_ck_mux/$ck_mx_src_inst_name]
}


######################################################
#all clk muxes with scan_mode and/or some functional signal as selection
#all clk muxes with active d0 when scan_mode is 1
for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 13 listing stop pins and clocks to stop array for misc_mux_inst_d0 for upcs lane $lane of link $link_num"
  if { $hdmi_supported && $hdmi_2p1_ctrl } {
   lappend misc_mux_inst_d0 \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { $pclk_as_phy_input } {
   lappend misc_mux_inst_d0 [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_mpll_pclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
 }
}

######################################################
#muxes whose select pin is driven by combination of phy0_scan_mode and phy0_scan_clk_sel
for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 14 listing cells to disable clock gating check for phy_scanMode_clkSel_mux_inst categories for phy $phy"
 lappend phy_scanMode_clkSel_mux_inst [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_tck_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
     [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/apb0_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
     [prefixing $hiervar phy${phy}/pcs_raw/cmn/gen_proto_apb_if_0__apb_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 if { $dwc_dpalt_phy } {
  lappend phy_scanMode_clkSel_mux_inst [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/DPALT_PHY_1_mphy_mux_fw_clk_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
      [prefixing $hiervar phy${phy}/pcs_raw/cmn/gen_proto_apb_if_1__apb_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
      [prefixing $hiervar phy${phy}/pcs_raw/cmn/gen_proto_apb_if_2__apb_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 }
}


######################################################
#muxes to stop scan shift clk from both paths
for {set phy 0} {$phy < $nphys} {incr phy} {
 if { $dwc_dpalt_phy } {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 15 listing cells to stop propagation of shift clock of phy_scan_shift_clk_stop_mux_inst categories for phy $phy"
  lappend phy_scan_shift_clk_stop_mux_inst [prefixing $hiervar phy${phy}/pcs_raw/cmn/gen_proto_apb_if_1__apb_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name] \
      [prefixing $hiervar phy${phy}/pcs_raw/cmn/gen_proto_apb_if_2__apb_pclk_i_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 }
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 16 listing cells to disable clock gating check for cells_for_cg_disable categories for phy $phy"
 lappend cells_for_cg_disable [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_creg_clk_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 if { !$dwc_dpalt_phy } {
  lappend cells_for_cg_disable [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/DPALT_PHY_0_mphy_mux_fw_clk_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name]
 }
 lappend cells_for_cg_disable [prefixing $hiervar phy${phy}/pcs_raw/lane*_tx/tx_ctl/sel_tx_clk_in_mux*__tx_clk_sel_mux*/bcm_ck_mux/$ck_mx_src_inst_name]
}

for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 17 listing cells to disable clock gating check for cells_for_cg_disable categories for pcs lane $lane of link $link_num"
  if { !$pclk_as_phy_input } {
   lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
   lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/max_pclk_clk_mux_hand/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  } else {
   lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/scan_pcs_lane_in_pclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_ref_dig_clk_mux/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_ref_dig_clk_mux/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_ref_dig_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_word_clk_mux/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_word_clk_mux/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_word_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_div_clk_mux/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_div_clk_mux/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_div_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_word_clk_mux/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_word_clk_mux/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_word_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  if { !$dwc_dpalt_phy } {
   lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/usb_glcm_clk_a_mpll_word_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_div_clk_mux/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_div_clk_mux/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_div_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { $hdmi_supported && $hdmi_2p1_ctrl } {
   lappend cells_for_cg_disable  \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_*/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_*/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_hdmi_prepclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pixel_clk_src_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  if { $hdmi_supported && $hdmi_54b_support } {
   lappend cells_for_cg_disable  \
       [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_54ui_mux_hand/bcm_ck_mx_inst/$ck_mx_src_inst_name]
  }
  # Funtional Clock Static Muxes
  lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_mpll_pclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_clk_mux_hand_0/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_*_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
 }
}

if { $perlink_clk_arch } {
 if {$pipe_nlinks == "2"} {
  lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/mux_gblock_*_/bcm_ck_mx_inst/$ck_mx_src_inst_name]
 }
 if {$pipe_nlinks == "4"} {
  lappend cells_for_cg_disable [prefixing $hiervar pcs/upcs_clk_ctl/mux_gblock_*_/clk01_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/mux_gblock_*_/clk23_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name] \
      [prefixing $hiervar pcs/upcs_clk_ctl/mux_gblock_*_/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name]
 }
}

## procedures to create arrays
#1)   of clocks to stop and the pins to stop at
#2)   of cells to disable clock gating check at
foreach {inst_obj} $scan_func_mux_instances {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 18 creating arrays for list scan_func_mux_instances of clocks to stop, pins to stop and cells to disable clock gating check for $inst_obj"
 set scan_pin [get_pins -of ${inst_obj} -filter "full_name =~ */$ck_mx_src_clk1_pin" ]
 set data_pin [get_pins -of ${inst_obj} -filter "full_name =~ */$ck_mx_src_clk0_pin" ]
 lappend cells_for_cg_disable [get_object_name [get_cells -of $scan_pin]]
 set leaf_scan_pin [get_object_name $scan_pin]
 set leaf_data_pin [get_object_name $data_pin]
 set stop_func_clks_scan_pin [filter_collection [get_attribute -quiet [get_pins ${leaf_scan_pin}] clocks] "full_name !~ *scan*"]
 set stop($leaf_scan_pin) $stop_func_clks_scan_pin
 set num_func_clocks [sizeof_collection $stop($leaf_scan_pin)]
 if { $num_func_clocks > 0 } {
  append_to_collection pins_to_stop_at $scan_pin
 }
 if { !$remove_upcs_scan_constraints } {
  set stop_scan_clks_func_pin [filter_collection [get_attribute [get_pins ${leaf_data_pin}] clocks] "full_name =~ *scan*"]
  set stop($leaf_data_pin) $stop_scan_clks_func_pin
  set num_scan_clocks [sizeof_collection $stop($leaf_data_pin)]
  if { $num_scan_clocks > 0 } {
   append_to_collection pins_to_stop_at $data_pin
  }
 }
}

foreach inst_obj $phy_scanMode_clkSel_mux_inst {
 set pin_names [filter_collection [get_pins ${inst_obj}/*] "full_name !~ */$ck_mx_src_s_pin && pin_direction == in"]
 foreach_in_collection pin $pin_names {
  set leaf_pin $pin
  puts "\[Constraints Debug\] Info: [file tail [info script]] 19 creating arrays for list phy_scanMode_clkSel_mux_inst of cells to disable clock gating check for $inst_obj of pin $leaf_pin"
  lappend cells_for_cg_disable [get_object_name [get_cells -of $pin]]
 }
}

foreach inst_obj $scan_scan_mux_instances {
 set pin_names [filter_collection [get_pins ${inst_obj}/*] "full_name !~ */$ck_mx_src_s_pin && pin_direction == in"]
 foreach_in_collection pin $pin_names {
  set leaf_pin $pin
  puts "\[Constraints Debug\] Info: [file tail [info script]] 20 creating arrays for list scan_scan_mux_instances of clocks to stop, pins to stop and cells to disable clock gating check for $inst_obj for the pin $leaf_pin"
  lappend cells_for_cg_disable [get_object_name [get_cells -of $pin]]
  if { !$remove_upcs_scan_constraints } {
   set leaf_obj [get_object_name $leaf_pin]
   set pin_obj [get_object_name $pin]
   set stop_func_clks_scan_pin [filter_collection [get_attribute [get_pins ${leaf_obj}] clocks] "full_name !~ *scan*"]
   set stop($leaf_obj) $stop_func_clks_scan_pin
   set scan_pin ""
   set num_clocks [sizeof_collection $stop($leaf_obj)]
   if { $num_clocks > 0 } {
    append_to_collection pins_to_stop_at $leaf_pin
   }
  }
 }
}

if { !$remove_upcs_scan_constraints } {
 #When scan_mode=1, d0 is selected, so d1 scan clocks are stopped
 foreach inst_obj $misc_mux_inst_d0 {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 21 creating arrays for list misc_mux_inst_d0 of clocks to stop, pins to stop and cells to disable clock gating check for $inst_obj"
  set data_pin [get_pins -of ${inst_obj} -filter "full_name =~ */$ck_mx_src_clk1_pin"]
  set leaf_data_pin [get_object_name $data_pin]
  set stop_scan_clks_func_pin [filter_collection [get_attribute [get_pins ${leaf_data_pin}] clocks] "full_name =~ *scan*"]
  set stop($leaf_data_pin) $stop_scan_clks_func_pin
  set num_data_clocks [sizeof_collection $stop($leaf_data_pin)]
  if { $num_data_clocks > 0 } {
   append_to_collection pins_to_stop_at $data_pin
  }
 }

 #When scan_mode=1, d1 is selected, so d0 scan clocks are stopped
 foreach inst_obj $misc_mux_inst_d1 {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 22 creating arrays for list misc_mux_inst_d1 of clocks to stop, pins to stop and cells to disable clock gating check for $inst_obj"
  set scan_pin [get_pins -of ${inst_obj} -filter "full_name =~ */$ck_mx_src_clk0_pin"]
  set leaf_scan_pin [get_object_name $scan_pin]
  set stop_scan_clks_func_pin [filter_collection [get_attribute [get_pins ${leaf_scan_pin}] clocks] "full_name =~ *scan*"]
  set stop($leaf_scan_pin) $stop_scan_clks_func_pin
  set num_scan_clocks [sizeof_collection $stop($leaf_scan_pin)]
  if { $num_scan_clocks > 0 } {
   append_to_collection pins_to_stop_at $scan_pin
  }
 }

 foreach inst_obj $phy_scan_shift_clk_stop_mux_inst {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 23 creating arrays for list phy_scan_shift_clk_stop_mux_inst of clocks to stop and, pins to stop for $inst_obj"
  set scan_pin [get_pins -of ${inst_obj} -filter "full_name =~ */$ck_mx_src_clk0_pin"]
  set leaf_scan_pin [get_object_name $scan_pin]
  set stop_scan_clks_func_pin [filter_collection [get_attribute [get_pins ${leaf_scan_pin}] clocks] "full_name =~ *scan*shift*"]
  set stop($leaf_scan_pin) $stop_scan_clks_func_pin
  set num_scan_clocks [sizeof_collection $stop($leaf_scan_pin)]
  if { $num_scan_clocks > 0 } {
   append_to_collection pins_to_stop_at $scan_pin
  }
 }
}
set cells_for_cg_disable [lsort -unique $cells_for_cg_disable]

