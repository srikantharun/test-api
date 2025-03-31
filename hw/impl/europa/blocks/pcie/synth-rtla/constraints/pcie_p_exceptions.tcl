############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_exceptions.tcl
#
# PIPE(UPCS+PHY) synthesis all exceptions other than dft specific and clocks specifics
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

##### MULTICYCLE PATHS
# 8b10b mcp do not solve the problems for customer due to variations of delays across runs and would not be feasible to meet shifted setup and
# hold windiw

# PHY Multicycle Exceptions
set_multicycle_path -setup 2 -from [get_clocks ${SNPS_CLOCK_PREFIX}phy*_jtag_clk_n] -through [get_driver_cell_pin [get_pins [prefixing $hiervar phy*/pcs_raw/cmn/creg_ctl/creg_jtag/crsel_reg/capture_val[*]]]]
set_multicycle_path -hold 1 -end -from [get_clocks ${SNPS_CLOCK_PREFIX}phy*_jtag_clk_n] -through [get_driver_cell_pin [get_pins [prefixing $hiervar phy*/pcs_raw/cmn/creg_ctl/creg_jtag/crsel_reg/capture_val[*]]]]

##-- PHY - Set Case Analysis
# Propagate the functional tx_clk_i PHY input (others are used for ATE)
set_case_analysis 1 [prefixing $hiervar phy*/pcs_raw/lane*/tx_ctl/tx_pma_clk_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_s_pin]

# Only applicable for Non-serdes protocol
if { !$tx_only_supported && !($pcie_supported  && $serdes_mode)} {
 # Set Max delay constraints for async transfers in estore
 if { $pcie_supported } {
  set max_async_skew [freq2per $RX_DWCLK_FREQ]
 } else {
  set max_async_skew [freq2per $RX_DWCLK_NONSDS_FREQ]

 }

 # For STA,an option '-ignore_clock_latency' needs to be added to set_max_delay commands to avoid unnecessary
 # clock network path delays added to the max delay checks.

 foreach_in_collection dest_clk $upcs_mpll_estore_rd_clk {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 applying max delay constraint with respect to [get_object_name $dest_clk]"
   set_max_delay $max_async_skew -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/ug_estore_data_wr*/Q*"]] -to [get_object_name $dest_clk] -ignore_clock_latency
   set_max_delay $max_async_skew -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/wr_ptr_0_gray*/Q*"]]     -to [get_object_name $dest_clk] -ignore_clock_latency
   set_max_delay $max_async_skew -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/pre_write_cntr*/Q*"]]    -to [get_object_name $dest_clk] -ignore_clock_latency
   set_min_delay 0.0 -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/ug_estore_data_wr*/Q*"]] -to [get_object_name $dest_clk] -ignore_clock_latency
   set_min_delay 0.0 -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/wr_ptr_0_gray*/Q*"]]     -to [get_object_name $dest_clk] -ignore_clock_latency
   set_min_delay 0.0 -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/pre_write_cntr*/Q*"]]    -to [get_object_name $dest_clk] -ignore_clock_latency

  #### FALSE PATHS
  # No timing analysis to be done in the paths other than Estore
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_gen_sync_handshake_lane_pcs_sync_rst_sync2rx/d_ack*/Q*"]]   -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*blk_aligned*/Q*"]]                      -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*rx_aligned*/Q*"]]                      -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_rx_cdr_valid_u0/rx_valid*/Q*"]]     -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*los_for_valid_s1*/Q*"]]                   -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*phy_rx_valid_d5_i_*/Q*"]]               -to $dest_clk
  set_false_path    -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_gen_sync_handshake_lpc_rx_eb_reset_req/d_ack_*/Q*"]]            -to $dest_clk

 }

 # False path as rx_status mux sel is usb_p3&rx_det_p3 which gates the combo path propagating from estore to rx_status
set_false_path   -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/*pipe_estore_u0/ug_estore_data_wr*/Q*"]] -through [get_pins [prefixing $hiervar *pipe_rx?_status[*]]]

 set data_pin "bcm41_inst/U_SYNC/GEN_FST3_${sync_3_stage_src_inst_name}_*/$sync_3_stage_src_data_s_pin"

 set_false_path   -from [get_clocks  *rx*asic*clk*] -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/phy_rx_valid_sync2pclk_gen_sync/${data_pin}"]]
 set_false_path   -from [get_clocks  *rx*asic*clk*] -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/phy_rx_valid_sync2pcs_gen_sync/${data_pin}"]]
 set_false_path   -from [get_clocks  *rx*asic*clk*] -through [get_pins [prefixing $hiervar "pcs/lane*/rx*/lane_rx_serdes/pipe_gen_sync_phy_rx_valid_sync2pclk/${data_pin}"]]
} ;#protocol !dp_hdmi

set phy_iso_pins [list  [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/isolate_en_final_gen_buf/gen_bit_0__bcm_ck_buf/$ck_buf_src_inst_name/$ck_buf_src_clk_out_pin] \
                      [prefixing $hiervar phy*/pcs_raw/aon/aon_cmn/isolate_ref_dig_clk_or/bcm_or/$or_src_inst_name/$or_src_z_pin]]

if { [sizeof_collection [get_pins -quiet [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_ovrd_mux/z]]] > 0 } {
 lappend phy_iso_pins [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_ovrd_mux/gen_mux_0__bcm_mx_inst/$mx_src_inst_name/$mx_src_out_pin]
} else {
 lappend phy_iso_pins [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/pcs_isolate_en_hand_gen_and16/and_inst14/and2/bcm_and_inst/$and_src_inst_name/$and_src_z_pin]
}
set_false_path -through [get_pins $phy_iso_pins]

set cr_para_rd_data_name [get_bitblasted_signal cr_para_rd_data $jtag_pma_bit_blasted]
set cr_para_name [get_bitblasted_signal cr_para $jtag_pma_bit_blasted]
# Set a false path through any non-cr_para bus input to the cr_para_rd_data from
# the PMA for functional clocks.
set_false_path -through [remove_from_collection [get_pins [prefixing $hiervar phy*/${pma_inst_name}/*] -filter "direction==in"] \
                             [get_pins [prefixing $hiervar phy*/${pma_inst_name}/${cr_para_name}*]]] -through [get_pins [prefixing $hiervar phy*/${pma_inst_name}/${cr_para_rd_data_name}*]] \
    -to [get_clocks [list ${SNPS_CLOCK_PREFIX}*ref*clk* \
                         ${SNPS_CLOCK_PREFIX}apb_pclk \
                         ${SNPS_CLOCK_PREFIX}phy*_jtag_clk_n \
                         ${SNPS_CLOCK_PREFIX}phy*_fw_clk ]]

set cr_false_paths [remove_from_collection [get_pins [prefixing $hiervar phy*/${pma_inst_name}/*]] \
                        [get_pins [prefixing $hiervar phy*/${pma_inst_name}/${cr_para_name}*]]]
set_false_path -through  $cr_false_paths \
    -from [get_clocks [list ${SNPS_CLOCK_PREFIX}*ref*clk* \
                           ${SNPS_CLOCK_PREFIX}apb_pclk \
                           ${SNPS_CLOCK_PREFIX}phy*_jtag_clk_n \
                           ${SNPS_CLOCK_PREFIX}phy*_fw_clk ]]

# scan clock from creg_clk_scan_mux should not propagate to dtb_out_scan_mux d0 pin
# Should not check func clock timing on dtb_out_r register
if { [sizeof_collection $dtb_out_scan_mux_d0_pins] > 0 } {
 set_false_path -through $dtb_out_scan_mux_d0_pins
 set_false_path -from [get_clocks $ip_all_func_clocks] -to $dtb_out_reg_in_pins

}
if { [sizeof_collection $raw_pcs_clk_mux_d0_pins] > 0 } {
 set_false_path -through $raw_pcs_clk_mux_d0_pins
}

if { !$remove_upcs_scan_constraints } {
 #https://jira.internal.synopsys.com/browse/P80001562-452671, scan arc through functional path is false and can only propagate through clk1 pin when scan_mode is 1
 set_false_path -from [get_clocks $ip_all_shift_clks] -through [get_pins [prefixing $hiervar phy*/pcs_raw/cmn/mplla_clk_ovrd_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
 set_false_path -from [get_clocks $ip_all_shift_clks] -through [get_pins [prefixing $hiervar phy*/pcs_raw/cmn/mpllb_clk_ovrd_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]

 set_false_path -through  $cr_false_paths \
     -from [get_clocks ${SNPS_CLOCK_PREFIX}phy?_scan_cr_clk ]
}

if { $usb4_supported && $PMA_NAME == "c40" } {
 # Set a false path through PMA mpll[a,b]_state starting from any functional and SCAN-ASST clock and reaching to cr register in pcs_raw through UPCS
 set_false_path -through [get_pins [prefixing $hiervar phy*/pma/mpll?_state]] \
     -from [get_clocks [list ${SNPS_CLOCK_PREFIX}*phy*ref*clk*] \
                ${SNPS_CLOCK_PREFIX}apb_pclk \
                ${SNPS_CLOCK_PREFIX}phy*_jtag_clk_n \
                ${SNPS_CLOCK_PREFIX}phy*_fw_clk ]]

if { !$remove_upcs_scan_constraints } {
 set_false_path -through [get_pins [prefixing $hiervar phy*/pma/mpll?_state]] \
     -from [get_clocks ${SNPS_CLOCK_PREFIX}phy*_scan_cr_clk]
}

}

if { $usb3_supported  || $pcie_supported } {
 # Path from pipe_laneX_powerdown to pipe_rxX_status through pcs/pipe_ctl_inst/lane0_pwr_ctl/pcs_lane_goto_p2_p4_usb is asynchronous (U3 path)
 set_false_path -from $ip_all_func_pclks \
     -through [get_pins [prefixing $hiervar pcs/lane*/rx/pcs_lane_goto_p2_async_inst/bcm_buf_inst/$buf_src_inst_name/$buf_src_z_pin]] \
     -through [get_pins [prefixing $hiervar pcs/lane*/rx/pcs_rx_status_mux/gen_mux_*__bcm_mx_inst/$mx_src_inst_name/$mx_src_z_pin]]
}

if { $usb3_supported  || ($pcie_supported && !$serdes_mode) } {
 # False path on es_mode reg for USB3 PCS/PMA functional clocks
 # Transition on es_mode reg would happen when Rx datapath of non-serdes is not in use
 # USB3- Gen1/2, PCIe-Gen1/2/3/4 funtional clks, scan clks are not included
 if { !$remove_upcs_scan_constraints } {
  set_false_path -through [get_pins [prefixing $hiervar pcs/pipe_ctl_inst/lane*_pwr_ctl/pipe_lpc/u_pipe_lpc_mux/lpc_rx_es_mode_reg/Q*]] \
      -to [remove_from_collection [get_clocks [list *lane*pcs_clk_* *lane*_pma_clk_*]] [get_clocks *scan*clk*]]
 } else {
  set_false_path -through [get_pins [prefixing $hiervar pcs/pipe_ctl_inst/lane*_pwr_ctl/pipe_lpc/u_pipe_lpc_mux/lpc_rx_es_mode_reg/Q*]] \
      -to [get_clocks [list *lane*pcs_clk_* *lane*_pma_clk_*]]
 }
}

# False path between pcs/pcs_lane*_powerdown* and all async_resets
# Remove hierarchical pin from earlier exception, added leaf cell pin
set_false_path -from $ip_all_func_clocks \
    -through [get_pins [prefixing $hiervar  pcs/pipe_ctl_inst/GLUE/phy?_pwr_en_hand_gen_or2/bcm_or_inst/$or_src_inst_name/$or_src_z_pin]] \
    -through [get_pins [prefixing $hiervar pcs/pipe_ctl_inst/GLUE/async_phy?_reset_hand_gen_or_1/or2/bcm_or_inst/$or_src_inst_name/$or_src_z_pin]]

if { $pclk_as_phy_input } {
 # NOTE FOR INTEGRATION -
 # In integration mode, PCLKs are expected to be defined at higher levels and propagate down to the UPCS(PHY IP)
 # Therefore, stop propagation of internally defined PCLK is protected under NOT of integration mode
 # At integration mode, these constraints can be re-used with correct names of all N_PCLK
 if { ! ($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
  # False path on es_mode reg for PCLK functional clocks
  # Transition on es_mode reg would happen when Rx datapath of non-serdes is not in use
  if { !$tx_only_supported } {
   if { !$remove_upcs_scan_constraints } {
    set_false_path -through [get_pins [prefixing $hiervar  pcs/pipe_ctl_inst/lane*_pwr_ctl/pipe_lpc/u_pipe_lpc_mux/lpc_rx_es_mode_reg/Q*]] \
        -to [remove_from_collection [get_clocks [list *lane*_pclk* core_clk*]] [get_clocks *scan*clk*]]
   } else {
    set_false_path -through [get_pins [prefixing $hiervar  pcs/pipe_ctl_inst/lane*_pwr_ctl/pipe_lpc/u_pipe_lpc_mux/lpc_rx_es_mode_reg/Q*]] \
        -to [get_clocks [list *lane*_pclk* core_clk*]]
   }
  }

 }
}


if { $DC_SHELL || $flow == "syn"} {
 ##### IDEAL NETWORK
 # Set the isolate_en signals as an ideal network to prevent
 # issues with high-fanout
 set_ideal_network [get_pins $phy_iso_pins]

 # Exception valid for INTEGRATION level as well
 # Ideal network on isolate_enable pins to prevent issues with high-fanout
 if {$separate_vp_vdd_support == 1} {
  if { $SYNTH_UPF_FLOW == 1} {
   set_ideal_network [get_ports [prefixing $hiervar_ phy*_vpoff_vddon_iso_en]]
   set_ideal_network [get_ports [prefixing $hiervar_ phy*_vpon_vddoff_iso_en]]
  }
 }
}

# Data to data check
# Limit the maximum allowed skew for multi-bit synchronizer inputs
#to 80% of destination clock period

# Updated set_data_check loop for runtime improvement
# get_attribute followed by set_data_check in a loop invokes update_timing
# after every instance in the loop
# Query clock/cell attributes in different loops and collect the information
# in arrays which can be used in a different set_data_check loop


# This loop applies set_data_check on bus synchronizer cells
# using information collected in arrays above
foreach_in_collection gen_bus_sync_cell $gen_bus_sync_cells {
 set gen_cell_name [get_object_name $gen_bus_sync_cell]
 #echo "\nset_data_check on gen cell $gen_cell_name.   t_setup = $t_setup_val($gen_cell_name)... Leaf sync d pins as follows: \n [get_object_name $leaf_sync_d_pins_col($gen_cell_name)]"
 puts "\[Constraints Debug\] Info: [file tail [info script]] 2 set_data_check for gen bus sync cell $gen_cell_name across all wires of bus with t_setup = $t_setup_val($gen_cell_name)"

 set data_check_flag 0
 foreach_in_collection pin1 $leaf_sync_d_pins_col($gen_cell_name) {
  foreach_in_collection pin2 $leaf_sync_d_pins_col($gen_cell_name) {
   if { [string compare [get_object_name $pin1] [get_object_name $pin2]]!=0 } {
    set_data_check -from $pin1 -to $pin2 -setup $t_setup_val($gen_cell_name)
    set data_check_flag 1
   }
  }
 }
 if { $data_check_flag } {
  echo "Information: Max skew constraint set to $max_skew_val($gen_cell_name) (80% of $min_clk_name($gen_cell_name) period)."
 } else {
  echo "Warning: Max skew constraint could not be applied."
 }
}

##########################################################################################################


set_false_path -through [get_pins ${pcie_core_inst}rx_lane_flip_en]
set_false_path -through [get_pins ${pcie_core_inst}tx_lane_flip_en]


set_false_path -through [get_pins ${pcie_ss_inst}u_pcie_gen_ctrl/*phy_reset*]  -through [get_pins ${pcie_clk_rst_inst}soft_phy_reset_n]
set_false_path -through [get_pins ${pcie_ss_inst}u_pcie_gen_ctrl/*warm_reset*] -through [get_pins ${pcie_clk_rst_inst}soft_warm_reset_n]
set_false_path -through [get_pins ${pcie_ss_inst}u_pcie_gen_ctrl/*cold_reset*] -through [get_pins ${pcie_clk_rst_inst}soft_cold_reset_n]

set_false_path \
 -from \
 ${pcie_core_inst}u_DWC_pcie_native_core/u_DWC_pcie_core/u_radm_ep/u_radm_q_seg_buf/u_hdr_DW_sbc/start_addr*
set_false_path \
 -from \
 ${pcie_core_inst}u_DWC_pcie_native_core/u_DWC_pcie_core/u_radm_ep/u_radm_q_seg_buf/u_data_DW_sbc/start_addr*
set_false_path \
 -from \
 ${pcie_core_inst}u_DWC_pcie_native_core/u_DWC_pcie_core/u_radm_ep/u_radm_q_seg_buf/u_hdr_DW_sbc/end_addr_m1*
set_false_path \
 -from \
 ${pcie_core_inst}u_DWC_pcie_native_core/u_DWC_pcie_core/u_radm_ep/u_radm_q_seg_buf/u_data_DW_sbc/end_addr_m1*




########################################################################################################
#max delay setting between async clock domain
########################################################################################################
#max delay setting between async clock domain
## bwtween core clocks and axi clocks
##Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals) 
set ck_lst1 [get_clocks [list \
                        core_clk* \
                        ]]

set ck_lst2 [get_clocks [list \
                        mstr_aclk* \
                        slv_aclk*  \
                        dbi_aclk*  \
                        ]]

set m_value 1.67
set_max_delay_between_clock_lists $m_value $ck_lst1 $ck_lst2

set m_value 2.0
set_max_delay_between_clock_lists $m_value $ck_lst2 $ck_lst1

###############################################################
## bwtween apb_pclk clocks and core clocks
set ck_lst1 [get_clocks [list \
                         core_clk* \
                        ]] 

set ck_lst2 [get_clocks [list \
                        apb_pclk* \
                        ]]

set m_value 15.0
set_max_delay_between_clock_lists $m_value $ck_lst1 $ck_lst2

set m_value 3.0
set_max_delay_between_clock_lists $m_value $ck_lst2 $ck_lst1

###########################################
# Include top-level timing exception files.
# These files may contain non-standard SDC commands.
###########################################
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : common.tcl
# Description : Common procs and settings used by CDC constraint files


if {$::synopsys_program_name eq "dc_shell"} {
  redirect /dev/null {report_clocks [get_clocks]}
}

namespace eval BCM {

  variable ignore_clock_latency_option "-ignore_clock_latency"
  variable reset_path_option ""
  variable bcm_hier_to_skip ""
  variable bcm_mod_to_skip ""
  variable cmd_list_bcm_all {}
  variable bcm_constrain_input_ports 1

  variable name_attr "name"
  variable template_style 0
  variable cmnts_arr
  # We would like to use different comments for different constraints, but it
  # seems that tools (DC/FC) only apply the last comments on the same path. So,
  # use same comments for both max delay and min delay for now.
  #array set cmnts_arr {
  #  CDC_SYN_02_max {Define set_max_delay of 1 source clock period for Gray-coded signals}
  #  CDC_SYN_02_min {Define set_min_delay of 0 for Gray-coded signals}
  #  CDC_SYN_03_max {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period for Qualifier-based Data Bus signals}
  #  CDC_SYN_03_min {Define set_min_delay of 0 for Qualifier-based Data Bus signals}
  #  CDC_SYN_04_max {Define set_max_delay of 1 destination clock period for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
  #  CDC_SYN_04_min {Define set_min_delay of 0 for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
  #  CDC_SYN_05     {Define set_false_path -through for quasi-static signals at the output of the Bus Delay components}
  #  MCP_SYN        {Define set_multicycle_path for multi-cycle delay cells}
  #}
  array set cmnts_arr {
    CDC_SYN_02_max {Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals}
    CDC_SYN_02_min {Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals}
    CDC_SYN_03_max {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals}
    CDC_SYN_03_min {Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals}
    CDC_SYN_04_max {Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
    CDC_SYN_04_min {Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)}
    CDC_SYN_05     {Define set_false_path -through for quasi-static signals at the output of the Bus Delay components}
    MCP_SYN        {Define set_multicycle_path for multi-cycle delay cells}
  }

  variable design_list {.*}
  set design_list {ep_x4_DWC_pcie_ctl}
  if {($design_list ne {.*}) && (![regexp {^(\s*\w+\s*)+$} $design_list])} {
    set design_list {.*}
  }

  if {($::synopsys_program_name eq "fc_shell") || ($::synopsys_program_name eq "pt_shell")} {
    alias bcm_all_fanin {all_fanin -quiet}
    alias bcm_all_fanout {all_fanout -quiet}
  } else {
    alias bcm_all_fanin {all_fanin}
    alias bcm_all_fanout {all_fanout}
  }

  proc bcm_puts {severity str} {
    set msg_tag "(BcmCdcConstraint)"
    if {$severity eq "DBG"} {
      if {![catch {getenv DWC_BCM_TCL_SNPS_DEBUG}]} {
        puts "$severity: $str $msg_tag"
      }
    } elseif {$severity eq "WARNFST0"} {
      if {![catch {getenv DWC_BCM_WRN_SYNC_NOREG}]} {
        puts "WARN: $str $msg_tag"
      }
    } else {
      puts "$severity: $str $msg_tag"
    }
  }

  proc getBCMClocks { cell_name pin_name } {
    if {[get_pins -quiet $cell_name/$pin_name] eq ""} {
      return ""
    }
    # find all the clocks associated to the pin
    set clks [get_clocks -quiet [get_attribute -quiet [get_pins -quiet $cell_name/$pin_name] clocks]]
    if { [sizeof_collection $clks] == 0 } {
      # second try for compiled netlist where clock attribute only exists in leaf pins
      set pins [bcm_all_fanout -from $cell_name/$pin_name -endpoints_only -flat]
      append_to_collection -unique clks [get_attribute -quiet $pins clocks]
    }
    if { [sizeof_collection $clks] == 0 } {
      # third try if something before this cell stops the clock propagation
      set pins [bcm_all_fanin -to $cell_name/$pin_name -startpoints_only -flat]
      append_to_collection -unique clks [get_attribute -quiet $pins clocks]
    }
    if { [sizeof_collection $clks] == 0 } {
      bcm_puts "WARN" "Cannot get associated clocks on pin $pin_name of $cell_name. Cell will be skipped."
    }
    return $clks
  }

  proc getBCMClockPeriod { cell_name pin_name clks } {
    set allPeriods [get_attribute -quiet $clks period]
    if {$allPeriods ne ""} {
      set clkPeriod [tcl::mathfunc::min {*}$allPeriods]
      bcm_puts "DBG" "getBCMClockPeriod: cell name $cell_name - pin name $pin_name - clocks [get_object_name $clks] - period $clkPeriod"
    } else {
      set clkPeriod ""
      bcm_puts "WARN" "Period is not defined for clock [get_object_name $clks], which is associated to pin $pin_name of $cell_name. Cell will be skipped."
    }
    return $clkPeriod
  }

  proc checkTemplateNamingStyle {} {
    set value 0
    set template_naming_style ""
    set template_parameter_style ""
    set template_separator_style ""
    if {$::synopsys_program_name eq "fc_shell"} {
      set template_naming_style [get_app_option_value -name hdlin.naming.template_naming_style]
      set template_parameter_style [get_app_option_value -name hdlin.naming.template_parameter_style]
      set template_separator_style [get_app_option_value -name hdlin.naming.template_separator_style]
    } elseif {($::synopsys_program_name eq "dc_shell") || ($::synopsys_program_name eq "dcnxt_shell")} {
      set template_naming_style [get_app_var template_naming_style]
      set template_parameter_style [get_app_var template_parameter_style]
      set template_separator_style [get_app_var template_separator_style]
    } else {
      set value 2
    }
    if {
      ($template_naming_style eq {%s_%p}) &&
      (($template_parameter_style eq {%s%d}) || ($template_parameter_style eq {%d})) &&
      ($template_separator_style eq {_})
    } {
      set value 1
    }
    if {$value == 0} {
      puts "INFO: Cannot get the value of BCM parameters, because tool options template_*_style probably have non-default settings."
      puts "      Supported template_naming_style is %s_%p, supported template_parameter_style is %s%d or %d, supported template_separator_style is _"
      puts "      Normally this won't impact constraint setting, but you may see warnings like 'Unable to find synchronization flip-flop ...'."
      puts "      These warnings can be ignored if parameter F_SYNC_TYPE of some BCM modules is intentionally set to 0."
      puts "      Set 'template_*_style' to supported styles if you want to avoid such warnings."
    }
    return $value
  }
  set template_style [checkTemplateNamingStyle]

  proc getBCMParamFromNameOrIndex { cell bcmSuffix bcmParamName bcmParamIndex } {
    variable template_style
    set cell_name [get_object_name $cell]
    set value ""
    if {$template_style == 1} {
      set ref_name [get_attribute $cell ref_name]
      if {![regsub ".*_${bcmSuffix}_" $ref_name {} paramString]} {
        # No instance name match.
        return $value
      }
      # First look by name PARAMA<valueA>_PARAMB<valueB>_...
      if {![regexp "${bcmParamName}(\[^_\]+)" $paramString match value]} {
        # Look by index <valueA>_<valueB>_...
        set parameters [split $paramString _]
        if {[llength $parameters] >= $bcmParamIndex} {
          set value [lindex $parameters $bcmParamIndex]
        }
      }
    }
    if {$value eq ""} {
      bcm_puts "DBG" "Cannot get the value of parameter $bcmParamName in $cell_name."
    }
    return $value
  }

  # Get name of reference design 'level' levels above the given cell name
  proc getBCMParent {cell_name level} {
    set names [split $cell_name /]
    set name [join [lrange $names 0 end-$level] /]
    if {$name ne ""} {
      return [get_attribute -quiet [get_cells -quiet $name] ref_name]
    }
    return ""
  }

  proc runCmd { cmd } {
    bcm_puts "DBG" $cmd
    eval $cmd
  }

  if {![catch {getenv DWC_BCM_DISABLE_IGNORE_CLOCK_LATENCY}]} {
    set ignore_clock_latency_option ""
    bcm_puts "DBG" "DWC_BCM_DISABLE_IGNORE_CLOCK_LATENCY is defined, -ignore_clock_latency won't be used."
  }

  if {![catch {getenv DWC_BCM_RESET_PATH}]} {
    set reset_path_option "-reset_path"
    bcm_puts "DBG" "DWC_BCM_RESET_PATH is defined, -reset_path will be used."
  }

  if {![catch {getenv DWC_BCM_HIER_TO_SKIP}]} {
    set bcm_hier_to_skip [getenv DWC_BCM_HIER_TO_SKIP]
    if {[llength $bcm_hier_to_skip] > 0} {
      bcm_puts "DBG" "DWC_BCM_HIER_TO_SKIP is defined, skip constraints on BCM instances under $bcm_hier_to_skip."
    }
  }

  if {![catch {getenv DWC_BCM_MOD_TO_SKIP}]} {
    set bcm_mod_to_skip [getenv DWC_BCM_MOD_TO_SKIP]
    if {[llength $bcm_mod_to_skip] > 0} {
      bcm_puts "DBG" "DWC_BCM_MOD_TO_SKIP is defined, skip constraints on BCM modules $bcm_mod_to_skip."
    }
  }

  if {![catch {getenv DWC_BCM_CONSTRAIN_INPUT_PORTS}]} {
    if {$::env(DWC_BCM_CONSTRAIN_INPUT_PORTS) == 0} {
      set bcm_constrain_input_ports 0
      bcm_puts "DBG" "DWC_BCM_CONSTRAIN_INPUT_PORTS is defined as 0, skip constraints on the paths starting from primary inputs."
    }
  }

  if {$::synopsys_program_name eq "pt_shell"} {
    set name_attr base_name
  }

}; # end of namespace BCM (common procs and vars)

#===============================================================================
# Create Guard for file DWbb_bcm21_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm21_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : DWbb_bcm21_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints


# -----------------------------------------------------------------------------
# [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
# BCM21 set_max_delay | set_min_delay constraints
#namespace eval BCM {
#
#  proc set_cstr_bcm21 {} {
#    variable ignore_clock_latency_option
#    variable reset_path_option
#    variable bcm_hier_to_skip
#    variable bcm_mod_to_skip
#    variable cmd_list_bcm_all
#    variable bcm_constrain_input_ports
#    variable name_attr
#    variable cmnts_arr
#    variable design_list
#
#    foreach design $design_list {
#      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm21$"] >= 0 } {
#        continue
#      }
#      set cell_collection_bcm21 [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm21.*) AND @ref_name!~.*_bcm21_a.* AND @ref_name!~.*_bcm21_cg.* AND @ref_name!~.*_bcm21_neo.* AND @ref_name!~.*_bcm21_tgl.*"]
#      # Parent modules of bcm21 which have their own constraints
#      set bcm21_excl_parents_expr_lvl1 "_bcm05_cf|_bcm24|_bcm40|_bcm38"
#      set bcm21_excl_parents_expr_lvl2 "_bcm07(?!_rs)|_bcm87"
#      set bcm21_excl_parents_expr_lvl3 "_bcm07_atv"
#      foreach_in_collection cell $cell_collection_bcm21 {
#        set cell_name [get_object_name $cell]
#        set inst_name [get_attribute $cell $name_attr]
#        set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
#        set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
#        if { [llength $bcm_hier_to_skip] > 0 } {
#          set bcm_skip 0
#          foreach bcm_skip_inst $bcm_hier_to_skip {
#            if { [regexp "^$bcm_skip_inst" $cell_name] } {
#              set bcm_skip 1
#              break
#            }
#          }
#          if {$bcm_skip == 1} {
#            continue
#          }
#        }
#        if { \
#          [regexp $bcm21_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] || \
#          [regexp $bcm21_excl_parents_expr_lvl2 [getBCMParent $cell_name 2]] || \
#          [regexp $bcm21_excl_parents_expr_lvl3 [getBCMParent $cell_name 3]] \
#        } {
#          continue
#        }
#
#        set clk_dst [getBCMClocks $cell_name "clk_d"]
#        if { [sizeof_collection $clk_dst] == 0 } {
#          # Skip, the clock is probably tied off
#          continue
#        }
#        set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
#        if {$clkPeriod eq ""} {
#          continue
#        }
#
#        set dst_pins ""
#        if { [get_cells -quiet $cell_name/GEN_FST??sample_meta*] != "" } {
#          # No tech cell mapping
#          set dst_pins [get_pins -quiet $cell_name/GEN_FST??sample_meta*/next_state]
#          if { [sizeof_collection $dst_pins] == 0 } {
#            set dst_pins [get_pins $cell_name/GEN_FST??sample_meta*/D]
#          }
#        } elseif { [get_cells -quiet $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
#          # Old way with DWC_SYNCHRONIZER_TECH_MAP
#          set dst_pins [get_pins -quiet $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
#          if { [sizeof_collection $dst_pins] == 0 } {
#            set dst_pins [get_pins $cell_name/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
#          }
#        } elseif { [get_cells -quiet $cell_name/GEN_FST??U_SAMPLE_META_*] != "" } {
#          # New way with cT tech cell mapping
#					echo "I am here"
#          set dst_pins [get_pins $cell_name/GEN_FST??U_SAMPLE_META_*/D]
#					echo "$dst_pins"
#        }
#        if { [sizeof_collection $dst_pins] > 0 } {
#          set dst_pins_name [get_object_name $dst_pins]
#          set clk_from ""
#          set data_s_regs [bcm_all_fanin -to $cell_name/data_s -startpoints_only -only_cells -flat]
#          foreach_in_collection sreg $data_s_regs {
#            append_to_collection -unique clk_from [get_pins -quiet [get_object_name $sreg]/* -filter "is_clock_pin == true"]
#          }
#          if { [sizeof_collection $clk_from] > 0 } {
#            set clk_from_name [get_object_name $clk_from]
#					  echo "I am here2"						
#            lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
#            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
#						echo "$cmd_list_bcm_all"
#          }
#          if {$bcm_constrain_input_ports == 1} {
#            set i_ports [filter_collection [bcm_all_fanin -to $cell_name/data_s -startpoints_only -flat] "object_class == port"]
#            if {[sizeof_collection $i_ports] > 0} {
#              set i_ports_name [get_object_name $i_ports]
#              lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
#              lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
#            }
#          }
#        } else {
#          set f_sync_type [getBCMParamFromNameOrIndex $cell bcm21 F_SYNC_TYPE 1]
#          if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
#            # Nothing to be done when F_SYNC_TYPE is 0
#            bcm_puts "WARNFST0" "Skip constraining $cell_name because F_SYNC_TYPE is set to 0."
#          } else {
#            bcm_puts "WARN" "Unable to find first synchronization flip-flop to destination domain in cell $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
#          }
#        }
#      }
#    }; # end of foreach design
#  }; # end of proc set_cstr_bcm21
#  set_cstr_bcm21
#
#}; # end of namespace BCM (bcm21)
#}

#===============================================================================
# Create Guard for file DWbb_bcm24_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm24_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : DWbb_bcm24_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints


# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# bcm24 set_max_delay | set_min_delay constraints
namespace eval BCM {

  proc set_cstr_bcm24 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable bcm_mod_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    variable design_list

    foreach design $design_list {
      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm24$"] >= 0 } {
        continue
      }
      set cell_collection_bcm24 [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm24.*) AND @ref_name!~.*_bcm24_ap.*"]
      foreach_in_collection cell $cell_collection_bcm24 {
        set cell_name [get_object_name $cell]
        set inst_name [get_attribute $cell $name_attr]
        set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
        set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
        if { [llength $bcm_hier_to_skip] > 0 } {
          set bcm_skip 0
          foreach bcm_skip_inst $bcm_hier_to_skip {
            if { [regexp "^$bcm_skip_inst" $cell_name] } {
              set bcm_skip 1
              break
            }
          }
          if {$bcm_skip == 1} {
            continue
          }
        }

        set clk_from [getBCMClocks $cell_name "clk_s"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPeriod [getBCMClockPeriod $cell_name "clk_s" $clk_from]
        if {$clkPeriod eq ""} {
          continue
        }

        set dst_pins ""
        if { [get_cells -quiet $cell_name/*bin2gray_s_reg*] != "" } {
          if { [get_cells -quiet $cell_name/U_SYNC/GEN_FST??sample_meta*] != "" } {
            # No tech cell mapping
            set dst_pins [get_pins -quiet $cell_name/U_SYNC/GEN_FST??sample_meta*/next_state]
            if { [sizeof_collection $dst_pins] == 0 } {
              set dst_pins [get_pins $cell_name/U_SYNC/GEN_FST??sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_SYNC/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
            # Old way with DWC_SYNCHRONIZER_TECH_MAP
            set dst_pins [get_pins -quiet $cell_name/U_SYNC/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
            if { [sizeof_collection $dst_pins] == 0 } {
              set dst_pins [get_pins $cell_name/U_SYNC/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_SYNC/GEN_FST??U_SAMPLE_META_*] != "" } {
            # New way with cT tech cell mapping
            set dst_pins [get_pins $cell_name/U_SYNC/GEN_FST??U_SAMPLE_META_*/D]
          }
          if { [sizeof_collection $dst_pins] > 0 } {
            set dst_pins_name [get_object_name $dst_pins]
            set clk_from_name [get_object_name $clk_from]
            lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_clocks {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          } else {
            set f_sync_type ""
            set sync_cell [get_cells -quiet $cell_name/U_SYNC]
            if { [sizeof_collection $sync_cell] > 0 } {
              set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
            }
            if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
              # Nothing to be done when F_SYNC_TYPE is 0
              bcm_puts "WARNFST0" "Skip constraining $cell_name because F_SYNC_TYPE of $cell_name/U_SYNC is set to 0."
            } else {
              bcm_puts "WARN" "Unable to find first synchronization flip-flop to destination domain in cell $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
            }
          }
        } else {
          bcm_puts "WARN" "Unable to find source flip-flop in $cell_name"
        }
      }
    }; # end of foreach design
  }; # end of proc set_cstr_bcm24
  set_cstr_bcm24

}; # end of namespace BCM (bcm24)
}

#===============================================================================
# Create Guard for file DWbb_bcm25_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm25_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : DWbb_bcm25_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints


# -----------------------------------------------------------------------------
# [CDC_SYN_03] Define set_max_delay of (Number of Sync stages - 0.5) x destination clock period and set_min_delay of 0 constraints for Qualifier-based Data Bus signals
# BCM25 set_max_delay | set_min_delay constraints
namespace eval BCM {

  proc set_cstr_bcm25 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable bcm_mod_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    variable design_list

    foreach design $design_list {
      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm25$"] >= 0 } {
        continue
      }
      set cell_collection_bcm25 [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND (@ref_name=~.*_bcm25.*) AND @ref_name!~.*_bcm25_atv.* AND @ref_name!~.*_bcm25_c.*"]
      foreach_in_collection cell $cell_collection_bcm25 {
        set cell_name [get_object_name $cell]
        set inst_name [get_attribute $cell $name_attr]
        set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_max)}"
        set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_03_min)}"
        if { [llength $bcm_hier_to_skip] > 0 } {
          set bcm_skip 0
          foreach bcm_skip_inst $bcm_hier_to_skip {
            if { [regexp "^$bcm_skip_inst" $cell_name] } {
              set bcm_skip 1
              break
            }
          }
          if {$bcm_skip == 1} {
            continue
          }
        }

        set clk_from [getBCMClocks $cell_name "clk_s"]
        if { [sizeof_collection $clk_from] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clk_dst [getBCMClocks $cell_name "clk_d"]
        if { [sizeof_collection $clk_dst] == 0 } {
          # Skip, the clock is probably tied off
          continue
        }
        set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
        if {$clkPeriod eq ""} {
          continue
        }

        if { [get_cells -quiet $cell_name/data_d_reg*] != "" } {
          if { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST* ] != "" } {
            set clkPeriodFactor ""
            if { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST1* ] != "" } {
              set clkPeriodFactor 1
            } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST2* ] != "" } {
              set clkPeriodFactor 1.5
            } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST3* ] != "" } {
              set clkPeriodFactor 2.5
            } elseif { [get_cells -quiet $cell_name/U1/U_DW_SYNC_F/GEN_FST4* ] != "" } {
              set clkPeriodFactor 3.5
            } else {
              bcm_puts "WARN" "Unable to find first synchronization flip-flop to destination domain in cell $cell_name"
            }

            foreach_in_collection data_d_reg [get_cells $cell_name/data_d_reg*] {
              set data_d_reg_name [get_object_name $data_d_reg]
              set data_d_pin [get_pins -quiet $data_d_reg_name/next_state]
              if { [sizeof_collection $data_d_pin] == 0 } {
                set data_d_pin [get_pins $data_d_reg_name/D]
              }
              set data_d_pin_name [get_object_name $data_d_pin]
              set clk_from_name [get_object_name $clk_from]
              if { $clkPeriodFactor != "" } {
                set maxdelay [expr $clkPeriodFactor*$clkPeriod]
                lappend cmd_list_bcm_all "set_max_delay $maxdelay -from \[get_clocks {$clk_from_name}\] -to {$data_d_pin_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pin_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
              }
            }
          } else {
            set f_sync_type ""
            set sync_cell [get_cells -quiet $cell_name/U1/U_DW_SYNC_F]
            if { [sizeof_collection $sync_cell] > 0 } {
              set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
            }
            if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
              # Nothing to be done when F_SYNC_TYPE is 0
              bcm_puts "WARNFST0" "Skip constraining $cell_name because F_SYNC_TYPE of $cell_name/U1/U_DW_SYNC_F is set to 0."
            } else {
              bcm_puts "WARN" "Unable to find synchronization flip-flops to destination domain in cell $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
            }
          }
        }
      }
    }; # end of foreach design
  }; # end of proc set_cstr_bcm25
  set_cstr_bcm25

}; # end of namespace BCM (bcm25)
}

#===============================================================================
# Create Guard for file DWbb_bcm36_nhs_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm36_nhs_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : DWbb_bcm36_nhs_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints


# -----------------------------------------------------------------------------
# [CDC_SYN_05] Define "set_false_path -through" constraint for quasi-static signals at the output of the Bus Delay components
# BCM36_NHS set_false_path constraints
namespace eval BCM {

  proc set_cstr_bcm36_nhs {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable bcm_mod_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    variable design_list

    foreach design $design_list {
      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm36_nhs$"] >= 0 } {
        continue
      }
      set cell_collection_bcm36_nhs [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm36_nhs.*"]
      # Parent modules of bcm36_nhs which have their own constraints
      set bcm36_nhs_excl_parents_expr_lvl1 "(_bcm36_(ack|tgl)|_bcm31_p2d_fifomem)"
      foreach_in_collection cell $cell_collection_bcm36_nhs {
        set cell_name [get_object_name $cell]
        set inst_name [get_attribute $cell $name_attr]
        set cmd_cmnt "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_05)}"
        if { [llength $bcm_hier_to_skip] > 0 } {
          set bcm_skip 0
          foreach bcm_skip_inst $bcm_hier_to_skip {
            if { [regexp "^$bcm_skip_inst" $cell_name] } {
              set bcm_skip 1
              break
            }
          }
          if {$bcm_skip == 1} {
            continue
          }
        }
        if { [regexp $bcm36_nhs_excl_parents_expr_lvl1 [getBCMParent $cell_name 1]] } {
          continue
        }
        lappend cmd_list_bcm_all "set_false_path -through \[get_pins $cell_name/data_d*\] $cmd_cmnt"
      }
    }; # end of foreach design
  }; # end of proc set_cstr_bcm36_nhs
  set_cstr_bcm36_nhs

}; # end of namespace BCM (bcm36_nhs)
}

#===============================================================================
# Create Guard for file DWbb_bcm40_cdc_constraints.tcl
#===============================================================================
#set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm40_cdc_constraints__tcl__
#if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
#  set ${sGuardVarName} 1
## -------------------------------------------------------------------------------
## 
## Copyright 2002 - 2024 Synopsys, INC.
## 
## This Synopsys IP and all associated documentation are proprietary to
## Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
## written license agreement with Synopsys, Inc. All other use, reproduction,
## modification, or distribution of the Synopsys IP or the associated
## documentation is strictly prohibited.
## Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
##            Inclusivity and Diversity" (Refer to article 000036315 at
##                        https://solvnetplus.synopsys.com)
## 
## Component Name   : DWC_pcie_ctl
## Component Version: 6.20a
## Release Type     : GA
## Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
## -------------------------------------------------------------------------------
#
#
## Filename    : DWbb_bcm40_cdc_constraints.tcl
## Description : Synthesis CDC Methodology constraints
#
#
## -----------------------------------------------------------------------------
## [CDC_SYN_04] Define set_max_delay of 1 destination clock period and set_min_delay of 0 constraints for all CDC crossings (excluding Gray-coded and Qualifier-based Data Bus signals)
## bcm40 set_max_delay | set_min_delay constraints
#namespace eval BCM {
#
#  proc set_cstr_bcm40 {} {
#    variable ignore_clock_latency_option
#    variable reset_path_option
#    variable bcm_hier_to_skip
#    variable bcm_mod_to_skip
#    variable cmd_list_bcm_all
#    variable bcm_constrain_input_ports
#    variable name_attr
#    variable cmnts_arr
#    variable design_list
#
#    foreach design $design_list {
#      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm40$"] >= 0 } {
#        continue
#      }
#      set cell_collection_bcm40 [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm40.*"]
#      foreach_in_collection cell $cell_collection_bcm40 {
#        set cell_name [get_object_name $cell]
#        set inst_name [get_attribute $cell $name_attr]
#        set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_max)}"
#        set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_04_min)}"
#        if { [llength $bcm_hier_to_skip] > 0 } {
#          set bcm_skip 0
#          foreach bcm_skip_inst $bcm_hier_to_skip {
#            if { [regexp "^$bcm_skip_inst" $cell_name] } {
#              set bcm_skip 1
#              break
#            }
#          }
#          if {$bcm_skip == 1} {
#            continue
#          }
#        }
#
#        set clk_dst [getBCMClocks $cell_name "clk_d"]
#        if { [sizeof_collection $clk_dst] == 0 } {
#          # Skip, the clock is probably tied off
#          continue
#        }
#        set clkPeriod [getBCMClockPeriod $cell_name "clk_d" $clk_dst]
#        if {$clkPeriod eq ""} {
#          continue
#        }
#
#        if { [get_pins -quiet $cell_name/rst_s_n] != "" } {
#          if { [get_cells -quiet $cell_name/U_SYNC/GEN_FST* ] != "" } {
#            set dst_pins [filter_collection [bcm_all_fanout -from $cell_name/rst_s_n -endpoints_only -flat] -regexp {full_name !~ .*\*cell\*\d+.*}]
#            if { [sizeof_collection $dst_pins] > 0 } {
#              set dst_pins_name [get_object_name $dst_pins]
#              set clk_from ""
#              set rst_s_regs [bcm_all_fanin -to $cell_name/rst_s_n -startpoints_only -only_cells -flat]
#              foreach_in_collection sreg $rst_s_regs {
#                append_to_collection -unique clk_from [get_pins -quiet [get_object_name $sreg]/* -filter "is_clock_pin == true"]
#              }
#              if { [sizeof_collection $clk_from] > 0 } {
#                set clk_from_name [get_object_name $clk_from]
#                lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
#                lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_pins {$clk_from_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
#              }
#              if {$bcm_constrain_input_ports == 1} {
#                set i_ports [filter_collection [bcm_all_fanin -to $cell_name/rst_s_n -startpoints_only -flat] "object_class == port"]
#                if {[sizeof_collection $i_ports] > 0} {
#                  set i_ports_name [get_object_name $i_ports]
#                  lappend cmd_list_bcm_all "set_max_delay $clkPeriod -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
#                  lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_ports {$i_ports_name}\] -to {$dst_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
#                }
#              }
#            }
#          }
#        } else {
#          bcm_puts "WARN" "Unable to find rst_s_n pin in cell $cell_name"
#        }
#      }
#    }; # end of foreach design
#  }; # end of proc set_cstr_bcm40
#  set_cstr_bcm40
#
#}; # end of namespace BCM (bcm40)
#}

#===============================================================================
# Create Guard for file DWbb_bcm87_cdc_constraints.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_bcm87_cdc_constraints__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : DWbb_bcm87_cdc_constraints.tcl
# Description : Synthesis CDC Methodology constraints


# -----------------------------------------------------------------------------
# [CDC_SYN_02] Define set_max_delay of 1 source clock period and set_min_delay of 0 constraints for Gray-coded signals
# BCM87 set_max_delay | set_min_delay constraints
namespace eval BCM {

  proc set_cstr_bcm87 {} {
    variable ignore_clock_latency_option
    variable reset_path_option
    variable bcm_hier_to_skip
    variable bcm_mod_to_skip
    variable cmd_list_bcm_all
    variable name_attr
    variable cmnts_arr
    variable design_list

    foreach design $design_list {
      if { [lsearch -regexp $bcm_mod_to_skip "${design}_bcm87$"] >= 0 } {
        continue
      }
      set cell_collection_bcm87 [filter_collection [get_cells -hierarchical *] -regexp "(@ref_name!~.*SNPS_CLOCK_GATE.*) AND @ref_name=~.*_bcm87.*"]
      foreach_in_collection cell $cell_collection_bcm87 {
        set cell_name [get_object_name $cell]
        set inst_name [get_attribute $cell $name_attr]
        set cmd_cmnt_max "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_max)}"
        set cmd_cmnt_min "-comment {Instance $inst_name: $cmnts_arr(CDC_SYN_02_min)}"
        if { [llength $bcm_hier_to_skip] > 0 } {
          set bcm_skip 0
          foreach bcm_skip_inst $bcm_hier_to_skip {
            if { [regexp "^$bcm_skip_inst" $cell_name] } {
              set bcm_skip 1
              break
            }
          }
          if {$bcm_skip == 1} {
            continue
          }
        }

        if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/this_addr_g_int*] != "" } {

          # A "set_max_delay" constraint equivalent to 1 period (or less) of the source clock domain shall be applied in all Gray-coded signals reaching the first synchronization flip-flops in the destination clock domain
          # A "set_min_delay" constraint with value 0 shall be applied to the same paths
          # Source clock_push: Gray Address to be sync into clock_pop domain
          set clk_from [getBCMClocks $cell_name "clk_push"]
          if { [sizeof_collection $clk_from] == 0 } {
            # Skip, the clock is probably tied off
            continue
          }
          set clkPushPeriod [getBCMClockPeriod $cell_name "clk_push" $clk_from]
          if {$clkPushPeriod eq ""} {
            continue
          }
          set data_d_pins ""
          if { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
            # No tech cell mapping
            set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
            if { [sizeof_collection $data_d_pins] == 0 } {
              set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
            # Old way with DWC_SYNCHRONIZER_TECH_MAP
            set data_d_pins [get_pins -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
            if { [sizeof_collection $data_d_pins] == 0 } {
              set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
            # New way with cT tech cell mapping
            set data_d_pins [get_pins $cell_name/U_POP_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
          }
          if { [sizeof_collection $data_d_pins] > 0 } {
            set clk_from_name [get_object_name $clk_from]
            set data_d_pins_name [get_object_name $data_d_pins]
            lappend cmd_list_bcm_all "set_max_delay $clkPushPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          } else {
            set f_sync_type ""
            set sync_cell [get_cells -quiet $cell_name/U_POP_FIFOFCTL/U_sync]
            if { [sizeof_collection $sync_cell] > 0 } {
              set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
            }
            if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
              # Nothing to be done when F_SYNC_TYPE is 0
              bcm_puts "WARNFST0" "Skip constraining from PUSH to POP in $cell_name because F_SYNC_TYPE of $cell_name/U_POP_FIFOFCTL/U_sync is set to 0."
            } else {
              bcm_puts "WARN" "Unable to find first synchronization flip-flop from PUSH domain to POP domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
            }
          }

          # Source clock_pop: Gray Address to be sync into clock_push domain
          set clk_from [getBCMClocks $cell_name "clk_pop"]
          if { [sizeof_collection $clk_from] == 0 } {
            # Skip, the clock is probably tied off
            continue
          }
          set clkPopPeriod [getBCMClockPeriod $cell_name "clk_pop" $clk_from]
          if {$clkPopPeriod eq ""} {
            continue
          }
          set data_d_pins ""
          if { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*] != "" } {
            # No tech cell mapping
            set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/next_state]
            if { [sizeof_collection $data_d_pins] == 0 } {
              set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*] != "" } {
            # Old way with DWC_SYNCHRONIZER_TECH_MAP
            set data_d_pins [get_pins -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/next_state]
            if { [sizeof_collection $data_d_pins] == 0 } {
              set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/sample_meta*/D]
            }
          } elseif { [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*] != "" } {
            # New way with cT tech cell mapping
            set data_d_pins [get_pins $cell_name/U_PUSH_FIFOFCTL/U_sync/GEN_FST??U_SAMPLE_META_*/D]
          }
          if { [sizeof_collection $data_d_pins] > 0 } {
            set clk_from_name [get_object_name $clk_from]
            set data_d_pins_name [get_object_name $data_d_pins]
            lappend cmd_list_bcm_all "set_max_delay $clkPopPeriod -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_max"
            lappend cmd_list_bcm_all "set_min_delay 0.0 -from \[get_clocks {$clk_from_name}\] -to {$data_d_pins_name} $ignore_clock_latency_option $reset_path_option $cmd_cmnt_min"
          } else {
            set f_sync_type ""
            set sync_cell [get_cells -quiet $cell_name/U_PUSH_FIFOFCTL/U_sync]
            if { [sizeof_collection $sync_cell] > 0 } {
              set f_sync_type [getBCMParamFromNameOrIndex $sync_cell bcm21 F_SYNC_TYPE 1]
            }
            if { [string is digit -strict $f_sync_type] && ([expr $f_sync_type % 8] == 0) } {
              # Nothing to be done when F_SYNC_TYPE is 0
              bcm_puts "WARNFST0" "Skip constraining from POP to PUSH in $cell_name because F_SYNC_TYPE of $cell_name/U_PUSH_FIFOFCTL/U_sync is set to 0."
            } else {
              bcm_puts "WARN" "Unable to find first synchronization flip-flop from POP domain to PUSH domain in $cell_name. This warning can be ignored if F_SYNC_TYPE of $cell_name is intentionally set to 0."
            }
          }
        } else {
          bcm_puts "WARN" "Unable to find address register in $cell_name"
        }
      }
    }; # end of foreach design
  }; # end of proc set_cstr_bcm87
  set_cstr_bcm87

}; # end of namespace BCM (bcm87)
}

# -------------------------------------------------------------------------------
# 
# Copyright 2002 - 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_pcie_ctl
# Component Version: 6.20a
# Release Type     : GA
# Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
# -------------------------------------------------------------------------------


# Filename    : common_end.tcl
# Description : Common procs which will be exectued at the end


namespace eval BCM {
  variable cmd
  if { [llength $cmd_list_bcm_all] > 0 } {
    foreach cmd $cmd_list_bcm_all {
      runCmd $cmd
    }
  } else {
    bcm_puts "INFO" "No BCM CDC constraints are applied."
  }

  unalias bcm_all_fanin
  unalias bcm_all_fanout
}


#===============================================================================
# Create Guard for file DWC_pcie_ctl.elab.exceptions.tcl
#===============================================================================
set sGuardVarName ::__snps_guard__ep_x4_DWC_pcie_ctl_DWC_pcie_ctlelabexceptions__tcl__
if {![info exists $sGuardVarName] || ![expr $${sGuardVarName}]} {
  set ${sGuardVarName} 1
# -----------------------------------------------------------------------------
# Define set_max|min_delay for RAM Flip-Flop based - DWC_pcie_ctl is not using BCM
# DWC_pcie_mem_dff set_max_delay/set_min_delay constraints
set maxmin_delay_cmds ""
#set core_clk_grp {core_clk_axi_g cdm_clk_g aux_clk aux_clk_g aux_clk_g_virt aux_clk_virt core_clk core_clk_ug core_clk_ug_virt core_clk_virt radm_clk_g radm_clk_g_virt}
#set mstr_clk_grp {mstr_aclk mstr_aclk_virt}
#set slv_clk_grp  {slv_aclk slv_aclk_virt}
#set dbi_clk_grp  {dbi_aclk dbi_aclk_virt}
#set lti_clk_grp  {lti_clk lti_clk_virt}
set maxmin_delay_cmds ""
set core_clk_grp [get_object_name [get_clocks -quiet core_clk*]]
set mstr_clk_grp [get_object_name [get_clocks -quiet mstr_aclk*]]
set slv_clk_grp  [get_object_name [get_clocks -quiet slv_aclk*]]
set dbi_clk_grp  [get_object_name [get_clocks -quiet dbi_aclk*]]
set ref_clk_grp  [get_object_name [get_clocks -quiet [list i_ref_clk ref_clk_virt]]]

append_to_collection cell_collection_mem_dff [filter_collection [get_cells -hierarchical *] -regexp {@ref_name=~.*DWC_pcie_mem_dff.*}]

foreach_in_collection cell $cell_collection_mem_dff {
  set cell_name [get_object_name $cell]

  foreach_in_collection mem_dff_out [get_pins  $cell_name/* -filter "direction==out"] {
    foreach_in_collection dest [get_pins [all_fanout -endpoints_only -flat -from [get_nets [get_object_name $mem_dff_out]]]] {

      set dest_clk [get_clocks [get_attribute [get_pins -of_object [get_cells -of_object [get_object_name $dest]] -filter "@is_clock_pin==true"] clocks]]
      set clk_period [get_attribute $dest_clk period]

      # When we have more than one clock, only the min period to apply set_max_delay
      set min_period 10
      foreach_in_collection a $dest_clk {
        set b [get_attribute $a period]
        if {$b < $min_period} {
          set clk_period $b
          #set min_clk_name [get_attribute $a name]
        }
      }

      foreach_in_collection source [get_pins [all_fanin -startpoints_only -flat -to [get_nets [get_object_name $mem_dff_out]]]] {

        set source_clk [get_clocks [get_attribute [get_pins $source -filter "@is_clock_pin==true"] clocks]]
        set source_clk_name [get_object_name $source_clk]
        set dest_clk_name [get_object_name $dest_clk]

        if {([lsearch -regexp $core_clk_grp $source_clk_name] >= 0 && [lsearch -regexp $core_clk_grp $dest_clk_name] <  0) || \
            ([lsearch -regexp $core_clk_grp $source_clk_name] <  0 && [lsearch -regexp $core_clk_grp $dest_clk_name] >= 0) || \
            ([lsearch -regexp $mstr_clk_grp $source_clk_name] >= 0 && [lsearch -regexp $mstr_clk_grp $dest_clk_name] <  0) || \
            ([lsearch -regexp $mstr_clk_grp $source_clk_name] <  0 && [lsearch -regexp $mstr_clk_grp $dest_clk_name] >= 0) || \
            ([lsearch -regexp $slv_clk_grp $source_clk_name]  >= 0 && [lsearch -regexp $slv_clk_grp  $dest_clk_name] <  0) || \
            ([lsearch -regexp $slv_clk_grp $source_clk_name]  <  0 && [lsearch -regexp $slv_clk_grp  $dest_clk_name] >= 0) || \
            ([lsearch -regexp $dbi_clk_grp $source_clk_name]  >= 0 && [lsearch -regexp $dbi_clk_grp  $dest_clk_name] <  0) || \
            ([lsearch -regexp $dbi_clk_grp $source_clk_name]  <  0 && [lsearch -regexp $dbi_clk_grp  $dest_clk_name] >= 0) || \
            ([lsearch -regexp $ref_clk_grp $source_clk_name]  >= 0 && [lsearch -regexp $ref_clk_grp $dest_clk_name] <  0) || \
            ([lsearch -regexp $ref_clk_grp $source_clk_name]  <  0 && [lsearch -regexp $ref_clk_grp $dest_clk_name] >= 0)
 } { 

              if {[get_object_name $source_clk] != "" && [get_object_name $dest_clk] != "" } {
                if {[get_object_name $source_clk] != [get_object_name $dest_clk]} {
                  set sourceff [get_object_name $source]
                  regsub -all {\[} $sourceff {\\[} sourceff
                  regsub -all {\]} $sourceff {\\]} sourceff

                  set destff [get_object_name $dest]
                  regsub -all {\[} $destff {\\[} destff
                  regsub -all {\]} $destff {\\]} destff
                  set maxmin_delay_cmds [format "${maxmin_delay_cmds}set_max_delay $clk_period -from $sourceff -to $destff -ignore_clock_latency\n"]
                  set maxmin_delay_cmds [format "${maxmin_delay_cmds}set_min_delay 0.0 -from $sourceff -to $destff -ignore_clock_latency\n"]
            }
          }
        }
      }
    }
  }
}
eval $maxmin_delay_cmds

}


