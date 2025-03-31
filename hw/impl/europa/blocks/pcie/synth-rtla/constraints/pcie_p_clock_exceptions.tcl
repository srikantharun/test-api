############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_clock_exceptions.tcl
#
# PIPE(UPCS+PHY) synthesis all clock related exceptions
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

###################################################################
##    Clock Grouping
###################################################################

if { !$remove_upcs_scan_constraints } {
 # when scan shift clock is created on scan_clk pin
 set_clock_groups -logically_exclusive \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_scanLE1_relation_between_scan_asst_and_shift_clocks" \
     -group [get_clocks $ip_all_shift_clks] \
     -group [get_clocks $ip_all_asst_clks]

 set_clock_groups -logically_exclusive \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_scanLE2_relation_between_scan_clocks_and_functional_clocks_without_embedded_asst_clock" \
     -group [remove_from_collection $scan_clocks_all $ip_all_asst_clks_on_func_ports] \
     -group [remove_from_collection $ip_all_func_clocks $ip_all_func_clocks_with_embedded_asst_clks]

 set_clock_groups -physically_exclusive \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_scanPE1_relation_between_scan_clocks_and_functional_clocks_with_embedded_asst_clock" \
     -group [get_clocks $ip_all_asst_clks_on_func_ports] \
     -group [get_clocks $ip_all_func_clocks_with_embedded_asst_clks]

 set_clock_groups -logically_exclusive \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_scanLE3_relation_between_scan_shift_clocks_and_functional_clocks_with_embedded_asst_clock" \
     -group [get_clocks $ip_all_shift_clks] \
     -group [get_clocks $ip_all_func_clocks_with_embedded_asst_clks]

 set_clock_groups -asynchronous \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_scan_ASYNC_relation_between_scan_ASST_clocks_and_functional_clocks_with_embedded_asst_clock" \
     -group [remove_from_collection $ip_all_asst_clks $ip_all_asst_clks_on_func_ports] \
     -group [get_clocks $ip_all_func_clocks_with_embedded_asst_clks]

 foreach_in_collection scan_clk $ip_all_asst_clks {
  set clk_obj [get_object_name $scan_clk]
  puts "\[Constraints Debug\] Info: [file tail [info script]] 0 asynchronous clock group for scan clock $clk_obj with all other clocks "
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC0_SCAN_ASST_$clk_obj" \
      -group [get_clocks $clk_obj] \
      -group [remove_from_collection $scan_clocks_all [get_clocks $scan_clk]]
 }

 # # Scan shift clocks - Asynchronous to all other clocks
 # set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC0_SCAN_SHIFT_CLK" \
     #    -group $ip_all_shift_clks \
     #    -group [remove_from_collection $all_clocks_collection $ip_all_shift_clks]


}
# PCIe Clock Grouping
if {$pcie_supported} {
 for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
  foreach lane $pcs_lanes($link_num) {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 1 clock groups for pcie4 pipe link $link_num and clock controller $lane"
   if { !$serdes_mode } {
    # Clocks at OR gate of GLCM-1 and their derivatives clocks are defined physically exclusive
    # MPLL/PCS/PMA/MAXPCLK/PCLK for g12 are defined exclusive with g34 created at same pins
    set_clock_groups -physically_exclusive \
        -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE1_clock_relation_among_pcie_g12_and_g34_clks_lane${lane}" \
        -group [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g12_div2_flop_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g12_div2_flop_phy$clksrc($link_num)] \
                                $pcs_lane_pcie_g12_pclks_(${lane})]] \
        -group [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div1_icg_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div1_icg_phy$clksrc($link_num) \
                                        ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)] \
                                $pcs_lane_pcie_g34_pclks_(${lane})]]
    if { !$remove_upcs_scan_constraints } {
     # Generated PMA clocks created on flop in PMA divider defined physical exclusive with each other
     set_clock_groups -physically_exclusive \
         -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE2_clock_relation_among_pma_clk_divider_flop_clks_lane${lane}" \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g12_div2_flop_phy$clksrc($link_num)] \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num)] \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_scan_shift_clk]

     # Generated PMA clocks created on flop and ICG in PMA divider defined logically exclusive with each other as there are no paths between them
     set_clock_groups -logically_exclusive \
         -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE1_clock_relation_among_pma_clk_divider_icg_n_flop_clks_lane${lane}" \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div1_icg_phy$clksrc($link_num)] \
         -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num) \
                                 ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_scan_shift_clk]]

     # Generated PCS clocks created on flop in PCS divider defined physical exclusive with each other
     set_clock_groups -physically_exclusive \
         -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE3_clock_relation_among_pcs_clk_divider_flop_clks_lane${lane}" \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g12_div2_flop_phy$clksrc($link_num)] \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)] \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_scan_shift_clk]

     # Generated PCS clocks created on flop and ICG in PCS divider defined logically exclusive with each other as there are no paths between them
     set_clock_groups -logically_exclusive \
         -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE2_clock_relation_among_pcs_clk_divider_icg_n_flop_clks_lane${lane}" \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div1_icg_phy$clksrc($link_num)] \
         -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num) \
                                 ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_scan_shift_clk]]

    } else {  ;#Functional only constraints
     # Generated PMA clocks created on flop in PMA divider defined physical exclusive with each other
     set_clock_groups -physically_exclusive \
                  -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE2_clock_relation_among_pma_clk_divider_flop_clks_lane${lane}" \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g12_div2_flop_phy$clksrc($link_num)] \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num)]

     # Generated PMA clocks created on flop and ICG in PMA divider defined logically exclusive with each other as there are no paths between them
     set_clock_groups -logically_exclusive \
                  -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE1_clock_relation_among_pma_clk_divider_icg_n_flop_clks_lane${lane}" \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div1_icg_phy$clksrc($link_num)] \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pma_clk_g34_div2_flop_phy$clksrc($link_num)]

     # Generated PCS clocks created on flop in PCS divider defined physical exclusive with each other
     set_clock_groups -physically_exclusive \
                  -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE3_clock_relation_among_pcs_clk_divider_flop_clks_lane${lane}" \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g12_div2_flop_phy$clksrc($link_num)] \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)]

     # Generated PCS clocks created on flop and ICG in PCS divider defined logically exclusive with each other as there are no paths between them
     set_clock_groups -logically_exclusive \
                  -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE2_clock_relation_among_pcs_clk_divider_icg_n_flop_clks_lane${lane}" \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div1_icg_phy$clksrc($link_num)] \
                  -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pcs_clk_g34_div2_flop_phy$clksrc($link_num)]
    }
   } else {  ;#serdes arch works with pclk as phy input clocking

    # MPLL/MaxPclk/PCLk for g12 are defined exclusive with g34 created at same pins
    set_clock_groups -physically_exclusive \
                 -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE1_clock_relation_among_pcie_g12_and_g34_clks_lane${lane}" \
                 -group [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g12_phy$clksrc($link_num)] \
                                         $pcs_lane_pcie_g12_pclks_(${lane})]] \
                 -group [get_clocks [concat [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_mpll_pcie_g34_phy$clksrc($link_num)] \
                                         $pcs_lane_pcie_g34_pclks_(${lane})]]

   } ;#end of non-serdes mode condition



   # Generated PCLK created on ICG in PCLK divider defined physical exclusive with each other
   set_clock_groups -physically_exclusive \
       -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE4_clock_relation_among_${pclk_out_name}_divider_icg_clks_lane${lane}" \
       -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_div1_icg_phy$clksrc($link_num)] \
       -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_div1_icg_phy$clksrc($link_num)]

   if { !$remove_upcs_scan_constraints } {
    # Generated PCLK created on flop in PCLK divider defined physical exclusive with each other
    set_clock_groups -physically_exclusive \
        -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE5_clock_relation_among_${pclk_out_name}_divider_flop_clks_link${link_num}_lane${lane}" \
        -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_nondiv1_flop_phy$clksrc($link_num)] \
        -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_nondiv1_flop_phy$clksrc($link_num)] \
        -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_scan_shift_clk]

    # Generated PCLK created on flop and ICG in PCLK divider defined logically exclusive with each other as there are no paths between them
    set_clock_groups -logically_exclusive \
        -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE3_clock_relation_among_${pclk_out_name}_divider_icg_n_flop_clks_lane${lane}" \
        -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_div1_icg_phy$clksrc($link_num) \
                                ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_div1_icg_phy$clksrc($link_num)]] \
        -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_nondiv1_flop_phy$clksrc($link_num) \
                                ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_nondiv1_flop_phy$clksrc($link_num) \
                                ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_scan_shift_clk]]
   } else {  ;#Functional only constraints
    # Generated PCLK created on flop in PCLK divider defined physical exclusive with each other
    set_clock_groups -physically_exclusive \
                 -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE5_clock_relation_among_${pclk_out_name}_divider_flop_clks_link${link_num}_lane${lane}" \
                 -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_nondiv1_flop_phy$clksrc($link_num)] \
                 -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_nondiv1_flop_phy$clksrc($link_num)]

    # Generated PCLK created on flop and ICG in PCLK divider defined logically exclusive with each other as there are no paths between them
    set_clock_groups -logically_exclusive \
                 -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE3_clock_relation_among_${pclk_out_name}_divider_icg_n_flop_clks_lane${lane}" \
                 -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_div1_icg_phy$clksrc($link_num) \
                                         ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_div1_icg_phy$clksrc($link_num)]] \
                 -group [get_clocks [list ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g34_nondiv1_flop_phy$clksrc($link_num) \
                                         ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_${pclk_out_name}_g12_nondiv1_flop_phy$clksrc($link_num)]]
   }


   if { !($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions)) } {
    if { $pclk_as_phy_input } {
     # Input PCLKs created at pclk port defined physical exclusive with each other
     if { !$remove_upcs_scan_constraints } {
      set_clock_groups -physically_exclusive \
          -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE6_clock_relation_among_pcie_g12_and_g34_in_pclk_lane${lane}" \
          -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g12_phy$clksrc($link_num)] \
          -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g34_phy$clksrc($link_num)] \
          -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_refclk] \
          -group [get_clocks ${SNPS_CLOCK_PREFIX}pcs_scan_lane${lane}_in_pclk]
     } else {  ;#Functional only constraints
      set_clock_groups -physically_exclusive \
                   -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIEPE6_clock_relation_among_pcie_g12_and_g34_in_pclk_lane${lane}" \
                   -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g12_phy$clksrc($link_num)] \
                   -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_pcie_g34_phy$clksrc($link_num)] \
                   -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_refclk]
     }

     # pclk refclk created for PCIE is defined as async to all other clocks
     set_clock_groups -asynchronous \
         -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIE_ASYNC_lane${lane}_pclk_refclk_with_others" \
         -group [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_refclk] \
         -group [remove_from_collection $all_clocks_collection [get_clocks ${SNPS_CLOCK_PREFIX}link${link_num}_lane${lane}_pclk_refclk]]

    }
   } ;#end of not of integration

  }
 }

 #JIRA P80001562-347244 : Inter-link clocks defined as logically exclusive to avoid unrealistic timing path between them in case of per-link clocking architecture
 if { $perlink_clk_arch } {
  if {$pipe_nlinks == "2"} {
   set_clock_groups -logically_exclusive \
       -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE4_btwn_link0_link1_clks" \
       -group [get_clocks *link0_*] \
       -group [get_clocks *link1_*]
  }
  if {$pipe_nlinks == "4"} {
   set_clock_groups -logically_exclusive \
       -name "${SNPS_CLOCK_PREFIX}snps_cg_PCIELE5_btwn_link0_link1_link2_link3_clks" \
       -group [get_clocks *link0_*] \
       -group [get_clocks *link1_*] \
       -group [get_clocks *link2_*] \
       -group [get_clocks *link3_*]
  }
 }
} ;#end of protocol condition

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 2 clock groups for phy $phy"
 #TCA appends related functional ref clocks in the array
 set_clock_groups -physically_exclusive \
     -name "${SNPS_CLOCK_PREFIX}snps_cg_COMPE1_ref_ana_clk_occ_and_functional_clocks_phy${phy}" \
     -group [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_fr_clk]] \
     -group [remove_from_collection $all_ref_clocks_($phy) [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i ${SNPS_CLOCK_PREFIX}phy${phy}_ref_dig_fr_clk]] ]

 foreach rxlane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 3 clock groups for rx $rxlane of phy $phy "
  if { $usb4_supported} {
   # Variants of Rx clocks for serdes and non-serdes modes are defined physical exclusive with each other
   # As one type of clocks would be present at a time in the design
   set_clock_groups -physically_exclusive \
       -name "${SNPS_CLOCK_PREFIX}snps_cg_USBPE1_rx_clocks_${rxlane}" \
       -group  [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_ana_dword_clk_i_nonsds ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_dig_?word_clk_nonsds ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_?wclk_nonsds]] \
       -group  [get_clocks [list ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_ana_dword_clk_i_sds ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_dig_?word_clk_sds ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_asic_?wclk_sds]]
  }
 }
}


for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 5 asynchronous clock groups for phy $phy "
 if { !$sync_apb0_fw } {
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC1_FW_CLK_${phy}" \
      -group $all_fw_clocks_($phy) \
      -group [remove_from_collection $all_clocks_collection $all_fw_clocks_($phy)]
 }
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC2_APB0_CLK_${phy}" \
     -group $all_apb0_clocks_($phy) \
     -group [remove_from_collection [remove_from_collection $all_clocks_collection $all_apb0_clocks_($phy)] $ip_all_core_clks] 
# set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC3_APB1_CLK_${phy}" \
     -group $all_apb1_clocks_($phy) \
     -group [remove_from_collection $all_clocks_collection $all_apb1_clocks_($phy)]
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC4_FUNC_JTAG_CLK_${phy}" \
     -group $all_func_jtag_($phy)  \
     -group [remove_from_collection $all_clocks_collection $all_func_jtag_($phy)]
# set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC5_BS_CDR_CLK_${phy}" \
     -group $all_bs_cdr_($phy) \
     -group [remove_from_collection $all_clocks_collection $all_bs_cdr_($phy)]
# set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC6_BS_UDR_CLK_${phy}" \
     -group $all_bs_udr_($phy) \
     -group [remove_from_collection $all_clocks_collection $all_bs_udr_($phy)]
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC7_REF_CLK_${phy}" \
     -group $all_ref_clocks_(${phy}) \
     -group [remove_from_collection $all_clocks_collection $all_ref_clocks_($phy)]
 #to manage per phy grouping for mpll clocks
 ##mplla/mpllb_div_clk group
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC8_MPLLA_DIV_CLK_${phy}" \
     -group $all_mplla_div_clocks_(${phy}) \
     -group [remove_from_collection $all_clocks_collection $all_mplla_div_clocks_($phy)]
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC9_MPLLB_DIV_CLK_${phy}" \
     -group $all_mpllb_div_clocks_(${phy}) \
     -group [remove_from_collection $all_clocks_collection $all_mpllb_div_clocks_($phy)]

 ##mplla/b_word_clk_group
 if { ( ( $usb3_supported || $tx_only_supported ) && $dwc_dpalt_phy) || $pcie_supported } {
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC10_MPLLB_WORD_CLK_${phy}" \
      -group [remove_from_collection $all_mpllb_word_clocks_(${phy}) $ip_all_core_clks] \
      -group [remove_from_collection $all_clocks_collection $all_mpllb_word_clocks_($phy)]
#F	
	set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC10_CORE12_CLK_${phy}" \
      -group [get_clocks *core_clk_g12*] \
      -group [remove_from_collection [remove_from_collection $all_clocks_collection $all_mpllb_word_clocks_($phy)] $all_apb0_clocks_($phy)]	
 }
 if { ($usb3_supported && !$dwc_dpalt_phy) || ($pcie_supported && $serdes_mode) || ($tx_only_supported && $dwc_dpalt_phy) } {
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC11_CORE_CLK34_${phy}" \
      -group [get_clocks *core_clk_g34*] \
      -group [remove_from_collection [remove_from_collection $all_clocks_collection $all_mplla_word_clocks_($phy)] $all_apb0_clocks_($phy)]
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC11_MPLLA_WORD_CLK_${phy}" \
      -group [remove_from_collection $all_mplla_word_clocks_(${phy}) $ip_all_core_clks]\
      -group [remove_from_collection $all_clocks_collection $all_mplla_word_clocks_($phy)] 	
 }

 ##mplla_div16p5_clk group
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC12_MPLLA_DIV16P5_CLK_${phy}" \
     -group $all_mplla_div16p5_clocks_(${phy}) \
     -group [remove_from_collection $all_clocks_collection $all_mplla_div16p5_clocks_($phy)]

 ##mpllb_hdmi div_clk group
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC13_MPLLB_HDMI_DIV_CLK_${phy}" \
     -group $all_mpllb_hdmi_div_clocks_(${phy}) \
     -group [remove_from_collection $all_clocks_collection $all_mpllb_hdmi_div_clocks_($phy)]

 # Tx ana clocks are defined asynchronous to all other clocks in the design
 foreach txlane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 6 asynchronous clock groups for tx $txlane of phy $phy "
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC14_TX${txlane}_ANA_WORD_CLK_${phy}" \
      -group [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx${txlane}_ana_word_clk_i] \
      -group [remove_from_collection $all_clocks_collection [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_tx${txlane}_ana_word_clk_i]]
 }
 foreach rxlane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 7 asynchronous clock groups for rx $rxlane of phy $phy "
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC15_RX${rxlane}_ANA_DIV16P5_CLK_${phy}" \
      -group [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_ana_div16p5_clk_i] \
      -group [remove_from_collection $all_clocks_collection [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_rx${rxlane}_ana_div16p5_clk_i]]
 }
}




## Estore is not used in pcie serdes mode
if { ($pcie_supported && $serdes_mode) || ($tx_only_supported && $dwc_dpalt_phy) } {
 for {set x 0} {$x < $num_rx} {incr x} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 9 asynchronous clock group for rx number $x with all other clocks "
  set_clock_groups -asynchronous  -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC21_rx_clk${x}_obj_with_others" \
      -group $rx_clks($x) \
      -group [remove_from_collection $all_clocks_collection $rx_clks($x)]
 }
}


####Estore Constraints
if { $usb3_supported ||  ($pcie_supported && !$serdes_mode)  } {
 ########################################################################################################
 # Max delay constraints for estore data paths
 # Constraints to limit max delay constraints for estore data paths for CDC async data transfers
 # 1. It involves defining Tx/PCS of USB3_G2 and Rx clock group definitions with -allow_paths between them to enable
 #    timing paths between the clock groups for max_delay constraint for cdc paths in estore
 #    a. NOTE - rx_clks are created considering highest data rate supported for USB3 protocol i.e G2(10G)
 # 2. With set_false_path, unintended timing between rx_clks and tx_clks and vice versa are suppressed
 #    e.x - a. phy0/${pma_inst_name}/rxX_asic_wclk      <->  laneX_[pcs|pma|pclk]_clk_usb_g2
 #    e.x - b. phy0/${pma_inst_name}/rxX_asic_dwclk_sds <->  laneX_[pcs|pma|pclk]_clk_usb_g2
 ########################################################################################################

 # A + B + C + D with rest
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC22_ALL_ESTORE_CLKS_WITH_OTHERS" \
     -group [remove_from_collection $all_tx_rx_estore_clks $ip_all_core_clks]\
     -group [remove_from_collection $all_clocks_collection $all_tx_rx_estore_clks]

#F
 set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC22_ALL_ESTORE_CLKS_WITH_OTHERS_CORE" \
     -group [get_clocks core_clk_g34]\
     -group [remove_from_collection [remove_from_collection $all_clocks_collection $all_tx_rx_estore_clks] $all_apb0_clocks_(0)]

 # (A + C) and (B + D) - allow paths
 for {set x 0} {$x < $num_rx} {incr x} {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 10 asynchronous clock group with allow paths for rx number $x with all other estore read side clocks"
  # phy_rxX_asic_dwclk_nonsds is defined async with usb3-g2 pcs/${pma_inst_name}/pclk with allow_paths which allows the tool to do the timing analysis between these clocks
  set_clock_groups -asynchronous -allow_paths \
      -name "${SNPS_CLOCK_PREFIX}snps_cg_Async23_Allow_paths_between_tx_and_rx${x}_clks" \
      -group $all_estore_related_mpll_rd_clks \
      -group $rx_clks($x)
 }

 # Asynchronous clock groups are created between rx clocks of inter lanes with -allow_paths for tool to do pessimistic crosstalk analysis.
 # Grouping is done in this to ensure crosstalk is done between inter lane RX clocks as async,
 # Using false_path timing is supressed as paths between inter lane clocks are not valid
 # To handle GCA error CGR-0004 which would come otherwise
 for {set x 0} {$x < $num_rx} {incr x} {
  for {set y [expr {$x+1}]} {$y < $num_rx} {incr y} {
   puts "\[Constraints Debug\] Info: [file tail [info script]] 11 asynchronous clock group for rx number $x with rx number $y"
   set_clock_groups -asynchronous \
       -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC24_rx${x}_and_rx${y}_clks" \
       -group $rx_clks($x) \
       -group $rx_clks($y)
  }
 }

 #A+C to B+D
 # False Path from all txclks to all rxclks
 set_false_path -from  $all_estore_related_mpll_rd_clks -to  $all_estore_related_rx_wr_clks

 #B to A+C
 # False path from rxclks except rx?_asic_dwclk rxclk to all usb3-g2/pcie-g34 txclks
 set_false_path -from  $rx_estore_wr_clks_rest   -to  $all_estore_related_mpll_rd_clks

 #D to A
 # False path from rx_asic_dwclk to all non-pcs clocks
 set_false_path -from  $upcs_rx_estore_wr_clk    -to  $tx_mpll_estore_rd_clks_rest

 # Avoid min timing analysis between rxX_dwclk_nonsds clock and lane*_pcs_clk
 set_false_path -hold -from $upcs_rx_estore_wr_clk -to $upcs_mpll_estore_rd_clk
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 foreach rxlane $phy_rx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 12 clock group for rx $rxlane of phy $phy"
  #TCM sees physically seperate paths inside pma and flags these violations
  if { $usb4_supported } {
   # RX clocks are defined logical exclusive with each other to ignore the false timing btween rxX_asic_wclk, rxX_asic_dwclk, rxX_asic_qwclk as these clocks propagate from pma pin(rxX_clk) to higher level blocks
   set cg_cmd_rx_phy_upcs_clk  ""
   set cg_cmd_rx_phy_upcs_clk "set_clock_groups -physically_exclusive  -name \"${SNPS_CLOCK_PREFIX}snps_cg_USBPE8_RX_ASIC_SDS_CLKs_${phy}_rx${rxlane}\" \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_wclk\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_dwclk_sds\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_qwclk_sds\]\]"
   if { $PMA_NAME == "c40" } {
    set cg_cmd_rx_phy_upcs_clk "$cg_cmd_rx_phy_upcs_clk \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_owclk_sds\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_div28clk\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_div56clk\]\]"

   }
   eval  $cg_cmd_rx_phy_upcs_clk

  }
  if { $usb3_supported } {
   set cg_cmd_rx_phy_upcs_clk_1  ""
   set cg_cmd_rx_phy_upcs_clk_1 "set_clock_groups -physically_exclusive  -name \"${SNPS_CLOCK_PREFIX}snps_cg_USBPE9_RX_ASIC_NONSDS_CLKs_${phy}_rx${rxlane}\" \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_wclk\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_dwclk_nonsds\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_qwclk_nonsds\]\]"
   if { $PMA_NAME == "c40" } {
    set cg_cmd_rx_phy_upcs_clk_1 "$cg_cmd_rx_phy_upcs_clk_1 \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_owclk_sds\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_div28clk\]\] \
        -group  \[get_clocks \[list *phy${phy}_rx${rxlane}_asic_div56clk\]\]"

   }
   eval  $cg_cmd_rx_phy_upcs_clk_1
  }
  if { $tx_only_supported || $pcie_supported } {

   set_clock_groups -physically_exclusive -name "${SNPS_CLOCK_PREFIX}snps_cg_COMPE_RX_ASIC_CLKs_${phy}_rx${rxlane}" \
       -group  [get_clocks [list *phy${phy}_rx${rxlane}_asic_wclk]] \
       -group  [get_clocks [list *phy${phy}_rx${rxlane}_asic_dwclk]] \
       -group  [get_clocks [list *phy${phy}_rx${rxlane}_asic_qwclk]]
  } ;#End of dp_hdmi/pcie

 }
 puts "\[Constraints Debug\] Info: [file tail [info script]] 13 clock group for mphy clocks of phy $phy"
 if { $jtag_mphy_support && !$dwc_dpalt_phy } {
  set_clock_groups -asynchronous -name "${SNPS_CLOCK_PREFIX}snps_cg_ASYNC25_MPHY_CLKs_${phy}" \
      -group $all_mphy_clocks_($phy) \
      -group [remove_from_collection $all_clocks_collection $all_mphy_clocks_($phy)]
 }

}

## Mplla root master clocks and its derivatives clocks are defined asynchronous with the other clocks in the design for Display only design
## Below clock grouping is to define the relation between derivative clocks,of different modes such as dp20_a, usb3_gen2, usb4, who share same root master clock i.e mplla_ana_word_clk
## "lane*_mpll_*" clocks can coexist at GLCM outputs, therfore, group is defined as logical exclusive
## It also covers inter-lane timing paths
## logically Exclusive b/w USB3 Gen2 and USB4 clocks to avoid tool to do timing b/w these two clock groups neither within same lane nor inter-lanes
set cg_cmd_mplla_gen_clks ""
set cg_cmd_mplla_gen_clks "set_clock_groups -logically_exclusive -name  \"${SNPS_CLOCK_PREFIX}snps_cg_USBLE3_Clock_relation_between_generated_mplla_variant_clks\""
if {($usb4_supported || ($usb3_supported && $dp20_supported)) && $dwc_dpalt_phy } {
 if {$dp20_supported} {
  set cg_cmd_mplla_gen_clks "$cg_cmd_mplla_gen_clks \
           -group \[get_clocks \[list ${SNPS_CLOCK_PREFIX}lane*_mpll_dp20_a \
                 ${SNPS_CLOCK_PREFIX}lane*_max_pclk_int_dp20_a \]\]"
 }
 if {$usb3_supported && $dwc_dpalt_phy} {
  set cg_cmd_mplla_gen_clks "$cg_cmd_mplla_gen_clks \
           -group \[get_clocks \[list ${SNPS_CLOCK_PREFIX}lane*_mpll_*usb3_g2 \
                 ${SNPS_CLOCK_PREFIX}lane*_max_pclk_int_*usb3_g2 \
                 ${SNPS_CLOCK_PREFIX}lane*_pcs_clk_usb3_g2 \
                 ${SNPS_CLOCK_PREFIX}lane*_pma_clk_usb3_g2\]\]"
 }
 if { $usb4_supported } {
  set cg_cmd_mplla_gen_clks "$cg_cmd_mplla_gen_clks \
           -group \[get_clocks \[list ${SNPS_CLOCK_PREFIX}lane*_max_pclk_int_usb4_g* \
                 ${SNPS_CLOCK_PREFIX}lane*_mpll_*usb4_g* \]\]"
 }
 eval $cg_cmd_mplla_gen_clks
}

#if { $usb4v2_supported } {
## AB come here
# # Clocking grouping to be executed when combophy is not integrated
# if { !$combo_pipe_synth } {
#  ## Mplla word for usb4 Gen4 clocks are defined asynchronous with the all other clocks in the design
#  set_clock_groups -asynchronous \
    #       -name "Clock_relation_between_mplla_pam3_and_all_remaining_clks" \
    #        -group [get_clocks [list  ${SNPS_CLOCK_PREFIX}phy0_mplla_ana_word_clk_pam3i \
    #             [prefixing $hiervar ${SNPS_CLOCK_PREFIX}phy0_mplla*word*clk_pam3i] \
    #                    ${SNPS_CLOCK_PREFIX}lane*_mpll_usb4_g4 \
    #                    ${SNPS_CLOCK_PREFIX}lane*_max_pclk_int_usb4_g4 ]]
# }
#}


## Subsystem clock grouping ####
# Async Clock Grouping
set_clock_groups -asynchronous -group {mac_scan_coreclk} 

set_clock_groups -asynchronous -group {aux_clk} 
set_clock_groups -asynchronous -group {async_clk_virt} 


# core_clk vs apb pclk groups
 #conflicting
set_clock_groups_asynchronous_w_or_wo_allow_paths -name core_clk_vs_apb_pclk_clkgrp \
      -group [get_clocks [list core_clk* ]] \
      -group [get_clocks [list apb_pclk]]
#set_clock_groups_asynchronous_w_or_wo_allow_paths -name apb_pclk_clkgrp \
      -group [get_clocks [list apb_pclk*]]
      
#F
# all subsystem function clock groups
set_clock_groups_asynchronous_w_or_wo_allow_paths -name acg_all_func_clks \
      -group [get_clocks [list core_clk* ]] \
      -group [get_clocks [list mstr_aclk*]] \
      -group [get_clocks [list slv_aclk*]] \
      -group [get_clocks [list dbi_aclk*]] \

#set_clock_groups -physically_exclusive -group {core_clk_g12} -group {core_clk_g34}
##############################
# Stop Propagations
##############################

foreach_in_collection stop_pin $pins_to_stop_at {
 set pin_obj [get_object_name $stop_pin]
 puts "\[Constraints Debug\] Info: [file tail [info script]] 14 stopping propagation of clocks [get_object_name $stop($pin_obj)] at pin $pin_obj"
 set_sense -type clock -stop_propagation -clocks [get_clocks [get_object_name $stop($pin_obj)]] $pin_obj
}

for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 15 stopping propagation of phy$phy clocks"
 # *fr_clk should be used in SCAN mode only
 set_sense -type clock -stop_propagation -clocks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_clk_i] [get_pins [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_dig_fr_clk]]
 # ref_ana_scan_occ_clk should be used in SCAN mode only
 # stopping of ref_ana_occ_clk can be done after ref-dig_fr_clk branch but before ref_div2 flop. Pin is internal pma pin and skipped for stop propgation
 # this gives warning CLK0004 in GCA which can be waived for ref_div2_clk_i. This warning doesnt come for ref_dig_clk as the clock is stopped at ref_div2 flop output
 #set_sense -type clock -stop_propagation -clocks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i] [get_pins [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_dig_clk_i]]
 set_sense -type clock -stop_propagation -clocks [get_clocks ${SNPS_CLOCK_PREFIX}phy${phy}_ref_ana_occ_clk_i] [get_pins [prefixing $hiervar phy${phy}/${pma_inst_name}/ref_div2_clk_i]]

 if { !$remove_upcs_scan_constraints } {
  #TCM CLK-006; gen clock is only created with functional clock source
  set_sense -type clock -stop_propagation -clocks [get_clocks [list ${SNPS_CLOCK_PREFIX}scan_shift_clk ${SNPS_CLOCK_PREFIX}phy${phy}_scan_occ_clk]] [get_pins [prefixing $hiervar phy${phy}/${pma_inst_name}/mpll?_word_fr_clk]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list ${SNPS_CLOCK_PREFIX}scan_shift_clk ${SNPS_CLOCK_PREFIX}phy${phy}_scan_occ_clk]] [get_pins [prefixing $hiervar phy${phy}/${pma_inst_name}/mpll?_div_fr_clk]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list ${SNPS_CLOCK_PREFIX}scan_shift_clk ${SNPS_CLOCK_PREFIX}phy${phy}_scan_jtag_clk]] [get_pins [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_clk_n_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
 }
}

if { $usb3_supported && !$usb4v2_supported } {
 # Clock propoagation of rx_asic_wclk on pma  rxX_clk pin as not used for USB4/USB3
 set rxX_clk_name  [get_bitblasted_signal rx?_clk $jtag_pma_bit_blasted]
 set_sense -type clock -stop_propagation -clocks [get_clocks *rx?_asic_wclk] [get_pins [prefixing $hiervar phy0/${pma_inst_name}/*${rxX_clk_name}]]
}

if { $usb4_supported && (($usb4_pipe_width == "32" ) || ($usb4_pipe_width == "40")) } {
 # Clock propoagation of rx_asic_dwclk_sds on pma rxX_clk pin as not used for USB4/USB3 in pipe_width 32/40
 set rxX_clk_name  [get_bitblasted_signal rx?_clk $jtag_pma_bit_blasted]
 set_sense -type clock -stop_propagation -clocks [get_clocks *rx?_asic_dwclk_sds] [get_pins [prefixing $hiervar phy0/${pma_inst_name}/*${rxX_clk_name}]]
}

if { !$remove_upcs_scan_constraints } {
 #we create generated clocks on glcm or gate output for functional clocks, always stop propagation of scan clocks on the input of OR gate to avoid TCM CLK-006 violations
 #Scan muxing is present after the or gate
 #TCM CLK-006 there is no scan_shift_clk, phy0_scan_mpll_dword_clk / generated clk present on output
 if { !$perlink_clk_arch } {
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_a_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_b_pin]]

  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mplla_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_a_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mplla_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_b_pin]]
 } else {
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_word_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_a_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_word_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_b_pin]]

  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mplla_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_a_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk ]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mplla_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_b_pin]]
 }
}

if { $pcie_supported } {
 if { !$serdes_mode } {
  #Added to resolve TCM CLK-006. In non-sds mode, pcie_g12 clock will always propagate through flop path
  set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane*_mpll_pcie_g12_phy*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_pcs_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane*_mpll_pcie_g12_phy*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_pma_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
 }
}
#mpll_word_clk_data_mux2 -> pcie/dp glcm -> glcm1 -> source of scan clock
#mplla_clk_data_mux2     -> usb glcm     -> glcm2 -> not source of scan clock


for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {

  if { ($tx_only_supported  && $dwc_dpalt_phy) || $pcie_supported } {
   # Stop the propagation of all clocks through GLCM2 output as only GLCM1 is required for PCIE or tx only phys
   # scan clock would propagate through GLCM1
   # Stop all clocks except div_clk on glcm output
   # div clock to be stopped on protocol mux output to avoid clk-024 violations in TCM
   set_sense -type clock -stop_propagation -clocks $mpll_glcm2_clks_($lane) $mpll_glcm2_out_($lane)
   set_sense -type clock -stop_propagation -clocks $mpll_glcm2_div_clks_($lane) [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_clk_mux_hand_0/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  }
  if { $pcie_supported } {
   # TCM CLK_006 fix : Stop propagation of phy clocks other than clock source PHY
   if { [sizeof_collection $mpll_glcm_not_clksrc_clks_($lane)] > 0  } {
    set_sense -type clock -stop_propagation -clocks $mpll_glcm_not_clksrc_clks_($lane) $lane_mpll_word_clk_src_pin_($lane)
   }
   if { [sizeof_collection $mplla_div_not_clksrc_clks_($lane)] > 0  } {
    set_sense -type clock -stop_propagation -clocks $mplla_div_not_clksrc_clks_($lane) [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mplla_div_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   }
   if { [sizeof_collection $mpllb_div_not_clksrc_clks_($lane)] > 0  } {
    set_sense -type clock -stop_propagation -clocks $mpllb_div_not_clksrc_clks_($lane) [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_mpllb_div_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   }
   if { [sizeof_collection $ref_not_clksrc_clks_($lane)] > 0  } {
    set_sense -type clock -stop_propagation -clocks $ref_not_clksrc_clks_($lane) [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/phy_ref_dig_clk_mux/clk0123_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   }
  }
 }
}
if { ( (!($synth_pipe_integration && ([info exists reuse_upcs_clock_definitions] && $reuse_upcs_clock_definitions))) || $combo_pipe_synth ) } {
 if { (($usb3_supported && $serdes_supported) || ($hdmi_supported && $hdmi_54b_support))  } {
  #TCM-010 no generated clock corresponding to these clocks for pma/pcs dividers
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane?_pclk_serdes* *lane?_pclk_refclk]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_p??_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_clk_pin]]
 }
}

if { $nom_usb3_opt_mpllb } {
 #TCM-010 no generated clock corresponding to these clocks for pma/pcs dividers
 set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane?_mpll_usb3_g2 *lane?_pma_clk_usb3_g2 *lane?_pcs_clk_usb3_g2]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_p??_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_clk_pin]]
 set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane?_pma_clk_usb3_g2 *lane?_pcs_clk_usb3_g2]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_${pclk_out_name}_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_clk_pin]]
}

if { $nom_usb3_opt_mpllb || $pcie_supported } {
 if { !$remove_upcs_scan_constraints } {
  #TCM-006 no generated clock corresponding to the scan clocks on clock gating cell
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *pcs_scan_pcs_clk]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_*pclk_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
 }
}

if { $pcie_supported } {
 if { !$remove_upcs_scan_constraints } {
  #TCM-006 no generated clock corresponding to the scan clocks on clock gating cell
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *pcs_scan_pcs_clk]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_pma_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *pcs_scan_pcs_clk]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/clk_div_flop_base_pcs_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
 }
}

if { $hdmi_supported && $hdmi_54b_support } {
 if { !$remove_upcs_scan_constraints } {
  #TCM-006 no generated clock corresponding to the scan clocks on clock gating cell
  set_sense -type clock -stop_propagation -clocks [get_clocks [list *scan_shift_clk *phy*_scan_mpll_dword_clk]] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_hdmi_clk_gate/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_in_pin]]
 }
}

for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes_in_link($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 16 stopping propagation of RX clocks in pcs lane $lane of link $link_num"
  # Stop clock propagation of clocks which are not intended to be propagated through non-serdes rx datapath- rx_asic_wclk , rx_asic_dwclk_qwclk_sds, rx_asic_qwclk_nonsds, scan_dword_clk
  if { !$tx_only_supported } {
   #For USB3, only rx_asic_dwclk_nonsds clock to be propagated through rx_clk divider
   if { $usb3_supported  } {
    if { $usb4_supported} {
     set_sense -type clock -stop_propagation -clocks [get_clocks *rx?_asic*wclk_nonsds] $sds_rx_clk_buf_inst_($lane)
    }
    set_sense -type clock -stop_propagation -clocks [remove_from_collection $rx_clks_on_nonsds_buf_($lane) [get_clocks *rx*asic_dwclk_nonsds]]  $rx_clk_buf_inst_($lane)
   } else {
    set_sense -type clock -stop_propagation -clocks [remove_from_collection $rx_clks_on_nonsds_buf_($lane) [get_clocks *rx*asic_dwclk*]]  $rx_clk_buf_inst_($lane)
   }
  }
 }
 foreach lane $pcs_lanes($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 17 stopping propagation of mpll/pclk in clock controller $lane of link $link_num"
  if { $pclk_as_phy_input } {
   #there are no in_pclk reaching pma/pcs divider for pclk as output mode
   if { $usb3_supported } {
    # Stop propagation of USB3 pclks at Mux output placed before PMA/PCS divider inside UPCS
    set_sense -type clock -stop_propagation -clocks [get_clocks [concat $lane_usb3_g1_pclks $lane_usb3_g2_pclks]] $lane_mpll_pclk_mux_outpin_($lane)
    if { !$serdes_supported } {
     # for non serdes only products, pclk ref clk will never propagate through mpll pclk mux as serdes mode will always be 0 and only mpll clk will reach
     # using lane? to also match laneX name from TCA level while 0/1 for upcs level
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane?_pclk_refclk] $lane_mpll_pclk_mux_outpin_($lane)
    }
   }
   if { $pcie_supported  && !$serdes_mode } {
    set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane*_pclk_refclk *lane*_pclk_pcie_g12_phy* *lane*_pclk_pcie_g34_phy*]] $lane_mpll_pclk_mux_outpin_($lane)
   }

   if { $hdmi_supported && $hdmi_54b_support } {
    # Stop macro mode based hdmifrl clk from entering pma/pcs dividers as it is only used for fifo logic wr side
    set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_pclk_hdmififo] $lane_mpll_pclk_mux_outpin_($lane)
   }

   if { $hdmi_supported && $hdmi_2p1_ctrl } {
    set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_mpllb_hdmi_maxpclk_frlclk] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/bcm_flop_inst_2/${ck_dff_clrn_src_inst_name}/${ck_dff_clrn_src_clk_pin}]]

    # stop propagation of all dp clocks reaching hdmi only logic
    if { $dp14_supported } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp14*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp14*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp14*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_hdmi_prepclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp14*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pixel_clk_src_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
    }
    if { $dp20_supported } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp20*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp20*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_1/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp20*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_hdmi_prepclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
     set_sense -type clock -stop_propagation -clocks [get_clocks *lane${lane}_*dp20*] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pixel_clk_src_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
    }
   }

  }


  if { $usb3_supported  } {
   #Stop propogation of high speed mpll clocks after divider
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_mpll*usb3_g*]] $lane_pcs_clk_src_muxout_pin_($lane)
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_mpll*usb3_g*]] $lane_pma_clk_src_muxout_pin_($lane)
  }

  if { $nom_usb3_opt_mpllb } {
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_pcs_clk*usb3_g2]] $lane_pma_clk_src_icg_pin_($lane)
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_pma_clk*usb3_g2]] $lane_pcs_clk_src_icg_pin_($lane)
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_pma_clk*usb3_g2 *lane${lane}_pcs_clk*usb3_g2]] $lane_int_icg_pin_($lane)
  }

  if { $hdmi_supported && $hdmi_54b_support  } {
   #Stop propogation of high speed mpll clocks after divider as this clock is used as divided path for fifo logic and for serdes logic input pclk is used
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_mpll_hdmi_b]] $lane_pcs_clk_src_muxout_pin_($lane)
   set_sense -type clock -stop_propagation -clocks [get_clocks [list *lane${lane}_mpll_hdmi_b]] $lane_pma_clk_src_muxout_pin_($lane)
  }

  if { !$remove_upcs_scan_constraints } {
   #Stop propogation of scan clocks at pcs/pma clock divider as scan override mux present after divider
   set_sense -type clock -stop_propagation -clocks [get_clocks [list  *scan*clk*]] $lane_pcs_clk_src_muxout_pin_($lane)
   set_sense -type clock -stop_propagation -clocks [get_clocks [list  *scan*clk*]] $lane_pma_clk_src_muxout_pin_($lane)


   if { $pclk_as_phy_input } {
    # Stopping of input scan pclk reaching to data pin of pclk_nonsds mux
    set_sense -type clock -stop_propagation -clocks [get_clocks *scan*clk*]  $pclk_nonsds_scan_mux_data_pin_($lane)
   }
   if { $pclk_as_phy_input } {
    # Following scan clocks to be stopped to be propagated through max pclk glcm as there is scan mux present in the glcm
    set_sense -type clock -stop_propagation -clocks [get_clocks *phy*_scan_ref_clk ] $lane_max_pclk_glcm_or_pin_($lane)
   }
  }


  if { $pcie_supported } {
   if { $pclk_as_phy_input } {

    if { !$remove_upcs_scan_constraints } {
     # Following scan clocks to be stopped to be propagated through max pclk glcm as there is scan mux present in the glcm
     set_sense -type clock -stop_propagation -clocks [get_clocks *phy*_scan_ref_clk ] $lane_max_pclk_glcm_or_pin_($lane)
    }

    # If final maxpclk/pclk div ratio is nondiv1 then stopping the propagation of high frequency clock based MPLL clocks(div1) are stopped
    if { $pcie4_pclk_final_div_g12 != 1 } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane${lane}_max_pclk_g12_div1_icg_phy*]  $lane_max_pclk_int_muxout_pin_($lane)
    }
    if { $pcie4_pclk_final_div_g34 != 1 } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane${lane}_max_pclk_g34_div1_icg_phy*]  $lane_max_pclk_int_muxout_pin_($lane)
    }

    if { $serdes_mode} {
     # High frequency functional mpll clocks are stopped at mux-d0 placed prior to PCS/PMA divider as pcs/pma clocks are same as in_pclk
     set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane${lane}_mpll_pcie*] $lane_mpll_pclk_mux_d0pin_($lane)

    }

   } else { ;#Pclk as phy output
    if { $pcie4_pclk_final_div_g12 != 1 } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane${lane}_pclk_g12_div1_icg_phy*]  $lane_pclk_src_muxout_pin_($lane)
    }
    if { $pcie4_pclk_final_div_g34 != 1 } {
     set_sense -type clock -stop_propagation -clocks [get_clocks *link*_lane${lane}_pclk_g34_div1_icg_phy*]  $lane_pclk_src_muxout_pin_($lane)
    }

   }
  } ;#end of pcie condition

 } ;#end of foreach
} ;#end of for loop

if { !$remove_upcs_scan_constraints } {
 # Added to avoid CLK_0008 violation in GCA due to different sequential depths through d1 and sel pin. Scan shift clock to be used for divider should come from d1 pin and not sel pin
 set_sense -type clock -stop_propagation -clocks [get_clocks ${SNPS_CLOCK_PREFIX}scan_shift_clk] [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_*_/mpll_clk_mux_hand_0/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_s_pin]]
}

################################
# Clock gating checks disabled
################################
# Following mux's are static MUX's or else the selection change does not cause glitch
##UPCS
foreach cell $cells_for_cg_disable {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 18 clock gating check disabled for $cell"
 set_disable_clock_gating_check [get_cells $cell]
}

if { ($PT_SHELL || $GCA_SHELL || ($flow == "sta" )) } {
 if { $SYNTH_UPF_FLOW  } {
  # for UPF, iso cells are not expected to work as clock gating cells
  set_disable_clock_gating_check [get_cells -quiet [prefixing $hiervar pcs/snps_PD_*_iso*rule_*_UPF_ISO]]
  set_disable_clock_gating_check [get_cells -quiet [prefixing $hiervar phy*/snps_PD_*iso*rule_*_UPF_ISO]]
 }
 set_disable_clock_gating_check [get_pins  [prefixing $hiervar phy*/${pma_inst_name}/*mpll*clk_i ]]
 set_disable_clock_gating_check [get_pins  [prefixing $hiervar phy*/${pma_inst_name}/*clk ]]
}

##PCS RAW
set_disable_clock_gating_check [get_cells [prefixing $hiervar phy*/pcs_raw/cmn/mpll*_clk_and_gen*mpll*_clk_and/*/*]]

##PMA
set scan_clk_sel_name [get_bitblasted_signal scan_clk_sel $jtag_pma_bit_blasted]
set_disable_clock_gating_check [get_pins  [prefixing $hiervar phy*/${pma_inst_name}/${scan_clk_sel_name} ]]
set scan_pma_occ_en_name [get_bitblasted_signal scan_pma_occ_en $jtag_pma_bit_blasted]
set_disable_clock_gating_check [get_pins  [prefixing $hiervar phy*/${pma_inst_name}/${scan_pma_occ_en_name} ]]

