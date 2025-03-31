############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_con_vars.tcl
#
# PIPE(UPCS+PHY) synthesis all variables definitions
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

# Variables TCL synth_variables 



##################################################################################
set TUNIT               1
set FREQ_MARGIN         1.00
set FREQ_MARGIN_SS      1.00


set pcie_ss_inst        "u_pcie_subsys/"
set phy_top_hier        "${pcie_ss_inst}u_pcie_phy_top/"
set pcie_phy_hier       "${pcie_ss_inst}u_pcie_phy_top/u_pcie_pipe/"
set pcie_top_inst      "${pcie_ss_inst}u_pcie_ctrl_top_0/"
set pcie_core_inst     "${pcie_ss_inst}u_pcie_ctrl_top_0/u_pcie_core/"
set pcie_clk_rst_inst  "${pcie_ss_inst}u_pcie_ctrl_top_0/u_pcie_clk_rst/"

#############################################################################
# use 'set_timing_derate' to reserve timing margin in front-end synthesis. 
#############################################################################
set_timing_derate -cell_delay -data -late 1.20
set_timing_derate -late -net 1.20
set_timing_derate -late  1.07 [get_cells [list ${pcie_phy_hier}phy?/pma]]

# 50MHz
set ref_clk_freq        50.0
set ref_clk_period      [expr {1000.0*$TUNIT/($ref_clk_freq * $FREQ_MARGIN_SS)}]
set ref_clk_unc_s       [expr {0.15*$TUNIT}]
set ref_clk_unc_h       0.05

# 100MHz
set apb_pclk_freq       100.0
set apb_pclk_period     [expr {1000.0*$TUNIT/($apb_pclk_freq * $FREQ_MARGIN_SS)}]
set apb_pclk_unc_s      [expr {0.15*$TUNIT}]
set apb_pclk_unc_h      0.05

# 100MHz
set aux_clk_freq        100.0
set aux_clk_period      [expr {1000.0*$TUNIT/($aux_clk_freq * $FREQ_MARGIN_SS)}]
set aux_clk_unc_s       [expr {0.15*$TUNIT}]
set aux_clk_unc_h       0.05

#core_clk 500M 
set core_clk_freq       500.0
set core_clk_period     [expr {1000.0*$TUNIT/$core_clk_freq}]
set core_clk_unc_s      [expr {0.15*$TUNIT}]
set core_clk_unc_h      0.05

#pcie1_core_clk 500M 
set pcie1_core_clk_freq       500.0
set pcie1_core_clk_period     [expr {1000.0*$TUNIT/$pcie1_core_clk_freq}]
set pcie1_core_clk_unc_s      [expr {0.15*$TUNIT}]
set pcie1_core_clk_unc_h      0.05

# 600MHz
set mstr_aclk_freq      600.0
set mstr_aclk_period    [expr {1000.0*$TUNIT/($mstr_aclk_freq * $FREQ_MARGIN_SS)}]
set mstr_aclk_unc_s     [expr {0.10*$TUNIT}]
set mstr_aclk_unc_h     0.05

# 600MHz
set slv_aclk_freq       600.0
set slv_aclk_period     [expr {1000.0*$TUNIT/($slv_aclk_freq * $FREQ_MARGIN_SS)}]
set slv_aclk_unc_s      [expr {0.10*$TUNIT}]
set slv_aclk_unc_h      0.05

# 600MHz
set dbi_aclk_freq       600.0
set dbi_aclk_period     [expr {1000.0*$TUNIT/($dbi_aclk_freq * $FREQ_MARGIN_SS)}]
set dbi_aclk_unc_s      [expr {0.10*$TUNIT}]
set dbi_aclk_unc_h      0.05

# 100MHz
set async_clk_virt_freq       100.0
set async_clk_virt_period     [expr {1000.0*$TUNIT/($async_clk_virt_freq * $FREQ_MARGIN_SS)}]
set async_clk_virt_unc_s      [expr {0.15*$TUNIT}]
set async_clk_virt_unc_h      0.05

set idy_ratio                 0.6
set ody_ratio                 0.6
set mstr_aclk_idy_s           [expr {$mstr_aclk_period*$idy_ratio}]
set mstr_aclk_idy_h           [expr {0.10*$TUNIT}]
set slv_aclk_idy_s            [expr {$slv_aclk_period*$idy_ratio}]
set slv_aclk_idy_h            [expr {0.10*$TUNIT}]
set dbi_aclk_idy_s            [expr {$dbi_aclk_period*$idy_ratio}]
set dbi_aclk_idy_h            [expr {0.10*$TUNIT}]
set core_clk_idy_s            [expr {$core_clk_period*$idy_ratio}] 
set core_clk_idy_h            [expr {0.10*$TUNIT}]
set aux_clk_idy_s             [expr {$aux_clk_period*$idy_ratio}]
set aux_clk_idy_h             [expr {0.10*$TUNIT}]
set ref_clk_idy_s             [expr {$ref_clk_period*$idy_ratio}]
set ref_clk_idy_h             [expr {0.10*$TUNIT}]
##F Reducing it since apb frequency 100MHz
set apb_pclk_idy_s            [expr {$apb_pclk_period*0.3}]
set apb_pclk_idy_h            [expr {0.10*$TUNIT}]
set ref_raw_clk_idy_s         [expr {10.0*$idy_ratio}]
set ref_raw_clk_idy_h         [expr {0.10*$TUNIT}]
set async_clk_virt_idy_s      [expr {$async_clk_virt_period*$idy_ratio}]
set async_clk_virt_idy_h      [expr {0.10*$TUNIT}]

set mstr_aclk_ody_s           [expr {$mstr_aclk_period*$ody_ratio}] 
set mstr_aclk_ody_h           [expr {0.10*$TUNIT}] 
set slv_aclk_ody_s            [expr {$slv_aclk_period*$ody_ratio}] 
set slv_aclk_ody_h            [expr {0.10*$TUNIT}] 
set dbi_aclk_ody_s            [expr {$dbi_aclk_period*$ody_ratio}] 
set dbi_aclk_ody_h            [expr {0.10*$TUNIT}] 
set core_clk_ody_s            [expr {$core_clk_period*$ody_ratio}] 
set core_clk_ody_h            [expr {0.10*$TUNIT}]
set ref_clk_ody_s             [expr {$ref_clk_period*$ody_ratio}]
set ref_clk_ody_h             [expr {0.10*$TUNIT}]
set aux_clk_ody_s             [expr {$aux_clk_period*$ody_ratio}]
set aux_clk_ody_h             [expr {0.10*$TUNIT}]
##F Reducing it since apb frequency 100MHz
set apb_pclk_ody_s            [expr {$apb_pclk_period*0.3}]
set apb_pclk_ody_h            [expr {0.10*$TUNIT}]
set ref_raw_clk_ody_s         [expr {10.0*$ody_ratio}]
set ref_raw_clk_ody_h         [expr {0.10*$TUNIT}]
set async_clk_virt_ody_s      [expr {$async_clk_virt_period*$ody_ratio}]
set async_clk_virt_ody_h      [expr {0.10*$TUNIT}]  
set async_clk_virt_ody_s      [expr {$async_clk_virt_period*$ody_ratio}]
set async_clk_virt_ody_h      [expr {0.10*$TUNIT}]

############ Clock latency values ############

set mstr_aclk_lt_s 0.5
set mstr_aclk_lt_h 0.3

set slv_aclk_lt_s 0.5
set slv_aclk_lt_h 0.3

set dbi_aclk_lt_s 0.5
set dbi_aclk_lt_h 0.3

set ref_clk_lt_s 0.5
set ref_clk_lt_h 0.3

set apb_pclk_lt_s 0.5
set apb_pclk_lt_h 0.3

set async_clk_lt_s 0.5
set async_clk_lt_h 0.3

set core_clk_lt_s 0.5
set core_clk_lt_h 0.3

##############################################


# Global variables used to identify the platform in use
set DC_SHELL 0
set ICC_SHELL 0
set PT_SHELL 0
set GCA_SHELL 0
set FC_SHELL 0
set FM_SHELL 0
set TCM_SHELL 0

if { [info exists synopsys_program_name] } {
 if { $synopsys_program_name == "dc_shell" } {
  set DC_SHELL 1
 } elseif { $synopsys_program_name == "icc_shell" || $synopsys_program_name == "icc2_shell" } {
  set ICC_SHELL 1
 } elseif { $synopsys_program_name == "pt_shell" } {
  set PT_SHELL 1
 } elseif { $synopsys_program_name == "gca_shell" || $synopsys_program_name == "ptc_shell" } {
  set GCA_SHELL 1
 } elseif { $synopsys_program_name == "fc_shell" } {
  set FC_SHELL 1
 } elseif { $synopsys_program_name == "fm_shell" } {
  set FM_SHELL 1
 } elseif { $synopsys_program_name == "tcm" } {
  set TCM_SHELL 1
 }
}

if {![info exists flow]} {
 set flow ""
 puts "Warning: Default: flow is set empty"
}
# Set the default library time unit (1 = ns, 1000 = ps)
# Get the time unit from library
if { $FC_SHELL } {
 set alib [lindex [get_object_name [get_libs]] 1]
} elseif { $DC_SHELL || $ICC_SHELL || $GCA_SHELL || $flow=="syn" } {
 set alib [lindex [get_object_name [get_libs]] 0]
}
if { !$TCM_SHELL } {
 if { $DC_SHELL || $FC_SHELL || $ICC_SHELL || $GCA_SHELL || $flow=="syn" } {
  #set alib [lindex [get_object_name [get_libs]] 0]
  if {$alib != "gtech" && $alib != "standard.sldb"} {
   if { $ICC_SHELL || $GCA_SHELL } {
    set tus [get_attribute -quiet [get_lib $alib] time_unit]
   } else {
    set tus [get_attribute -quiet $alib time_unit_name]
   }

   if {[lindex $tus 0] != ""} {
    set tu [lindex $tus 0]
    puts "tu from library [get_object_name [get_lib $alib]] = $tu\n"
   } else {
    set tu "ns"
   }
  }
 } else {
  foreach alib [get_libs] {
   set tus [get_attribute $alib time_unit_in_second]
  }
  if {[lindex $tus 0] != ""} {
   set tu [lindex $tus 0]
  } else {
  set tu "ns"
  }
 }

 if { $tu == "ns" || $tu == "1e-09" || $tu == "1.00ns" } {
  set TUNIT 1.0
 } elseif { $tu == "ps" || $tu == "1e-12" || $tu == "1.00ps" } {
  set TUNIT 1000.0
 }
} else {
 #TCM tool doesnt require uncertainty and load related constraints, in order to keep files without conditions just setting some value for the variable
 set TUNIT 1.0

}
## Setting synth_pipe_integration if constraints to be loaded at higher level
if { ![info exists synth_pipe_integration] } {
 set synth_pipe_integration 1
 puts "Warning: Default: synth_pipe_integration is set 1"
}

if { ![info exists max_pclk_div_ratio] } {
 set max_pclk_div_ratio "0,0,0,0,0"
 puts "Warning: Default: max_pclk_div_ratio is set 0,0,0,0,0"
}

if { $synth_pipe_integration == 0 } {
 set integration 0
} else {
 set integration 1
}

alias set_clock_groups_asynchronous_w_or_wo_allow_paths "set_clock_groups -asynchronous -allow_paths"

## NOT Supported Configs
## With dpalt mode 0
## --- usb4v2
## --- usb32_dp
## --- dp
## --- hdmi
## --- dp_hdmi
## With dpalt mode 1
## --- usb3

## any_usb_supported = !pcie_supported (created different name to avoid reference of pcie in usb products)
#==========================================================================================================================
# Internal \argument           ||         |        |        |          |        |            |      |        |           |
# Supported\protocol,          || pcie4,0 | usb4,1 | usb4,0 | usb4v2,1 | usb3,0 | usb32_dp,1 | dp,1 | hdmi,1 | dp_hdmi,1 |
# variables\dpalt_mode         ||         |        |        |          |        |            |      |        |           |
#==========================================================================================================================
# pcie_supported               ||    1    |   0    |   0    |    0     |   0    |     0      |  0   |   0    |     0     |
#--------------------------------------------------------------------------------------------------------------------------
# usb4_supported               ||    0    |   1    |   1    |    1     |   0    |     0      |  0   |   0    |     0     |
#--------------------------------------------------------------------------------------------------------------------------
# usb3_supported               ||    0    |   1    |   1    |    1     |   1    |     1      |  0   |   0    |     0     |
#--------------------------------------------------------------------------------------------------------------------------
# usb4v2_supported             ||    0    |   0    |   0    |    1     |   0    |     0      |  0   |   0    |     0     |
#--------------------------------------------------------------------------------------------------------------------------
# dp14_supported               ||    0    |   1    |   0    |    1     |   0    |     1      |  1   |   0    |     1     |
#--------------------------------------------------------------------------------------------------------------------------
# dp20_supported(dp20width!=0) ||    0    |   1    |   0    |    1     |   0    |     1      |  1   |   0    |     1     |
#--------------------------------------------------------------------------------------------------------------------------
# dp20_supported(dp20width==0) ||    0    |   0    |   0    |    0     |   0    |     0      |  0   |   0    |     0     |
#--------------------------------------------------------------------------------------------------------------------------
# dp_supported                 ||    0    |   1    |   0    |    1     |   0    |     1      |  1   |   0    |     1     |
#--------------------------------------------------------------------------------------------------------------------------
# hdmi_supported               ||    0    |   1    |   0    |    1     |   0    |     0      |  0   |   1    |     1     |
#--------------------------------------------------------------------------------------------------------------------------
# tx_only_supported            ||    0    |   0    |   0    |    0     |   0    |     0      |  1   |   1    |     1     |
#--------------------------------------------------------------------------------------------------------------------------
# any_usb_supported            ||    0    |   1    |   1    |    1     |   1    |     1      |  1   |   1    |     1     |
#--------------------------------------------------------------------------------------------------------------------------

# extracting supported subprotocol based on product protocol input
# argument to synthesis scripts
if { $protocol == "pcie4" } {
 set pcie_supported  1
} else {
 set pcie_supported  0
}

if { $protocol == "usb4" || $protocol == "usb4v2" } {
 set usb4_supported  1
 set protocol_usb4v  1
} else {
 set usb4_supported  0
 set protocol_usb4v  0
}

if { $protocol == "usb4" || $protocol == "usb4v2" || ($protocol == "usb3" && !$dwc_dpalt_phy) || $protocol == "usb32_dp" } {
 set usb3_supported  1
} else {
 set usb3_supported  0
}

if { $protocol == "usb4v2" } {
 set usb4v2_supported  1
} else {
 set usb4v2_supported  0
}

if { ($protocol == "usb4" || $protocol == "usb4v2" || $protocol == "usb32_dp" || $protocol == "dp" || $protocol == "dp_hdmi") && $dwc_dpalt_phy } {
 set dp14_supported  1
 set dp_supported  1
} else {
 set dp14_supported  0
 set dp_supported  0
}

if { ($protocol == "usb4" || $protocol == "usb4v2" || $protocol == "hdmi"|| $protocol == "dp_hdmi") && $dwc_dpalt_phy} {
 set hdmi_supported  1
} else {
 set hdmi_supported  0
}

if { ($protocol == "dp" || $protocol == "dp_hdmi"|| $protocol == "hdmi") && $dwc_dpalt_phy} {
 set tx_only_supported  1
} else {
 set tx_only_supported  0
}

if { $protocol == "usb4" || $protocol == "usb32_dp" || $protocol == "usb3" || $protocol == "dp" || $protocol == "hdmi" || $protocol == "dp_hdmi" || $protocol == "usb4v2" } {
 set any_usb_supported 1
} else {
 set any_usb_supported 0
}

if { $protocol == "usb4" || $protocol == "usb32_dp" || $protocol == "dp" || $protocol == "hdmi" || $protocol == "dp_hdmi" || $protocol == "usb4v2" } {
 set serdes_supported 1
} else {
 set serdes_supported 0
}

if { [info exists SNPS_CLOCK_PREFIX] } {
 # do not override if the variable is already defined in higher level script
} else {
 set SNPS_CLOCK_PREFIX ""
 puts "Warning: Default: SNPS_CLOCK_PREFIX is set $SNPS_CLOCK_PREFIX"
}


if { [info exists remove_upcs_scan_constraints] } {
 # do not override if the variable is already defined in higher level script
} else {
 set  remove_upcs_scan_constraints 0
 puts "Warning: Default: remove_upcs_scan_constraints is set $remove_upcs_scan_constraints"
}

# if true then mpllb word clock from pma will be 625 as against 1250
if { $usb3_supported && !$dwc_dpalt_phy } {
 set nom_usb3_opt_mpllb 1
} else {
 set nom_usb3_opt_mpllb 0
}
## Hierarchy to be prefixed
## if no hierarcy "set hiervar /" else set required hierarcy name "set hiervar abc/"
## Hierarchy to be prefixed 
## if no hierarcy "set hiervar /"  else set required hierarcy name "set  hiervar abc/"
# hiervar is used to add prefix to rtl hierarchy paths
# hiervar_ is used to add prefix to primary ports
set  hiervar    $pcie_phy_hier
set  hiervar_   $pcie_ss_inst

# Line Reserved for re-use pragma don't remove it

# Line Reserved for re-use pragma don't remove it

if { $PMA_NAME == "c20" || $PMA_NAME == "c40" } {
 if { $any_usb_supported && $PMA_NAME == "c20" } {
  #Assigning respective pipe width-need to set correct clock frequencies. Format is "usb3, usb4, dp20, dp14, hdmi"
  set usb3_pipe_width [lindex [split $pipe_width ","] 0]
  set usb4_pipe_width [lindex [split $pipe_width ","] 1]
  set dp20_pipe_width [lindex [split $pipe_width ","] 2]
  set dp14_pipe_width [lindex [split $pipe_width ","] 3]
  set hdmi_pipe_width [lindex [split $pipe_width ","] 4]
  #Assigning respective max pclk div ratio to  set correct clock frequencies. Format is "usb3, usb4, dp20, dp14, hdmi"

  set usb3_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 0]
  set usb4_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 1]
  set dp20_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 2]
  set dp14_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 3]
  set hdmi_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 4]
 }
 if { $usb4v2_supported } {
  #Assigning respective pipe width-need to set correct clock frequencies. Format is "usb3, usb4_g23, usb4_g4, dp20tx, dp14tx, hdmi, dp20rx, dp14rx"
  set usb3_pipe_width  [lindex [split $pipe_width ","] 0]
  set usb4_pipe_width  [lindex [split $pipe_width ","] 1]
  set usb4_g4_pipe_width [lindex [split $pipe_width ","] 2]
  set dp20_pipe_width  [lindex [split $pipe_width ","] 3]
  set dp14_pipe_width  [lindex [split $pipe_width ","] 4]
  set hdmi_pipe_width  [lindex [split $pipe_width ","] 5]
  set dp20rx_pipe_width  [lindex [split $pipe_width ","] 6]
  set dp14rx_pipe_width  [lindex [split $pipe_width ","] 7]
  #Assigning respective max pclk div ratio to  set correct clock frequencies. Format is "usb3, usb4_g23, usb4_g4, dp20tx, dp14tx, hdmi, dp20rx, dp14rx"

  set usb3_max_pclk_div_ratio   [lindex [split $max_pclk_div_ratio ","] 0]
  set usb4_max_pclk_div_ratio   [lindex [split $max_pclk_div_ratio ","] 1]
  set usb4_g4_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 2]
  set dp20_max_pclk_div_ratio   [lindex [split $max_pclk_div_ratio ","] 3]
  set dp14_max_pclk_div_ratio   [lindex [split $max_pclk_div_ratio ","] 4]
  set hdmi_max_pclk_div_ratio   [lindex [split $max_pclk_div_ratio ","] 5]
  set dp20rx_max_pclk_div_ratio  [lindex [split $max_pclk_div_ratio ","] 6]
  set dp14rx_max_pclk_div_ratio  [lindex [split $max_pclk_div_ratio ","] 7]
 }
 if { $dp_supported && $dp20_pipe_width != 0} {
  set dp20_supported  1
 } else {
  set dp20_supported  0
 }
 if { $pcie_supported } {
  #Assigning respective pipe width-need to set correct clock frequencies. Format is pcie - "pcie-g1,pcie-g2,pcie-g3,pcie-g4"
  set pcie4_g1_pipe_width [lindex [split $pipe_width ","] 0]
  set pcie4_g2_pipe_width [lindex [split $pipe_width ","] 1]
  set pcie4_g3_pipe_width [lindex [split $pipe_width ","] 2]
  set pcie4_g4_pipe_width [lindex [split $pipe_width ","] 3]
  #Assigning respective max pclk div ratio to  set correct clock frequencies. Format is "pcie-g1, pcie-g2, pcie-g3, pcie-g4"

  set pcie4_g1_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 0]
  set pcie4_g2_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 1]
  set pcie4_g3_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 2]
  set pcie4_g4_max_pclk_div_ratio [lindex [split $max_pclk_div_ratio ","] 3]
 }
}


puts "pma name is $PMA_NAME"
## Get the number of phy tx lanes from the design
set phy_tx_lane_list ""
set txlane  0
if { $PMA_NAME == "c20" || $PMA_NAME == "c40" } {
 set phy_tx_hier [get_object_name [get_cells [prefixing $hiervar phy0/pcs_raw/lane?_tx]]]
}

foreach lane $phy_tx_hier {
 if { $PMA_NAME == "c20" || $PMA_NAME == "c40" } {
  regexp -all {phy0/pcs_raw/lane([0-9])_tx} $lane "" txlane
 }
 lappend phy_tx_lane_list $txlane
}

## Get the number of phy rx lanes from the design
set phy_rx_lane_list ""
if { $PMA_NAME == "c20" || $PMA_NAME == "c40" } {
 set rxlane  0
 set phy_rx_hier [get_object_name [get_cells [prefixing $hiervar phy0/pcs_raw/lane?_rx]]]
 foreach lane $phy_rx_hier {
  regexp -all {phy0/pcs_raw/lane([0-9])_rx} $lane "" rxlane
  lappend phy_rx_lane_list $rxlane
 }
}

## Get the number of UPCS lanes from the design
set pipe_lane_list ""
set ulane  0
set upcs_lane_hier [get_object_name [get_cells [prefixing $hiervar pcs/lane*]]]

foreach lane $upcs_lane_hier {
 regexp -all {pcs/lane([0-9]+)} $lane "" ulane
 lappend pipe_lane_list $ulane
}

puts " phy_lane_list :: $phy_tx_lane_list"
puts " phy_rx_list  :: $phy_rx_lane_list"
puts " pipe_lane_list :: $pipe_lane_list"


# Variable are defined explicitly when synthesis is running at UPCS level, default are set for synth run with combophy
if {![info exists pipe_nlanes]} {
 set pipe_nlanes 2
 puts "Warning: Default: pipe_nlanes is set 2"
}
if {![info exists pipe_nlinks]} {
 set pipe_nlinks 1
 puts "Warning: Default: pipe_nlinks is set 1"
}
if {![info exists pipe_clksrc_perlink]} {
 set pipe_clksrc_perlink 0x
 puts "Warning: Default: pipe_clksrc_perlink is set 0x"
}
if {![info exists pipe_lanes_perlink]} {
 set pipe_lanes_perlink 2x
 puts "Warning: Default: pipe_lanes_perlink is set 2x"
}
if {![info exists perlink_clk_arch]} {
 set perlink_clk_arch 0
 puts "Warning: Default: perlink_clk_arch is set 0"
}

## Computation of num of total lanes, num of links, lanes per link, clksrc of each link
set SameClkSrc [string match {*x} $pipe_clksrc_perlink]

if { $SameClkSrc } {
 set pcs_clksrc [string trimright $pipe_clksrc_perlink x]
} else {
 set pcs_clksrc [split $pipe_clksrc_perlink ,]
}

set SameLanePerLink [string match {*x} $pipe_lanes_perlink]

if { $SameLanePerLink} {
 set pcs_lanes_perlink [string trimright $pipe_lanes_perlink x]
} else {
 set pcs_lanes_perlink [split $pipe_lanes_perlink ,]
}

set inilanes 0
set finallanes 0
set clkctl_inst_perlink 0
#set pcs_lanes ""
## List of clksrc and number of lanes per PCIe link
for {set link 0} {$link<$pipe_nlinks} {incr link} {
 #Clksrc per link
 if { $SameClkSrc } {
  set clksrc($link) $pcs_clksrc
 } else {
  set clksrc($link) [lindex $pcs_clksrc $link]
 }
 puts "\nclksrc for link $link : $clksrc($link)"

 set inilanes $finallanes
 ## Lanes per link
 if { $SameLanePerLink } {
  set pcs_tlanes($link) $pcs_lanes_perlink
 } else {
  set pcs_tlanes($link) [lindex $pcs_lanes_perlink $link]
 }
 puts "list of total pcs lanes in link $link : $pcs_tlanes($link)"
 set finallanes [expr {$inilanes + $pcs_tlanes($link)}]
 puts "finallanes : $finallanes"
 #puts "inilane is = $inilanes"
 set pcs_lanes($link) ""
 set pcs_lanes_in_link($link) ""
 for {set lane $inilanes} {$lane<$finallanes} {incr lane} {
  lappend pcs_lanes_in_link($link) $lane
 }
 if { $perlink_clk_arch } {
  lappend pcs_lanes($link) $clkctl_inst_perlink
  incr clkctl_inst_perlink
 } else {
  for {set lane $inilanes} {$lane<$finallanes} {incr lane} {
   #lappend pcs_lanes($link) $lane
   lappend pcs_lanes($link) $lane
  }
 }
 puts "list of lanes in link $link : $pcs_lanes_in_link($link)"
 puts "list of clk_ctl instances in  link $link : $pcs_lanes($link)"
} ;#end of for loop

# Variable used when synthesis is running at UPCS level, not with combophy
if {![info exists combo_pipe_synth]} {
 set combo_pipe_synth 0
}
if {![info exists pclk_as_phy_input]} {
 set pclk_as_phy_input 1
}
if {![info exists serdes_mode]} {
 set serdes_mode 0
}

# Line Reserved for reuse pragma

if {![info exists msg2apb_pdos_reg]} {
 set msg2apb_pdos_reg 0
}
if {![info exists jtag_mphy_support]} {
 set jtag_mphy_support 0
}
if {![info exists noextrom]} {
 set noextrom 0
}
if {![info exists norom]} {
 set norom 0
}
if {![info exists jtag_phy_res_ext]} {
 set jtag_phy_res_ext 0
}
if {![info exists dpalt_4tx4rx]} {
 set dpalt_4tx4rx 0
}
if {![info exists jtag_pma_new_timing_arcs]} {
 set jtag_pma_new_timing_arcs 0
}

if { [info exists FREQ_MARGIN] } {
 # do not override if the variable is already defined in higher level script
} else {
 set FREQ_MARGIN   1.15
 puts "Warning: Default: FREQ_MARGIN is set 1.15"
}


if { [info exists jtag_pma_bit_blasted] } {
 # do not override if the variable is already defined in higher level script
} else {
 set jtag_pma_bit_blasted   0
}
if { [info exists pma_inst_name] } {
 # do not override if the variable is already defined in higher level script
} else {
 set pma_inst_name   pma
}

##-- Clk variables
set DP20_PIPE_20B_FREQ   843.75
set DP14_PIPE_10B_FREQ   810.0
set HDMI_PIPE_10B_FREQ   1200.0
set HDMI_PIPE_54B_FREQ   225.0
if { $pcie_supported } {
 # PCIe-Gen3 , Gen4 has Mplla word 1000M
 set MPLLA_WCLK_FREQ     1000.0
} elseif { $usb4_supported } {
 # USB4/TBT3 data rates have Mplla word to be 1289.0625M
 set MPLLA_WCLK_FREQ    1290.0
} elseif { $protocol == "hdmi" } {
 # for HDMI FRL data rates have Mplla word to be 1200.0M
 set MPLLA_WCLK_FREQ     1200.0
} elseif { $nom_usb3_opt_mpllb } {
 # for nominal USB products Mplla word is not used and mpllb word is max 625.0M
 set MPLLA_WCLK_FREQ    625.0
} else {
 # DP UHBHR-10G, 20G, usb3* require Mplla word to be 1250.00M
 set MPLLA_WCLK_FREQ     1250.0
}
set MPLLA_WCLK_TRIT28_FREQ     914.29
set RX_TRIT_DIV28_FREQ   $MPLLA_WCLK_TRIT28_FREQ
set MPLLA_DIV_FREQ     500.0
set MPLLA_DIV16P5_FREQ   625.0
set JTAG_CLK_FREQ      100.0
set BS_CLK_FREQ       100.0
set APB_CLK_FREQ      400.0
set FW_CLK_FREQ       400.0
set SCAN_SHIFT_FREQ     200.0
if { $protocol == "pcie4" } {
 set REF_DIG_CLK_FREQ    100.0
 set SCAN_REF_CLK_FREQ   100.0
} else {
 if { [info exists ref_freq_val] } {
  set REF_DIG_CLK_FREQ    $ref_freq_val
  set SCAN_REF_CLK_FREQ   $ref_freq_val
 } else {
  set REF_DIG_CLK_FREQ    200.0
  set SCAN_REF_CLK_FREQ   200.0
 }
}
set DCO_CLK_CAL_FREQ   [expr {288.0 * 3.0/2.0}]    ;# Referred from raw constraints
set DCO_CLK_CCO_FREQ   72.0              ;# Referred from raw constraints
set RX_ANA_PWM_FREQ   850.0             ;# Referred from raw constraints
set RX_PWM_CLK_EDGE         {1 5 23}             ;
set RX_PWM_CLK_EDGE_SHIFT   {0 4.704 0}             ;
set RX_PWM_WCLK_EDGE        {1 21 41}             ;
set TX_PWM_WCLK_EDGE        {1 21 41}             ;
set TX_PWM_BIT_CLK_EDGE     {1 3 7}             ;
set REF_ANA_FREQ      [expr {2*$REF_DIG_CLK_FREQ}]
set REF_ANA_OCC_FREQ    $REF_DIG_CLK_FREQ
set CR_CLK_FREQ       [expr {max ($REF_DIG_CLK_FREQ,$JTAG_CLK_FREQ, $APB_CLK_FREQ, $FW_CLK_FREQ )}]
set SCAN_OCC_FREQ      100.0   ;#JIRA#[P80001562-226618]
# variables to set MPLLB WORD CLK frequency for DP1.4=8.1Gbps, DP2.0=13.5Gbps, HDMI FRL=12G
set MPLLB_WCLK_FREQ_DP20     $DP20_PIPE_20B_FREQ
set MPLLB_WCLK_FREQ_DP14     $DP14_PIPE_10B_FREQ
set MPLLB_WCLK_FREQ_HDMI     $HDMI_PIPE_10B_FREQ
set MPLLB_WCLK_FREQ_PCIE     500.0              ;#PCIe-Gen1, Gen2
# In USB nominal PHYs, mpllb is used for usb3.x
# usb 3 gen1 mpllb div clk of 500M and
# usb 3 gen2 mpllb word clk of 1250M and
set MPLLB_DIV_FREQ            500.0
if { $nom_usb3_opt_mpllb } {
 set MPLLB_WCLK_FREQ_NOMINAL   625.0
} else {
 set MPLLB_WCLK_FREQ_NOMINAL   1250.0
}
#Variable set for PMA Tx
if { $any_usb_supported && $dwc_dpalt_phy} {
 set TX_WCLK_FREQ      [expr {max ($MPLLA_WCLK_FREQ,$MPLLA_DIV_FREQ,$DP20_PIPE_20B_FREQ,$DP14_PIPE_10B_FREQ,$HDMI_PIPE_10B_FREQ)}]
} elseif { $protocol == "usb32_dp" && $dp20_pipe_width !=0 && $dwc_dpalt_phy} {
 set TX_WCLK_FREQ      [expr {max ($MPLLA_WCLK_FREQ,$MPLLA_DIV_FREQ,$DP20_PIPE_20B_FREQ,$DP14_PIPE_10B_FREQ)}]
} elseif { $protocol == "usb32_dp" && $dp20_pipe_width ==0 && $dwc_dpalt_phy} {
 set TX_WCLK_FREQ      [expr {max ($MPLLA_WCLK_FREQ,$MPLLA_DIV_FREQ,$DP14_PIPE_10B_FREQ)}]
} elseif { $any_usb_supported && !$dwc_dpalt_phy} {
 set TX_WCLK_FREQ      [expr {max ($MPLLA_WCLK_FREQ,$MPLLA_DIV_FREQ,$MPLLB_WCLK_FREQ_NOMINAL,$MPLLB_DIV_FREQ)}]
} else { ;#pcie
 set TX_WCLK_FREQ      [expr {max ($MPLLA_WCLK_FREQ,$MPLLB_WCLK_FREQ_PCIE)}]
}
if { $protocol == "pcie4"} {
 set RX_WCLK_FREQ      $MPLLB_WCLK_FREQ_PCIE ;#WCLK is used for 8-bit only and in pcie 8-bit is supported for G1/G2 only in sds
} else {
 set RX_WCLK_FREQ      $MPLLA_WCLK_FREQ
}
set RX_DWCLK_FREQ      $MPLLA_WCLK_FREQ        ;#defined for serdes protocols-usb4,tbt3, and, for pcie-mplla word has higher frequency
if { $usb4_supported } {
 # for USB4 product mpll word clock is 1290 to support TBT and has direct path to pcs clock which is divided version. This causes GCA error due to sync clock path between pcs clk (645) to rx nonsds clk (625). To match the period run rx nonsds path on slighly higher frequency
 set RX_DWCLK_NONSDS_FREQ  645.0   ;#variable defined for usb3-non-serdes rx datapath
} else {
 set RX_DWCLK_NONSDS_FREQ  625.0   ;#variable defined for usb3-non-serdes rx datapath
}
set RX_DIV16P5_FREQ     625.0
set HDMI_DIV_FREQ         667

#Setting Clock Network Latency Variables
set SCAN_RX_CLOCK_LATENCY 0.930
set RX_ASIC_WCLK_CLOCK_LATENCY 0.350
set RX_ASIC_DWCLK_CLOCK_LATENCY 0.350
set RX_ASIC_QWCLK_CLOCK_LATENCY 0.350
set PMA_CR_PARA_CLOCK_LATENCY  0.230
# Set clock latency 500ps on apb0_pclk/fw_clk/scan_cr_clk to fix the cr_reg_rd_data_d_reg violations
safe_set APB0_FW_SCAN_CR_CLOCK_LATENCY APB0_FW_SCAN_CR_CLOCK_LATENCY 0.500

# Pclk freq for usb is computed based on input pipe width set
if { $pcie_supported } {
 ## PCIe Gen1, Gen2 are supported for pipe intf width 8b/16b/32b
 ## PCIe Gen3, Gen4 are supported for pipe intf width 16b/32b for non-serdes mode
 ## PCIe Gen3 supported for pipe intf width 8b/16b/32b, Gen4 supported for pipe intf width 16b/32b for serdes mode
 if { $pcie4_g2_pipe_width == 8 || $pcie4_g2_pipe_width == 10 } {
  set PCLK_PCIE_G12_FREQ    $MPLLB_WCLK_FREQ_PCIE
 } elseif { $pcie4_g2_pipe_width == 16 || $pcie4_g2_pipe_width == 20 || $pcie4_g1_pipe_width == 8 || $pcie4_g1_pipe_width == 10 } {
  set PCLK_PCIE_G12_FREQ    [expr {$MPLLB_WCLK_FREQ_PCIE/2}]
 } else {
  set PCLK_PCIE_G12_FREQ    [expr {$MPLLB_WCLK_FREQ_PCIE/4}]
 }
 if { $pcie4_g3_pipe_width == 8 || $pcie4_g3_pipe_width == 10 || $pcie4_g4_pipe_width == 16 || $pcie4_g4_pipe_width == 20 } {
  set PCLK_PCIE_G34_FREQ    $MPLLA_WCLK_FREQ
 } elseif { $pcie4_g3_pipe_width == 16 || $pcie4_g3_pipe_width == 20 || $pcie4_g4_pipe_width == 32 || $pcie4_g4_pipe_width == 40 } {
  set PCLK_PCIE_G34_FREQ    [expr {$MPLLA_WCLK_FREQ/2}]
 } else {
  set PCLK_PCIE_G34_FREQ    [expr {$MPLLA_WCLK_FREQ/4}]
 }
 set SCAN_PCLK_NONSDS_FREQ $PCLK_PCIE_G34_FREQ
} ;# End of PCie4

#scan_rx_dword_clk freq is kept dependent on pipe_width for pcie sds mode, whereas for non-sds mode it's kept same as mplla_wclk i.e. 1000MHz as fixed 16-bit is supported which can have max 1GHz clock
if { $pcie_supported && $serdes_mode } {
 set SCAN_RX_DWCLK_FREQ $PCLK_PCIE_G34_FREQ
} elseif { $usb4_supported && ( $usb4_pipe_width == 32 || $usb4_pipe_width == 32 ) } {
 set SCAN_RX_DWCLK_FREQ [expr {$MPLLA_WCLK_FREQ/2}]
} else {
 set SCAN_RX_DWCLK_FREQ $MPLLA_WCLK_FREQ
}

set PCLK_REF_CLK_FREQ                      $REF_DIG_CLK_FREQ

if { $pcie_supported } {
 set PCLK_SERDES_FREQ    [expr {max ($PCLK_PCIE_G12_FREQ, $PCLK_PCIE_G34_FREQ)}]
}

# ASST Scan Clock Frequencies
set SCAN_PCS_CLK_FREQ    $MPLLA_WCLK_FREQ

if {$pcie_supported } {  ;#CHoose the maximum frequency b/w G3-G4 rx dwclk
 set SCAN_PCS_RX_CLK_DIV_FREQ  $RX_DWCLK_FREQ
} else {
 set SCAN_PCS_RX_CLK_DIV_FREQ  $RX_DWCLK_NONSDS_FREQ
}

if {$pcie_supported } {
 set SCAN_PMA_CLK_FREQ    $MPLLA_WCLK_FREQ    ;#Max freq is corresponding to Gen4-16b Phy intf
} else {
 if {$dwc_dpalt_phy} {
  if {$tx_only_supported} {
   set SCAN_PMA_CLK_FREQ          [expr {$HDMI_PIPE_10B_FREQ/2}]      ;#Non-Serdes Path Clock only used with macro in HDMI
  } else {
   set SCAN_PMA_CLK_FREQ          [expr {$MPLLA_WCLK_FREQ/2}]        ;#Non-Serdes Path Clock
  }
 } else {
  if { $nom_usb3_opt_mpllb } {
   set SCAN_PMA_CLK_FREQ          [expr {$MPLLB_WCLK_FREQ_NOMINAL/1}]    ;#Non-Serdes Path Clock
  } else {
   set SCAN_PMA_CLK_FREQ          [expr {$MPLLB_WCLK_FREQ_NOMINAL/2}]    ;#Non-Serdes Path Clock
  }
 }
}


if {$pcie_supported} {
 set SCAN_PCLK_OUT_FREQ           $PCLK_SERDES_FREQ
 set SCAN_PCLK_IN_FREQ            $PCLK_SERDES_FREQ
} elseif { $usb3_supported } {
 set SCAN_PCLK_OUT_FREQ           [expr {max ($PCLK_SERDES_FREQ,$PCLK_USB3_G1_FREQ,$PCLK_USB3_G2_FREQ,$PCLK_REF_CLK_FREQ)}]
 set SCAN_PCLK_IN_FREQ            [expr {max ($PCLK_SERDES_FREQ,$PCLK_USB3_G1_FREQ,$PCLK_USB3_G2_FREQ,$PCLK_REF_CLK_FREQ)}]
} elseif { $hdmi_supported } {
 set SCAN_PCLK_OUT_FREQ           [expr {max ($PCLK_SERDES_FREQ,$PCLK_REF_CLK_FREQ,$PCLK_HDMIFIFO_FREQ)}]
 set SCAN_PCLK_IN_FREQ            [expr {max ($PCLK_SERDES_FREQ,$PCLK_REF_CLK_FREQ,$PCLK_HDMIFIFO_FREQ)}]
} else {
 set SCAN_PCLK_OUT_FREQ           [expr {max ($PCLK_SERDES_FREQ,$PCLK_REF_CLK_FREQ)}]
 set SCAN_PCLK_IN_FREQ            [expr {max ($PCLK_SERDES_FREQ,$PCLK_REF_CLK_FREQ)}]
}
if { $pclk_as_phy_input } {
 set pclk_out_name  max_pclk
} else {
 set pclk_out_name  pclk
 if { $any_usb_supported } {
  set usb3_max_pclk_div_ratio  0
 }
}

# Variables used to set the final div ratio set based on pipe_width and max_pclk_div_ratio
if {$pcie_supported } {
 set pcie4_max_pclk_final_div_g1  [max_pclk_final_div pcie4_g1 $pcie4_g1_max_pclk_div_ratio $pcie4_g1_pipe_width]
 set pcie4_max_pclk_final_div_g2  [max_pclk_final_div pcie4_g2 $pcie4_g2_max_pclk_div_ratio $pcie4_g2_pipe_width]
 set pcie4_max_pclk_final_div_g3  [max_pclk_final_div pcie4_g3 $pcie4_g3_max_pclk_div_ratio $pcie4_g3_pipe_width]
 set pcie4_max_pclk_final_div_g4  [max_pclk_final_div pcie4_g4 $pcie4_g4_max_pclk_div_ratio $pcie4_g4_pipe_width]
 set pcie4_max_pclk_final_div_g12  [expr {min ($pcie4_max_pclk_final_div_g1, $pcie4_max_pclk_final_div_g2)}]
 set pcie4_max_pclk_final_div_g34  [expr {min ($pcie4_max_pclk_final_div_g3, $pcie4_max_pclk_final_div_g4)}]

 set pcie4_pclk_final_div_g1    [max_pclk_final_div pcie4_g1 0 $pcie4_g1_pipe_width]
 set pcie4_pclk_final_div_g2    [max_pclk_final_div pcie4_g2 0 $pcie4_g2_pipe_width]
 set pcie4_pclk_final_div_g3    [max_pclk_final_div pcie4_g3 0 $pcie4_g3_pipe_width]
 set pcie4_pclk_final_div_g4    [max_pclk_final_div pcie4_g4 0 $pcie4_g4_pipe_width]
 set pcie4_pclk_final_div_g12    [expr {min ($pcie4_pclk_final_div_g1, $pcie4_pclk_final_div_g2)}]
 set pcie4_pclk_final_div_g34    [expr {min ($pcie4_pclk_final_div_g3, $pcie4_pclk_final_div_g4)}]
}

# Variables used to set nondiv ratio, if final div ratio is 1 then default nondiv set to 2

if {$pcie_supported } {
 if { $pcie4_max_pclk_final_div_g12 == 1 } {
  set pcie4_max_pclk_non_div_g12    2
 } else {
  set pcie4_max_pclk_non_div_g12    $pcie4_max_pclk_final_div_g12
 }
 if { $pcie4_max_pclk_final_div_g34 == 1 } {
  set pcie4_max_pclk_non_div_g34    2
 } else {
  set pcie4_max_pclk_non_div_g34    $pcie4_max_pclk_final_div_g34
 }
 if { $pcie4_pclk_final_div_g12 == 1 } {
  set pcie4_pclk_non_div_g12    2
 } else {
  set pcie4_pclk_non_div_g12    $pcie4_pclk_final_div_g12
 }
 if { $pcie4_pclk_final_div_g34 == 1 } {
  set pcie4_pclk_non_div_g34    2
 } else {
  set pcie4_pclk_non_div_g34    $pcie4_pclk_final_div_g34
 }
} ;#end of prot(pcie4) condition


if {$pcie_supported } {
 set SCAN_MAX_PCLK_FREQ     [expr {max ($MPLLB_WCLK_FREQ_PCIE/$pcie4_pclk_final_div_g12, $MPLLA_WCLK_FREQ/$pcie4_pclk_final_div_g34)}]
}



#
#
# Clock Uncertainty
# P80001562-462169 Provide PLL jitter and duty-cycle distortion numbers for STA constraints
# CK(set unc) = SUP + Clock Jitter + Rx CDR Drift
# SUP: SUP_UNC_MARGIN * Clock period, which max value is not greater than SUP_UNC_MAX.
#       SUP_UNC_MARGIN is a scaling factor
#       SUP_UNC_MAX unit is ns
# Clock Jitter: Clock Jitter Worst case value, Variable name format is "JITTER_%CLOCK_NAME". Unit is ns
# Rx CDR Drift: Optional, it is used for RX clock CDR drift. In generally, RX W/DW clock is 0.06 * clock period,
#               RX Q/O clock is 0.03 * clock period. The unit is ns.
# CK(hold unc) = UNC_HLD/UNC_RX_HLD/UNC_SCAN_HLD
# UNC_HLD: for function clock hold uncertainty. Unit is ns
# UNC_RX_HLD: for RX function clock hold uncertainty. Unit is ns
# UNC_SCAN_HLD: for scan clock hold uncertainty. Unit is ns
# CK(set DCU) = CK(set unc) + DCU
# CK(hold DCU) = CK(hold unc) + DCU
# DCU: DCU_%CLOCK_NAME * clock period. Variable name format is "DCU_%CLOCK_NAME".
#       DCU_%CLOCK_NAME is a scaling factor
# EDGE_MPLLD16P5: The duty percentage of pma clock mplla_ana_div16p5_clk_i


safe_set    SUP_UNC_MARGIN      SUP_UNC_MARGIN  0.0500
#additional uncertainty control for customer across different stages of development

if { ![info exists EXTRA_SETUP_UNC] } {
 set EXTRA_SETUP_UNC 0.00
}
if { ![info exists EXTRA_HOLD_UNC] } {
 set EXTRA_HOLD_UNC 0.00
}



# Default setup and hold uncertainties for non-SCAN clocks
safe_set UNC_HLD UNC_HLD 0.050

# Default setup and hold uncertainties for SCAN clocks.
# NOTE:
#   As the SCAN clocks come from customer side, customer can choose the value match the real
#   characterstic of SCAN clocks.
safe_set UNC_SCAN_HLD UNC_SCAN_HLD 0.050

# max up to 100ps by default
safe_set    SUP_UNC_MAX         SUP_UNC_MAX     0.1000

safe_set UNC_RX_HLD  UNC_RX_HLD    $UNC_HLD
safe_set    JITTER_JTAG         JITTER_JTAG         0.070

safe_set    JITTER_SCAN_JTAG    JITTER_SCAN_JTAG    0.070
safe_set    JITTER_FW           JITTER_FW           0.070
safe_set    JITTER_SCAN_FW      JITTER_SCAN_FW      0.070
safe_set    JITTER_APB          JITTER_APB          0.070
safe_set    JITTER_SCAN_APB     JITTER_SCAN_APB     0.070
safe_set    JITTER_SCAN_PCS_CLK     JITTER_SCAN_PCS_CLK     0.070
safe_set    JITTER_SCAN_PCS_RX     JITTER_SCAN_PCS_RX     0.070
safe_set    JITTER_SCAN_PCS_FIFO_RD      JITTER_SCAN_PCS_FIFO_RD      0.070
safe_set    JITTER_SCAN_PCS_FIFO_WR      JITTER_SCAN_PCS_FIFO_WR      0.070
safe_set    JITTER_SCAN_PCS_MAX_PCLK      JITTER_SCAN_PCS_MAX_PCLK      0.070
safe_set   JITTER_SCAN_PCS_NONSDS_PCLK      JITTER_SCAN_PCS_NONSDS_PCLK      0.070
safe_set   JITTER_SCAN_PCS_IN_PCLK      JITTER_SCAN_PCS_IN_PCLK      0.070
safe_set   JITTER_SCAN_PCS_PCLK      JITTER_SCAN_PCS_PCLK      0.070
safe_set    JITTER_SCAN_PCS_PMA_CLK     JITTER_SCAN_PCS_PMA_CLK     0.070
safe_set    JITTER_BS           JITTER_BS           0.070
safe_set    JITTER_TXDW         JITTER_TXDW         0.030
safe_set    JITTER_SCAN_CR      JITTER_SCAN_CR      0.070

safe_set    JITTER_REF          JITTER_REF          0.070
safe_set    JITTER_MPLLAW       JITTER_MPLLAW       0.030
safe_set    JITTER_MPLLBW       JITTER_MPLLBW       0.030
safe_set    JITTER_MPLLADIV     JITTER_MPLLADIV     0.030
safe_set    JITTER_PCLK_SERDES         JITTER_PCLK_SERDES  [expr {max ($JITTER_MPLLAW,$JITTER_MPLLBW)}]
safe_set    JITTER_MPLLBDIV     JITTER_MPLLBDIV     0.030
safe_set    JITTER_HDMIBDIV     JITTER_HDMIBDIV     0.030
safe_set    JITTER_MPLLAD16P5   JITTER_MPLLAD16P5   0.030
safe_set    JITTER_DCO          JITTER_DCO          0.030
safe_set    JITTER_RXDW         JITTER_RXDW         0.030
safe_set    JITTER_RXD16P5      JITTER_RXD16P5      0.030
safe_set    JITTER_MPWMR        JITTER_MPWMR        0.030

safe_set    JITTER_SCAN_SHIFT   JITTER_SCAN_SHIFT       0.070
safe_set    JITTER_SCAN_QWORD   JITTER_SCAN_QWORD       0.070
safe_set    JITTER_SCAN_DWORD   JITTER_SCAN_DWORD       0.070
safe_set    JITTER_SCAN_REF     JITTER_SCAN_REF         0.070
safe_set    JITTER_SCAN_OCC     JITTER_SCAN_OCC         0.070

safe_set    JITTER_PMA_COMMON   JITTER_PMA_COMMON       0.030
safe_set    DCU_REF             DCU_REF                 0.15
safe_set    DCU_MPLLAW          DCU_MPLLAW              0.07
safe_set    DCU_MPLLBW          DCU_MPLLBW              0.07
safe_set    DCU_MPLLADIV        DCU_MPLLADIV            0.15
safe_set    DCU_MPLLBDIV        DCU_MPLLBDIV            0.15
safe_set    DCU_MPLLAD16P5      DCU_MPLLAD16P5          0.02
safe_set    DCU_MPLLBHDMI       DCU_MPLLBHDMI           0.07
safe_set    DCU_TXDW            DCU_TXDW                0.05
safe_set    DCU_RXDW            DCU_RXDW                0.05
safe_set    DCU_RXD16P5         DCU_RXD16P5             0.05
safe_set    DCU_RXPWM           DCU_RXPWM               0.10
safe_set    DCU_BS              DCU_BS                  0.10
safe_set    DCU_PCLK_SERDES              DCU_PCLK_SERDES                 [expr {max ($DCU_MPLLAW,$DCU_MPLLBW)}]
safe_set    DCU_DCO             DCU_DCO                 0.10
safe_set    DCU_SCAN_SHIFT      DCU_SCAN_SHIFT          0.10

safe_set    DCU_SCAN_CR         DCU_SCAN_CR             0.10
safe_set    DCU_JTAG            DCU_JTAG                0.10
safe_set    DCU_SCAN_JTAG       DCU_SCAN_JTAG           0.10
safe_set    DCU_FW              DCU_FW                  0.10
safe_set    DCU_SCAN_FW         DCU_SCAN_FW             0.10
safe_set    DCU_APB             DCU_APB                 0.10
safe_set    DCU_SCAN_PCS_CLK        DCU_SCAN_PCS_CLK            0.10
safe_set    DCU_SCAN_PCS_RX        DCU_SCAN_PCS_RX     0.10
safe_set    DCU_SCAN_PCS_FIFO_RD        DCU_SCAN_PCS_FIFO_RD  0.10
safe_set    DCU_SCAN_PCS_FIFO_WR       DCU_SCAN_PCS_FIFO_WR  0.10
safe_set    DCU_SCAN_PCS_MAX_PCLK       DCU_SCAN_PCS_MAX_PCLK   0.10
safe_set    DCU_SCAN_PCS_NONSDS_PCLK       DCU_SCAN_PCS_NONSDS_PCLK  0.10
safe_set    DCU_SCAN_PCS_IN_PCLK      DCU_SCAN_PCS_IN_PCLK  0.10
safe_set    DCU_SCAN_PCS_PCLK       DCU_SCAN_PCS_PCLK  0.10
safe_set    DCU_SCAN_PCS_PMA_CLK       DCU_SCAN_PCS_PMA_CLK   0.10
safe_set    DCU_SCAN_APB        DCU_SCAN_APB            0.10
safe_set    DCU_SCAN_REF        DCU_SCAN_REF            0.10
safe_set    DCU_SCAN_OCC        DCU_SCAN_OCC            0.10
safe_set    DCU_SCAN_DWORD      DCU_SCAN_DWORD          0.10
safe_set    DCU_SCAN_QWORD      DCU_SCAN_QWORD          0.10

safe_set    DCU_PMA_COMMON      DCU_PMA_COMMON          0.10

set RX_WCLK_DRIFT_MARGIN 0.06
set RX_QCLK_DRIFT_MARGIN 0.03
array set  unc_set_clks_info {}
set unc_set_name_clks ""
# ALl clock collection arrays initializations
set ip_all_func_clocks ""
set ip_all_func_clocks_with_embedded_asst_clks ""
set ip_all_asst_clks ""
set ip_all_asst_clks_on_func_ports ""
set all_clocks_collection ""
set lane_usb3_g1_pclks ""
set lane_usb3_g2_pclks ""
set ip_all_shift_clks ""
set ip_all_func_pclks ""
set scan_clocks_all ""
set upcs_mpll_estore_rd_clk ""
set upcs_rx_estore_wr_clk ""
set all_estore_related_rx_wr_clks ""
set all_estore_related_mpll_rd_clks ""
set all_tx_rx_estore_clks ""
set tx_mpll_estore_rd_clks_rest ""
set rx_estore_wr_clks_rest ""

foreach lane $pipe_lane_list {
 set pcs_lane_dp20_a_clks_(${lane}) ""
 set pcs_lane_dp20_b_clks_(${lane}) ""
 set pcs_lane_dp14_clks_(${lane}) ""
 set pcs_lane_hdmi_clks_(${lane}) ""
 set pcs_lane_usb3_g1_clks_(${lane}) ""
 set pcs_lane_usb3_g2_clks_(${lane}) ""
 set pcs_lane_usb4_clks_(${lane}) ""
 set pcs_lane_pcie_g34_pclks_(${lane}) ""
 set pcs_lane_pcie_g12_pclks_(${lane}) ""
}
for {set phy 0} {$phy < $nphys} {incr phy} {
 set all_mplla_div_clocks_($phy) ""
 set all_mpllb_div_clocks_($phy) ""
 set all_mplla_word_clocks_($phy) ""
 set all_mpllb_word_clocks_($phy) ""
 set all_mplla_div16p5_clocks_($phy) ""
 set all_mpllb_hdmi_div_clocks_($phy) ""
 set all_tx_ana_word_clocks_($phy) ""
 set all_rx_ana_div16p5_clocks_($phy) ""
 set all_ref_clocks_($phy) ""
 set all_fw_clocks_($phy) ""
 set all_apb0_clocks_($phy) ""
 set all_apb1_clocks_($phy) ""
 set all_mphy_clocks_($phy) ""
 set all_bs_cdr_($phy) ""
 set all_bs_udr_($phy) ""
 set all_func_jtag_($phy) ""
}

#array initialization of pre_stop_clocks
set scan_func_mux_instances ""
set scan_scan_mux_instances ""
set misc_mux_inst_d1 ""
set misc_mux_inst_d0 ""
set phy_scanMode_clkSel_mux_inst ""
set phy_scan_shift_clk_stop_mux_inst ""
set cells_for_cg_disable ""
set pins_to_stop_at ""

# clock source pin of GLCM, Dividers
for {set link_num 0} {$link_num < $pipe_nlinks} {incr link_num} {
 foreach lane $pcs_lanes($link_num) {
  #set mpll_a_b_word_glcm_mpll_clk_src_pin_($lane)
  #set mpll_a_b_word_glcm_outpin_($lane)
  #set mpll_div_word_glcm_mpll_clk_src_pin_($lane)
  #set mpll_div_word_glcm_outpin_($lane)
  #set lane_mpll_clk_proto_mux_outpin_($lane)
  #set lane_mpll_pclk_mux_d0pin_($lane)
  #set lane_mpll_pclk_mux_outpin_($lane)
  #set lane_pma_clk_div_src_flop_pin_($lane)
  #set lane_pma_clk_src_muxout_pin_($lane)
  #set lane_pcs_clk_div_src_flop_pin_($lane)
  #set lane_pcs_clk_src_muxout_pin_($lane)
  #set lane_pclk_out_div_src_flop_pin_($lane)
  #set lane_pclk_out_div_muxout_pin_($lane)

  puts "\[Constraints Debug\] Info: [file tail [info script]] 1 creating variables for important pins in design of pcs lane $lane of link $link_num"
  if { $hdmi_supported && $hdmi_54b_support } {
   set max_pclk_int_div_scan_mux_datain_($lane) [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/max_pclk_int_div_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
   set mpll_hdmi_clk_gate_out_pin_($lane)    [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_hdmi_clk_gate/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  }
  if { $hdmi_supported && $hdmi_2p1_ctrl } {
   set scan_mux_prepclk_pclk_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set prepclk_pclk_div_pin_($lane)       [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/bcm_flop_inst_2/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
   set prepclk_pclk_scan_stop_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pclk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set scan_mux_prepclk_10ui_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set prepclk_mpll_10ui_clk_div_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/bcm_flop_inst_2/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
   set prepclk_mpll_10ui_clk_stop_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_10ui_clk_div/lane_hdmi_prepclk_mux_2/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
  }
  set pma_clk_nonsds_scan_mux_outpin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set pcs_clk_nonsds_scan_mux_outpin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set mpll_clk_buf_inst_($lane)               [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_clk_buf_inst/bcm_ck_buf_inst/$ck_buf_src_inst_name/$ck_buf_src_clk_out_pin]]
  set protocol_mpll_mux_outpin_($lane)        [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_clk_mux_hand_0/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  if { !$perlink_clk_arch } {
   set mpll_glcm1_out_($lane)                 [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set mpll_glcm2_out_($lane)                 [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set lane_mpll_word_clk_src_pin_($lane)     [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_z_pin]]
   set lane_mpll_div_clk_src_pin_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_z_pin]]
   set lane_mpll_word_clk_src_pin_($lane)     [get_driver_cell_pin [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/Y]]]
  } else {
   set mpll_glcm1_out_($lane)                 [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set mpll_glcm2_out_($lane)                 [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set lane_mpll_word_clk_src_pin_($lane)     [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mpll_word_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_z_pin]]
   set lane_mpll_div_clk_src_pin_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/mplla_clk_data_mux2/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_z_pin]]
  }
  set lane_mpll_pclk_mux_d0pin_($lane)        [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_mpll_pclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
  set lane_mpll_pclk_mux_outpin_($lane)       [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_mpll_pclk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set lane_pma_clk_src_flop_pin_($lane)       [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pma_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
  set lane_pma_clk_src_icg_pin_($lane)        [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pma_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  set lane_pma_clk_src_muxout_pin_($lane)     [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pma_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set lane_pcs_clk_src_flop_pin_($lane)       [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pcs_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
  set lane_pcs_clk_src_icg_pin_($lane)        [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pcs_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  set lane_pcs_clk_src_muxout_pin_($lane)     [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pcs_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set lane_int_flop_pin_($lane)               [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_${pclk_out_name}_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
  set lane_int_muxout_pin_($lane)             [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_${pclk_out_name}_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  set lane_int_icg_pin_($lane)                [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_${pclk_out_name}_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  if { $pclk_as_phy_input } {
   set max_pclk_glcm_out_($lane)              [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pllclk_refclk_sel_inst/pipe_clk_mux2_inst/scan_clkout_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set lane_max_div_scan_muxout_pin_($lane)   [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/max_pclk_int_div_scan_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set pclk_nonsds_scan_mux_data_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pclk_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
   set pclk_nonsds_scan_mux_outpin_($lane)    [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pclk_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set pclk_nonsds_scan_mux_scan_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pclk_nonsds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set pma_clk_sds_scan_mux_scan_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set pcs_clk_sds_scan_mux_scan_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk1_pin]]
   set pma_clk_sds_scan_mux_data_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
   set pcs_clk_sds_scan_mux_data_pin_($lane)  [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
   set pma_clk_sds_scan_mux_outpin_($lane)    [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pma_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set pcs_clk_sds_scan_mux_outpin_($lane)    [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/lane_pcs_sds_clk_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set lane_max_pclk_glcm_or_pin_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/pllclk_refclk_sel_inst/pipe_clk_mux2_inst/clka_or_clkb_hand_gen_or/bcm_ck_or_inst/$ck_or_src_inst_name/$ck_or_src_clk_z_pin]]
   set lane_max_pclk_int_flop_pin_($lane)     [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_max_pclk_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
   set lane_max_pclk_int_icg_pin_($lane)      [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_max_pclk_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
   set lane_max_pclk_int_muxout_pin_($lane)   [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_max_pclk_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
  } else {
   set lane_pclk_src_muxout_pin_($lane)       [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pclk_inst/gen_clk_out_0__clk_out_mux/bcm_ck_mx_inst/$ck_mx_src_inst_name/$ck_mx_src_clk_out_pin]]
   set lane_pclk_src_flop_pin_($lane)         [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pclk_inst/gen_clk_out_0__bcm_flop_inst/$ck_dff_clrn_src_inst_name/$ck_dff_clrn_src_q_pin]]
   set lane_pclk_src_icg_pin_($lane)          [get_pins [prefixing $hiervar pcs/upcs_clk_ctl/clk_ctl_${lane}_/clk_div_flop_base_pclk_inst/clk_in_gate_inst/hand_clk_gate/bcm_ck_gt_inst/$ck_gt_lat_src_inst_name/$ck_gt_lat_src_clk_out_pin]]
  }
 }
 foreach lane $pcs_lanes_in_link($link_num) {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 2 creating variables for important pins in design of clock controller $lane of link $link_num"
  if { !$tx_only_supported} {
   set rx_clk_buf_inst_($lane)               [get_pins [prefixing $hiervar pcs/lane${lane}/rx/rx_nonsds_clk_buf_inst/bcm_ck_buf_inst/$ck_buf_src_inst_name/$ck_buf_src_clk_out_pin]]
   set sds_rx_clk_buf_inst_($lane)           [get_pins [prefixing $hiervar pcs/lane${lane}/rx/lane_rx_serdes/rx_pcs_clk_buf_inst/bcm_ck_buf_inst/$ck_buf_src_inst_name/$ck_buf_src_clk_out_pin]]
  }
 }
}

# Common per PHY
for {set phy 0} {$phy < $nphys} {incr phy} {
 puts "\[Constraints Debug\] Info: [file tail [info script]] 3 creating variables for important pins in design of phy $phy"
 set jtag_clk_p_n_src_pin_($phy) [get_pins [prefixing $hiervar phy${phy}/pcs_raw/aon/aon_cmn/jtag_clk_n_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
 foreach lane $phy_tx_lane_list {
  puts "\[Constraints Debug\] Info: [file tail [info script]] 4 creating variables for important pins in design of tx $lane of phy $phy"
  set clk_func_txX_clk_d0pin_($lane)     [get_pins [prefixing $hiervar phy${phy}/pcs_raw/lane${lane}_tx/tx_fw_xface/tx_clk_s_scan_mux/bcm_ck_mux/$ck_mx_src_inst_name/$ck_mx_src_clk0_pin]]
 }
}

# UPCS common scan clocks
if { $pcie_supported } {
 if { $nphys == 1 } {
  set scan_shift_clk_list [list [prefixing $hiervar_ pcs_scan_clk] [prefixing $hiervar_ phy0_scan_clk]]
 } elseif { $nphys == 2 } {
  set scan_shift_clk_list [list [prefixing $hiervar_ pcs_scan_clk] [prefixing $hiervar_ phy0_scan_clk] [prefixing $hiervar_ phy1_scan_clk]]
 } elseif { $nphys == 4 } {
  set scan_shift_clk_list [list [prefixing $hiervar_ pcs_scan_clk] \
                               [prefixing $hiervar_ phy0_scan_clk] \
                               [prefixing $hiervar_ phy1_scan_clk] \
                               [prefixing $hiervar_ phy2_scan_clk] \
                               [prefixing $hiervar_ phy3_scan_clk]]
 }
} else {
 set scan_shift_clk_list [list [prefixing $hiervar_ pcs_scan_clk] [prefixing $hiervar_ phy0_scan_clk]]
}

