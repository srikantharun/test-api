############################################################################################
#
# dwc_c20pcie4_upcs_x4_ns_io_drive_load.tcl
#
# PIPE(UPCS+PHY) synthesis all driver cells and load parameters for io ports
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

########### Set boundary conditions for the design ###############
# For input ports, the driving cell is chosen to be a weak buffer #
# For output ports, a load value of 0.1pF is set                  #
###################################################################
# Scan Outputs
#set sync_sops []
#if { [is_port *pcs_*scan_*out*] } {
# set sync_sops  [add_to_collection $sync_sops  [get_ports *pcs_*scan_*out*]]
#}
#if { [is_port *raw_*_scan_*out*] } {
# set sync_sops  [add_to_collection $sync_sops  [get_ports *raw_*_scan_*out*]]
#}
#if { [is_port *phy*_*scan_*out*] } {
# set sync_sops  [add_to_collection $sync_sops  [get_ports *phy*_*scan_*out*]]
#}

#set driving cell for all input ports
set driving_cell      [get_weak_buffer_cell]
set driving_cell_pin  [get_lib_cell_out_pin $driving_cell]
set exclude_ports [get_ports * -filter "direction==inout"]   ;#Exclude ANA inout ports
##Excluding some ANA pins which require high capcitance drive strength
set exclude_ports [add_to_collection $exclude_ports [get_ports -quiet [list phy?_ref_pad_clk_? phy?_ref_alt_clk_? phy_tx*_flyover_data_? tx?_p tx?_m ]]]
if { $dwc_dpalt_phy } {
 set exclude_ports [add_to_collection $exclude_ports [get_ports -quiet [list txrx?_p txrx?_m ]]]
} else {
 set exclude_ports [add_to_collection $exclude_ports [get_ports -quiet [list rx?_p rx?_m ]]]
}
set_driving_cell -lib_cell $driving_cell -pin $driving_cell_pin [remove_from_collection [get_ports [all_inputs]] $exclude_ports]
# set load value for all output ports
set_load [expr 0.1*$TUNIT]   [remove_from_collection [all_outputs] $sync_sops]
set_load [expr 0.001*$TUNIT] $sync_sops
#################################################################

