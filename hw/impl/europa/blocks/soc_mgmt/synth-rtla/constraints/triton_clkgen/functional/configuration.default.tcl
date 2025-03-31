# (C) Copyright Axelera AI 2023
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: auto generated default configuration file for the constraints of triton_clock_gen_p
# Owners: Jeroen Vermeeren, Spyridoula Koumousi, Roel Uytterhoeven 

#-------------------------------------------------------------------------------
# Design parameters
#-------------------------------------------------------------------------------
set DESIGN_NAME triton_clock_gen_p
set CORNER      default
# Set the hierarchical path for this ip to "" when not set from a higher level.
if { ![info exists HIER_PATH_triton_clock_gen] } {
    set HIER_PATH_triton_clock_gen ""
}

#-------------------------------------------------------------------------------
# Derate parameters
#-------------------------------------------------------------------------------
set triton_clock_gen_p(${CORNER},derate,clock_early)     -0.025
set triton_clock_gen_p(${CORNER},derate,clock_late)      0.025
set triton_clock_gen_p(${CORNER},derate,data_early)      -0.025
set triton_clock_gen_p(${CORNER},derate,data_late)       0.025

set triton_clock_gen_p(${CORNER},derate,clock_early,SVT16) -0.025
set triton_clock_gen_p(${CORNER},derate,clock_late,SVT16)  0.025
set triton_clock_gen_p(${CORNER},derate,data_early,SVT16)  -0.025
set triton_clock_gen_p(${CORNER},derate,data_late,SVT16)   0.025
set triton_clock_gen_p(${CORNER},derate,clock_early,LVT16) -0.025
set triton_clock_gen_p(${CORNER},derate,clock_late,LVT16)  0.025
set triton_clock_gen_p(${CORNER},derate,data_early,LVT16)  -0.025
set triton_clock_gen_p(${CORNER},derate,data_late,LVT16)   0.025
set triton_clock_gen_p(${CORNER},derate,clock_early,ULT16) -0.025
set triton_clock_gen_p(${CORNER},derate,clock_late,ULT16)  0.025
set triton_clock_gen_p(${CORNER},derate,data_early,ULT16)  -0.025
set triton_clock_gen_p(${CORNER},derate,data_late,ULT16)   0.025

set triton_clock_gen_p(${CORNER},derate,clock_early,net) -0.025
set triton_clock_gen_p(${CORNER},derate,clock_late,net) 0.025
set triton_clock_gen_p(${CORNER},derate,data_early,net) -0.025
set triton_clock_gen_p(${CORNER},derate,data_late,net) 0.025

#-------------------------------------------------------------------------------
# Uncertainty parameters
#-------------------------------------------------------------------------------
set triton_clock_gen_p(${CORNER},uncertainty,setup)              0.1
set triton_clock_gen_p(${CORNER},uncertainty,hold)              0.1

#-------------------------------------------------------------------------------
# Clock parameters
#-------------------------------------------------------------------------------
# Global clock scaling factor (forced to 1.0 if in primetime)
if { ![info exists GLOBAL_CLOCK_SCALING_FACTOR] || $synopsys_program_name == "pt_shell" || $synopsys_program_name == "ptc_shell" } {
    set GLOBAL_CLOCK_SCALING_FACTOR 1.0
}
# Functional clocks
# ------------------- clk ------------------- #
set triton_clock_gen_p(${CORNER},clk_port,clk,name)                    clk
set triton_clock_gen_p(${CORNER},clk_port,clk,period)                  [expr 10.000 * $GLOBAL_CLOCK_SCALING_FACTOR]
set triton_clock_gen_p(${CORNER},clk_port,clk,port_name)               clk
set triton_clock_gen_p(${CORNER},clk_port,clk,dc)                      0.5
set triton_clock_gen_p(${CORNER},clk_port,clk,latency_source_early)    0
set triton_clock_gen_p(${CORNER},clk_port,clk,latency_source_late)     0
set triton_clock_gen_p(${CORNER},clk_port,clk,latency_net_early)       0
set triton_clock_gen_p(${CORNER},clk_port,clk,latency_net_late)        0
set triton_clock_gen_p(${CORNER},clk_port,clk,tran_min)                 0.027
set triton_clock_gen_p(${CORNER},clk_port,clk,tran_max)                 0.081

# ------------------- test_clk_i ------------------- #
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,name)                    test_clk_i
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,period)                  [expr 10.000 * $GLOBAL_CLOCK_SCALING_FACTOR]
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,port_name)               test_clk_i
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,dc)                      0.5
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,latency_source_early)    0
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,latency_source_late)     0
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,latency_net_early)       0
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,latency_net_late)        0
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,tran_min)                 0.027
set triton_clock_gen_p(${CORNER},clk_port,test_clk_i,tran_max)                 0.081

# ------------------- freq_meter_ref_clk_i ------------------- #
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,name)                    freq_meter_ref_clk_i
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,period)                  [expr 50.000 * $GLOBAL_CLOCK_SCALING_FACTOR]
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,port_name)               freq_meter_ref_clk_i
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,dc)                      0.5
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,latency_source_early)    0
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,latency_source_late)     0
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,latency_net_early)       0
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,latency_net_late)        0
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,tran_min)                 0.027
set triton_clock_gen_p(${CORNER},clk_port,freq_meter_ref_clk_i,tran_max)                 0.081

# ------------------- jtag_tck ------------------- #
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,name)                    jtag_tck
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)                  [expr 10.000 * $GLOBAL_CLOCK_SCALING_FACTOR]
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,port_name)               jtag_tck
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,dc)                      0.5
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,latency_source_early)    0
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,latency_source_late)     0
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,latency_net_early)       0
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,latency_net_late)        0
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,tran_min)                 0.027
set triton_clock_gen_p(${CORNER},clk_port,jtag_tck,tran_max)                 0.081


#-------------------------------------------------------------------------------
# IO parameters
#-------------------------------------------------------------------------------
# ------------------- misc related ports ------------------- #
set triton_clock_gen_p(${CORNER},in_port,clk,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clk,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clk,driving_cell)              EDBSVT16_INV_6

set triton_clock_gen_p(${CORNER},in_port,rst_n,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,rst_n,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,rst_n,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,rst_n,dly_min)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,rst_n,dly_max)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,rst_n,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,rst_n,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,test_mode_i,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,dly_min)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,dly_max)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,test_mode_i,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,test_clk_i,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,test_clk_i,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,test_clk_i,driving_cell)              EDBSVT16_INV_6

set triton_clock_gen_p(${CORNER},in_port,freq_meter_ref_clk_i,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,freq_meter_ref_clk_i,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,freq_meter_ref_clk_i,driving_cell)              EDBSVT16_INV_6

set triton_clock_gen_p(${CORNER},out_port,fast_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,fast_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,fast_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,slow_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,slow_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,slow_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_core_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_core_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_core_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_axi_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_axi_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_axi_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_scan_atspeed_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_scan_atspeed_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_scan_atspeed_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pvt_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pvt_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pvt_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,debug_clk_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,debug_clk_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,debug_clk_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic_0_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_0_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_0_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic_0_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic_0_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic_1_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_1_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_1_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic_1_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic_1_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic_2_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_2_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_2_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic_2_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic_2_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic_3_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_3_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic_3_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic_3_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic_3_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_incr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_incr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_incr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_incr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_incr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic0_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic0_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic0_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic0_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic0_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic1_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic1_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic1_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic1_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic1_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic2_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic2_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic2_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic2_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic2_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic3_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic3_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic3_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic3_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic3_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_0_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_0_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_0_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_1_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_1_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_1_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_2_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_2_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_2_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_3_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_3_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_3_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_data_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_data_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_data_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_data_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_data_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_data_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_sclk_clk_en_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_clk_en_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_clk_en_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_clk_en_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_clk_en_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_fclk_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,sys_ctrl_sclk_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic0_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic0_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic0_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic0_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic0_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic1_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic1_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic1_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic1_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic1_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic2_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic2_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic2_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic2_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic2_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,aic3_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic3_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,aic3_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,aic3_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,aic3_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_0_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_1_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_2_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,l2_3_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_data_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_pcfg_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,pcie_dbi_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_data_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,ddr_pcfg_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_ctrl_clr_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_ctrl_clr_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_ctrl_clr_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_ctrl_clr_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,noc_sclk_cdiv_ctrl_clr_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,clock_gen_pll_lock_o,dly_min)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_pll_lock_o,dly_max)                  [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_pll_lock_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,clock_gen_pll_lock_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,clock_gen_pll_lock_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,clock_gen_obs_o,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,clock_gen_obs_o,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,clock_gen_obs_o,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},in_port,jtag_tck,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,jtag_tck,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,jtag_tck,driving_cell)              EDBSVT16_INV_6

set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,dly_min)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,dly_max)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,jtag_tdi,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},out_port,jtag_tdo,dly_min)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo,dly_max)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,jtag_tdo_en,dly_min)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo_en,dly_max)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo_en,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo_en,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,jtag_tdo_en,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},in_port,jtag_tms,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,dly_min)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,dly_max)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,jtag_tms,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,dly_min)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,dly_max)                   [expr 0.5*$triton_clock_gen_p(${CORNER},clk_port,jtag_tck,period)]
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,jtag_trst_n,annot_tran_max)            0.262

# ------------------- apb_v4 related ports ------------------- #
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_paddr,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwrite,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pwdata,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_psel,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pprot,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_penable,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,cap_min)                   0.00042
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,cap_max)                   0.00336
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,driving_cell)              EDBSVT16_INV_6
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,dly_min)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,dly_max)                   [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,annot_tran_min)            0.027
set triton_clock_gen_p(${CORNER},in_port,clock_gen_apb_v4_pstrb,annot_tran_max)            0.262

set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pslverr,dly_min)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pslverr,dly_max)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pslverr,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pslverr,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pslverr,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_prdata,dly_min)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_prdata,dly_max)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_prdata,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_prdata,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_prdata,tran_max)                 0.216

set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pready,dly_min)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pready,dly_max)                  [expr 0.25*$triton_clock_gen_p(${CORNER},clk_port,clk,period)]
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pready,load_min)                 0.00042
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pready,load_max)                 0.00672
set triton_clock_gen_p(${CORNER},out_port,clock_gen_apb_v4_pready,tran_max)                 0.216

