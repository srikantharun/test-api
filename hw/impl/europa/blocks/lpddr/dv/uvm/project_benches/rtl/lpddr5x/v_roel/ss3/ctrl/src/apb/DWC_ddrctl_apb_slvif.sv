// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddrctl_apb_slvif.sv#18 $
`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"

module DWC_ddrctl_apb_slvif
import DWC_ddrctl_reg_pkg::*;
  #(parameter APB_AW = 16,
    parameter APB_DW = 32,
    parameter RW_REGS = `UMCTL2_REGS_RW_REGS,
    parameter REG_WIDTH = 32,
    parameter RWSELWIDTH = RW_REGS
    )
   (input                     pclk
    ,input                     presetn
    ,input [APB_DW-1:0]        pwdata
    ,input [RWSELWIDTH-1:0]    rwselect
    ,input                     write_en
    ,input                     store_rqst
    // static registers write enable
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block.
    ,input               static_wr_en_aclk_0
    ,input               quasi_dyn_wr_en_aclk_0
//spyglass enable_block W240
    ,input               static_wr_en_core_ddrc_core_clk
    ,input               quasi_dyn_wr_en_core_ddrc_core_clk
//`ifdef UMCTL2_OCECC_EN_1    
//    ,input               quasi_dyn_wr_en_pclk
//`endif // UMCTL2_OCPAR_OR_OCECC_EN_1 
    //----------------------------------
   ,output reg [REG_WIDTH -1:0] r0_mstr0
   ,output reg [REG_WIDTH -1:0] r2_mstr2
   ,output reg [REG_WIDTH -1:0] r4_mstr4
   ,output reg [REG_WIDTH -1:0] r8_mrctrl0
   ,input reg_ddrc_mrr_done_clr_ack_pclk
   ,input reg_ddrc_mr_wr_ack_pclk
   ,output reg ff_regb_ddrc_ch0_mr_wr_saved
   ,output reg [REG_WIDTH -1:0] r9_mrctrl1
   ,input ddrc_reg_mr_wr_busy_int
   ,output reg [REG_WIDTH -1:0] r14_deratectl0
   ,output reg [REG_WIDTH -1:0] r15_deratectl1
   ,output reg [REG_WIDTH -1:0] r16_deratectl2
   ,output reg [REG_WIDTH -1:0] r19_deratectl5
   ,input reg_ddrc_derate_temp_limit_intr_clr_ack_pclk
   ,input reg_ddrc_derate_temp_limit_intr_force_ack_pclk
   ,output reg [REG_WIDTH -1:0] r20_deratectl6
   ,output reg [REG_WIDTH -1:0] r24_deratedbgctl
   ,output reg [REG_WIDTH -1:0] r26_pwrctl
   ,output reg [REG_WIDTH -1:0] r27_hwlpctl
   ,output reg [REG_WIDTH -1:0] r29_clkgatectl
   ,output reg [REG_WIDTH -1:0] r30_rfshmod0
   ,output reg [REG_WIDTH -1:0] r32_rfshctl0
   ,output reg [REG_WIDTH -1:0] r33_rfmmod0
   ,output reg [REG_WIDTH -1:0] r34_rfmmod1
   ,output reg [REG_WIDTH -1:0] r35_rfmctl
   ,output reg [REG_WIDTH -1:0] r37_zqctl0
   ,output reg [REG_WIDTH -1:0] r38_zqctl1
   ,input reg_ddrc_zq_reset_ack_pclk
   ,output reg ff_regb_ddrc_ch0_zq_reset_saved
   ,output reg [REG_WIDTH -1:0] r39_zqctl2
   ,input ddrc_reg_zq_reset_busy_int
   ,output reg [REG_WIDTH -1:0] r41_dqsoscruntime
   ,output reg [REG_WIDTH -1:0] r43_dqsosccfg0
   ,output reg [REG_WIDTH -1:0] r45_sched0
   ,output reg [REG_WIDTH -1:0] r46_sched1
   ,output reg [REG_WIDTH -1:0] r48_sched3
   ,output reg [REG_WIDTH -1:0] r49_sched4
   ,output reg [REG_WIDTH -1:0] r50_sched5
   ,output reg [REG_WIDTH -1:0] r51_hwffcctl
   ,output reg [REG_WIDTH -1:0] r62_dfilpcfg0
   ,output reg [REG_WIDTH -1:0] r63_dfiupd0
   ,output reg [REG_WIDTH -1:0] r65_dfimisc
   ,output reg [REG_WIDTH -1:0] r67_dfiphymstr
   ,output reg [REG_WIDTH -1:0] r77_poisoncfg
   ,input reg_ddrc_wr_poison_intr_clr_ack_pclk
   ,input reg_ddrc_rd_poison_intr_clr_ack_pclk
   ,output reg [REG_WIDTH -1:0] r79_ecccfg0
   ,output reg [REG_WIDTH -1:0] r80_ecccfg1
   ,output reg [REG_WIDTH -1:0] r82_eccctl
   ,input reg_ddrc_ecc_corrected_err_clr_ack_pclk
   ,input reg_ddrc_ecc_uncorrected_err_clr_ack_pclk
   ,input reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk
   ,input reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk
   ,input reg_ddrc_ecc_ap_err_intr_clr_ack_pclk
   ,input reg_ddrc_ecc_corrected_err_intr_force_ack_pclk
   ,input reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk
   ,input reg_ddrc_ecc_ap_err_intr_force_ack_pclk
   ,output reg [REG_WIDTH -1:0] r97_eccpoisonaddr0
   ,output reg [REG_WIDTH -1:0] r98_eccpoisonaddr1
   ,output reg [REG_WIDTH -1:0] r101_eccpoisonpat0
   ,output reg [REG_WIDTH -1:0] r103_eccpoisonpat2
   ,output reg [REG_WIDTH -1:0] r161_lnkeccctl1
   ,input reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk
   ,input reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk
   ,input reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk
   ,input reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk
   ,input reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk
   ,input reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk
   ,output reg [REG_WIDTH -1:0] r162_lnkeccpoisonctl0
   ,output reg [REG_WIDTH -1:0] r164_lnkeccindex
   ,output reg [REG_WIDTH -1:0] r234_opctrl0
   ,output reg [REG_WIDTH -1:0] r235_opctrl1
   ,output reg [REG_WIDTH -1:0] r237_opctrlcmd
   ,input reg_ddrc_zq_calib_short_ack_pclk
   ,output reg ff_regb_ddrc_ch0_zq_calib_short_saved
   ,input reg_ddrc_ctrlupd_ack_pclk
   ,output reg ff_regb_ddrc_ch0_ctrlupd_saved
   ,input ddrc_reg_zq_calib_short_busy_int
   ,input ddrc_reg_ctrlupd_busy_int
   ,output reg [REG_WIDTH -1:0] r240_oprefctrl0
   ,input reg_ddrc_rank0_refresh_ack_pclk
   ,output reg ff_regb_ddrc_ch0_rank0_refresh_saved
   ,input reg_ddrc_rank1_refresh_ack_pclk
   ,output reg ff_regb_ddrc_ch0_rank1_refresh_saved
   ,input ddrc_reg_rank0_refresh_busy_int
   ,input ddrc_reg_rank1_refresh_busy_int
   ,output reg [REG_WIDTH -1:0] r249_swctl
   ,output reg [REG_WIDTH -1:0] r253_rankctl
   ,output reg [REG_WIDTH -1:0] r254_dbictl
   ,output reg [REG_WIDTH -1:0] r256_odtmap
   ,output reg [REG_WIDTH -1:0] r257_datactl0
   ,output reg [REG_WIDTH -1:0] r258_swctlstatic
   ,output reg [REG_WIDTH -1:0] r259_cgctl
   ,output reg [REG_WIDTH -1:0] r260_inittmg0
   ,output reg [REG_WIDTH -1:0] r285_ppt2ctrl0
   ,input reg_ddrc_ppt2_burst_ack_pclk
   ,output reg ff_regb_ddrc_ch0_ppt2_burst_saved
   ,input ddrc_reg_ppt2_burst_busy_int
   ,output reg [REG_WIDTH -1:0] r495_addrmap1_map0
   ,output reg [REG_WIDTH -1:0] r497_addrmap3_map0
   ,output reg [REG_WIDTH -1:0] r498_addrmap4_map0
   ,output reg [REG_WIDTH -1:0] r499_addrmap5_map0
   ,output reg [REG_WIDTH -1:0] r500_addrmap6_map0
   ,output reg [REG_WIDTH -1:0] r501_addrmap7_map0
   ,output reg [REG_WIDTH -1:0] r502_addrmap8_map0
   ,output reg [REG_WIDTH -1:0] r503_addrmap9_map0
   ,output reg [REG_WIDTH -1:0] r504_addrmap10_map0
   ,output reg [REG_WIDTH -1:0] r505_addrmap11_map0
   ,output reg [REG_WIDTH -1:0] r506_addrmap12_map0
   ,output reg [REG_WIDTH -1:0] r521_pccfg_port0
   ,output reg [REG_WIDTH -1:0] r522_pcfgr_port0
   ,output reg [REG_WIDTH -1:0] r523_pcfgw_port0
   ,output reg [REG_WIDTH -1:0] r556_pctrl_port0
   ,output reg [REG_WIDTH -1:0] r557_pcfgqos0_port0
   ,output reg [REG_WIDTH -1:0] r558_pcfgqos1_port0
   ,output reg [REG_WIDTH -1:0] r559_pcfgwqos0_port0
   ,output reg [REG_WIDTH -1:0] r560_pcfgwqos1_port0
   ,output reg [REG_WIDTH -1:0] r569_sbrctl_port0
   ,output reg [REG_WIDTH -1:0] r571_sbrwdata0_port0
   ,output reg [REG_WIDTH -1:0] r573_sbrstart0_port0
   ,output reg [REG_WIDTH -1:0] r574_sbrstart1_port0
   ,output reg [REG_WIDTH -1:0] r575_sbrrange0_port0
   ,output reg [REG_WIDTH -1:0] r576_sbrrange1_port0
   ,output reg [REG_WIDTH -1:0] r1929_dramset1tmg0_freq0
   ,output reg [REG_WIDTH -1:0] r1930_dramset1tmg1_freq0
   ,output reg [REG_WIDTH -1:0] r1931_dramset1tmg2_freq0
   ,output reg [REG_WIDTH -1:0] r1932_dramset1tmg3_freq0
   ,output reg [REG_WIDTH -1:0] r1933_dramset1tmg4_freq0
   ,output reg [REG_WIDTH -1:0] r1934_dramset1tmg5_freq0
   ,output reg [REG_WIDTH -1:0] r1935_dramset1tmg6_freq0
   ,output reg [REG_WIDTH -1:0] r1936_dramset1tmg7_freq0
   ,output reg [REG_WIDTH -1:0] r1938_dramset1tmg9_freq0
   ,output reg [REG_WIDTH -1:0] r1941_dramset1tmg12_freq0
   ,output reg [REG_WIDTH -1:0] r1942_dramset1tmg13_freq0
   ,output reg [REG_WIDTH -1:0] r1943_dramset1tmg14_freq0
   ,output reg [REG_WIDTH -1:0] r1946_dramset1tmg17_freq0
   ,output reg [REG_WIDTH -1:0] r1951_dramset1tmg23_freq0
   ,output reg [REG_WIDTH -1:0] r1952_dramset1tmg24_freq0
   ,output reg [REG_WIDTH -1:0] r1953_dramset1tmg25_freq0
   ,output reg [REG_WIDTH -1:0] r1958_dramset1tmg30_freq0
   ,output reg [REG_WIDTH -1:0] r1960_dramset1tmg32_freq0
   ,output reg [REG_WIDTH -1:0] r1991_initmr0_freq0
   ,output reg [REG_WIDTH -1:0] r1992_initmr1_freq0
   ,output reg [REG_WIDTH -1:0] r1993_initmr2_freq0
   ,output reg [REG_WIDTH -1:0] r1994_initmr3_freq0
   ,output reg [REG_WIDTH -1:0] r1995_dfitmg0_freq0
   ,output reg [REG_WIDTH -1:0] r1996_dfitmg1_freq0
   ,output reg [REG_WIDTH -1:0] r1997_dfitmg2_freq0
   ,output reg [REG_WIDTH -1:0] r1999_dfitmg4_freq0
   ,output reg [REG_WIDTH -1:0] r2000_dfitmg5_freq0
   ,output reg [REG_WIDTH -1:0] r2001_dfitmg6_freq0
   ,output reg [REG_WIDTH -1:0] r2003_dfilptmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2004_dfilptmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2005_dfiupdtmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2006_dfiupdtmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2008_dfiupdtmg2_freq0
   ,output reg [REG_WIDTH -1:0] r2009_dfiupdtmg3_freq0
   ,output reg [REG_WIDTH -1:0] r2010_rfshset1tmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2011_rfshset1tmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2012_rfshset1tmg2_freq0
   ,output reg [REG_WIDTH -1:0] r2013_rfshset1tmg3_freq0
   ,output reg [REG_WIDTH -1:0] r2014_rfshset1tmg4_freq0
   ,output reg [REG_WIDTH -1:0] r2024_rfmset1tmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2035_zqset1tmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2036_zqset1tmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2037_zqset1tmg2_freq0
   ,output reg [REG_WIDTH -1:0] r2046_dqsoscctl0_freq0
   ,output reg [REG_WIDTH -1:0] r2047_derateint_freq0
   ,output reg [REG_WIDTH -1:0] r2048_derateval0_freq0
   ,output reg [REG_WIDTH -1:0] r2049_derateval1_freq0
   ,output reg [REG_WIDTH -1:0] r2050_hwlptmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2051_dvfsctl0_freq0
   ,output reg [REG_WIDTH -1:0] r2052_schedtmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2053_perfhpr1_freq0
   ,output reg [REG_WIDTH -1:0] r2054_perflpr1_freq0
   ,output reg [REG_WIDTH -1:0] r2055_perfwr1_freq0
   ,output reg [REG_WIDTH -1:0] r2056_tmgcfg_freq0
   ,output reg [REG_WIDTH -1:0] r2057_ranktmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2058_ranktmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2059_pwrtmg_freq0
   ,output reg [REG_WIDTH -1:0] r2065_ddr4pprtmg0_freq0
   ,output reg [REG_WIDTH -1:0] r2066_ddr4pprtmg1_freq0
   ,output reg [REG_WIDTH -1:0] r2067_lnkeccctl0_freq0
   ,output reg [REG_WIDTH -1:0] r2201_dramset1tmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2202_dramset1tmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2203_dramset1tmg2_freq1
   ,output reg [REG_WIDTH -1:0] r2204_dramset1tmg3_freq1
   ,output reg [REG_WIDTH -1:0] r2205_dramset1tmg4_freq1
   ,output reg [REG_WIDTH -1:0] r2206_dramset1tmg5_freq1
   ,output reg [REG_WIDTH -1:0] r2207_dramset1tmg6_freq1
   ,output reg [REG_WIDTH -1:0] r2208_dramset1tmg7_freq1
   ,output reg [REG_WIDTH -1:0] r2210_dramset1tmg9_freq1
   ,output reg [REG_WIDTH -1:0] r2213_dramset1tmg12_freq1
   ,output reg [REG_WIDTH -1:0] r2214_dramset1tmg13_freq1
   ,output reg [REG_WIDTH -1:0] r2215_dramset1tmg14_freq1
   ,output reg [REG_WIDTH -1:0] r2218_dramset1tmg17_freq1
   ,output reg [REG_WIDTH -1:0] r2223_dramset1tmg23_freq1
   ,output reg [REG_WIDTH -1:0] r2224_dramset1tmg24_freq1
   ,output reg [REG_WIDTH -1:0] r2225_dramset1tmg25_freq1
   ,output reg [REG_WIDTH -1:0] r2230_dramset1tmg30_freq1
   ,output reg [REG_WIDTH -1:0] r2232_dramset1tmg32_freq1
   ,output reg [REG_WIDTH -1:0] r2263_initmr0_freq1
   ,output reg [REG_WIDTH -1:0] r2264_initmr1_freq1
   ,output reg [REG_WIDTH -1:0] r2265_initmr2_freq1
   ,output reg [REG_WIDTH -1:0] r2266_initmr3_freq1
   ,output reg [REG_WIDTH -1:0] r2267_dfitmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2268_dfitmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2269_dfitmg2_freq1
   ,output reg [REG_WIDTH -1:0] r2271_dfitmg4_freq1
   ,output reg [REG_WIDTH -1:0] r2272_dfitmg5_freq1
   ,output reg [REG_WIDTH -1:0] r2273_dfitmg6_freq1
   ,output reg [REG_WIDTH -1:0] r2275_dfiupdtmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2276_dfiupdtmg2_freq1
   ,output reg [REG_WIDTH -1:0] r2277_dfiupdtmg3_freq1
   ,output reg [REG_WIDTH -1:0] r2278_rfshset1tmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2279_rfshset1tmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2280_rfshset1tmg2_freq1
   ,output reg [REG_WIDTH -1:0] r2281_rfshset1tmg3_freq1
   ,output reg [REG_WIDTH -1:0] r2282_rfshset1tmg4_freq1
   ,output reg [REG_WIDTH -1:0] r2292_rfmset1tmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2303_zqset1tmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2304_zqset1tmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2305_zqset1tmg2_freq1
   ,output reg [REG_WIDTH -1:0] r2314_dqsoscctl0_freq1
   ,output reg [REG_WIDTH -1:0] r2315_derateint_freq1
   ,output reg [REG_WIDTH -1:0] r2316_derateval0_freq1
   ,output reg [REG_WIDTH -1:0] r2317_derateval1_freq1
   ,output reg [REG_WIDTH -1:0] r2318_hwlptmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2319_dvfsctl0_freq1
   ,output reg [REG_WIDTH -1:0] r2320_schedtmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2321_perfhpr1_freq1
   ,output reg [REG_WIDTH -1:0] r2322_perflpr1_freq1
   ,output reg [REG_WIDTH -1:0] r2323_perfwr1_freq1
   ,output reg [REG_WIDTH -1:0] r2324_tmgcfg_freq1
   ,output reg [REG_WIDTH -1:0] r2325_ranktmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2326_ranktmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2327_pwrtmg_freq1
   ,output reg [REG_WIDTH -1:0] r2333_ddr4pprtmg0_freq1
   ,output reg [REG_WIDTH -1:0] r2334_ddr4pprtmg1_freq1
   ,output reg [REG_WIDTH -1:0] r2335_lnkeccctl0_freq1
   ,output reg [REG_WIDTH -1:0] r2469_dramset1tmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2470_dramset1tmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2471_dramset1tmg2_freq2
   ,output reg [REG_WIDTH -1:0] r2472_dramset1tmg3_freq2
   ,output reg [REG_WIDTH -1:0] r2473_dramset1tmg4_freq2
   ,output reg [REG_WIDTH -1:0] r2474_dramset1tmg5_freq2
   ,output reg [REG_WIDTH -1:0] r2475_dramset1tmg6_freq2
   ,output reg [REG_WIDTH -1:0] r2476_dramset1tmg7_freq2
   ,output reg [REG_WIDTH -1:0] r2478_dramset1tmg9_freq2
   ,output reg [REG_WIDTH -1:0] r2481_dramset1tmg12_freq2
   ,output reg [REG_WIDTH -1:0] r2482_dramset1tmg13_freq2
   ,output reg [REG_WIDTH -1:0] r2483_dramset1tmg14_freq2
   ,output reg [REG_WIDTH -1:0] r2486_dramset1tmg17_freq2
   ,output reg [REG_WIDTH -1:0] r2491_dramset1tmg23_freq2
   ,output reg [REG_WIDTH -1:0] r2492_dramset1tmg24_freq2
   ,output reg [REG_WIDTH -1:0] r2493_dramset1tmg25_freq2
   ,output reg [REG_WIDTH -1:0] r2498_dramset1tmg30_freq2
   ,output reg [REG_WIDTH -1:0] r2500_dramset1tmg32_freq2
   ,output reg [REG_WIDTH -1:0] r2531_initmr0_freq2
   ,output reg [REG_WIDTH -1:0] r2532_initmr1_freq2
   ,output reg [REG_WIDTH -1:0] r2533_initmr2_freq2
   ,output reg [REG_WIDTH -1:0] r2534_initmr3_freq2
   ,output reg [REG_WIDTH -1:0] r2535_dfitmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2536_dfitmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2537_dfitmg2_freq2
   ,output reg [REG_WIDTH -1:0] r2539_dfitmg4_freq2
   ,output reg [REG_WIDTH -1:0] r2540_dfitmg5_freq2
   ,output reg [REG_WIDTH -1:0] r2541_dfitmg6_freq2
   ,output reg [REG_WIDTH -1:0] r2543_dfiupdtmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2544_dfiupdtmg2_freq2
   ,output reg [REG_WIDTH -1:0] r2545_dfiupdtmg3_freq2
   ,output reg [REG_WIDTH -1:0] r2546_rfshset1tmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2547_rfshset1tmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2548_rfshset1tmg2_freq2
   ,output reg [REG_WIDTH -1:0] r2549_rfshset1tmg3_freq2
   ,output reg [REG_WIDTH -1:0] r2550_rfshset1tmg4_freq2
   ,output reg [REG_WIDTH -1:0] r2560_rfmset1tmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2571_zqset1tmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2572_zqset1tmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2573_zqset1tmg2_freq2
   ,output reg [REG_WIDTH -1:0] r2582_dqsoscctl0_freq2
   ,output reg [REG_WIDTH -1:0] r2583_derateint_freq2
   ,output reg [REG_WIDTH -1:0] r2584_derateval0_freq2
   ,output reg [REG_WIDTH -1:0] r2585_derateval1_freq2
   ,output reg [REG_WIDTH -1:0] r2586_hwlptmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2587_dvfsctl0_freq2
   ,output reg [REG_WIDTH -1:0] r2588_schedtmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2589_perfhpr1_freq2
   ,output reg [REG_WIDTH -1:0] r2590_perflpr1_freq2
   ,output reg [REG_WIDTH -1:0] r2591_perfwr1_freq2
   ,output reg [REG_WIDTH -1:0] r2592_tmgcfg_freq2
   ,output reg [REG_WIDTH -1:0] r2593_ranktmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2594_ranktmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2595_pwrtmg_freq2
   ,output reg [REG_WIDTH -1:0] r2601_ddr4pprtmg0_freq2
   ,output reg [REG_WIDTH -1:0] r2602_ddr4pprtmg1_freq2
   ,output reg [REG_WIDTH -1:0] r2603_lnkeccctl0_freq2
   ,output reg [REG_WIDTH -1:0] r2737_dramset1tmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2738_dramset1tmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2739_dramset1tmg2_freq3
   ,output reg [REG_WIDTH -1:0] r2740_dramset1tmg3_freq3
   ,output reg [REG_WIDTH -1:0] r2741_dramset1tmg4_freq3
   ,output reg [REG_WIDTH -1:0] r2742_dramset1tmg5_freq3
   ,output reg [REG_WIDTH -1:0] r2743_dramset1tmg6_freq3
   ,output reg [REG_WIDTH -1:0] r2744_dramset1tmg7_freq3
   ,output reg [REG_WIDTH -1:0] r2746_dramset1tmg9_freq3
   ,output reg [REG_WIDTH -1:0] r2749_dramset1tmg12_freq3
   ,output reg [REG_WIDTH -1:0] r2750_dramset1tmg13_freq3
   ,output reg [REG_WIDTH -1:0] r2751_dramset1tmg14_freq3
   ,output reg [REG_WIDTH -1:0] r2754_dramset1tmg17_freq3
   ,output reg [REG_WIDTH -1:0] r2759_dramset1tmg23_freq3
   ,output reg [REG_WIDTH -1:0] r2760_dramset1tmg24_freq3
   ,output reg [REG_WIDTH -1:0] r2761_dramset1tmg25_freq3
   ,output reg [REG_WIDTH -1:0] r2766_dramset1tmg30_freq3
   ,output reg [REG_WIDTH -1:0] r2768_dramset1tmg32_freq3
   ,output reg [REG_WIDTH -1:0] r2799_initmr0_freq3
   ,output reg [REG_WIDTH -1:0] r2800_initmr1_freq3
   ,output reg [REG_WIDTH -1:0] r2801_initmr2_freq3
   ,output reg [REG_WIDTH -1:0] r2802_initmr3_freq3
   ,output reg [REG_WIDTH -1:0] r2803_dfitmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2804_dfitmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2805_dfitmg2_freq3
   ,output reg [REG_WIDTH -1:0] r2807_dfitmg4_freq3
   ,output reg [REG_WIDTH -1:0] r2808_dfitmg5_freq3
   ,output reg [REG_WIDTH -1:0] r2809_dfitmg6_freq3
   ,output reg [REG_WIDTH -1:0] r2811_dfiupdtmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2812_dfiupdtmg2_freq3
   ,output reg [REG_WIDTH -1:0] r2813_dfiupdtmg3_freq3
   ,output reg [REG_WIDTH -1:0] r2814_rfshset1tmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2815_rfshset1tmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2816_rfshset1tmg2_freq3
   ,output reg [REG_WIDTH -1:0] r2817_rfshset1tmg3_freq3
   ,output reg [REG_WIDTH -1:0] r2818_rfshset1tmg4_freq3
   ,output reg [REG_WIDTH -1:0] r2828_rfmset1tmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2839_zqset1tmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2840_zqset1tmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2841_zqset1tmg2_freq3
   ,output reg [REG_WIDTH -1:0] r2850_dqsoscctl0_freq3
   ,output reg [REG_WIDTH -1:0] r2851_derateint_freq3
   ,output reg [REG_WIDTH -1:0] r2852_derateval0_freq3
   ,output reg [REG_WIDTH -1:0] r2853_derateval1_freq3
   ,output reg [REG_WIDTH -1:0] r2854_hwlptmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2855_dvfsctl0_freq3
   ,output reg [REG_WIDTH -1:0] r2856_schedtmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2857_perfhpr1_freq3
   ,output reg [REG_WIDTH -1:0] r2858_perflpr1_freq3
   ,output reg [REG_WIDTH -1:0] r2859_perfwr1_freq3
   ,output reg [REG_WIDTH -1:0] r2860_tmgcfg_freq3
   ,output reg [REG_WIDTH -1:0] r2861_ranktmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2862_ranktmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2863_pwrtmg_freq3
   ,output reg [REG_WIDTH -1:0] r2869_ddr4pprtmg0_freq3
   ,output reg [REG_WIDTH -1:0] r2870_ddr4pprtmg1_freq3
   ,output reg [REG_WIDTH -1:0] r2871_lnkeccctl0_freq3


    );
  
   reg [APB_DW-1:0]         apb_data_r;
   reg [REG_WIDTH-1:0]      apb_data_expanded;

   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_lpddr4_mask;
   assign regb_ddrc_ch0_mstr0_lpddr4_mask = `REGB_DDRC_CH0_MSK_MSTR0_LPDDR4;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_lpddr5_mask;
   assign regb_ddrc_ch0_mstr0_lpddr5_mask = `REGB_DDRC_CH0_MSK_MSTR0_LPDDR5;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_lpddr5x_mask;
   assign regb_ddrc_ch0_mstr0_lpddr5x_mask = `REGB_DDRC_CH0_MSK_MSTR0_LPDDR5X;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_data_bus_width_mask;
   assign regb_ddrc_ch0_mstr0_data_bus_width_mask = `REGB_DDRC_CH0_MSK_MSTR0_DATA_BUS_WIDTH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_burst_rdwr_mask;
   assign regb_ddrc_ch0_mstr0_burst_rdwr_mask = `REGB_DDRC_CH0_MSK_MSTR0_BURST_RDWR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr0_active_ranks_mask;
   assign regb_ddrc_ch0_mstr0_active_ranks_mask = `REGB_DDRC_CH0_MSK_MSTR0_ACTIVE_RANKS;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr2_target_frequency_mask;
   assign regb_ddrc_ch0_mstr2_target_frequency_mask = `REGB_DDRC_CH0_MSK_MSTR2_TARGET_FREQUENCY;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr4_wck_on_mask;
   assign regb_ddrc_ch0_mstr4_wck_on_mask = `REGB_DDRC_CH0_MSK_MSTR4_WCK_ON;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr4_wck_suspend_en_mask;
   assign regb_ddrc_ch0_mstr4_wck_suspend_en_mask = `REGB_DDRC_CH0_MSK_MSTR4_WCK_SUSPEND_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mstr4_ws_off_en_mask;
   assign regb_ddrc_ch0_mstr4_ws_off_en_mask = `REGB_DDRC_CH0_MSK_MSTR4_WS_OFF_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_mr_type_mask;
   assign regb_ddrc_ch0_mrctrl0_mr_type_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_MR_TYPE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_sw_init_int_mask;
   assign regb_ddrc_ch0_mrctrl0_sw_init_int_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_SW_INIT_INT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_mr_rank_mask;
   assign regb_ddrc_ch0_mrctrl0_mr_rank_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_MR_RANK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_mr_addr_mask;
   assign regb_ddrc_ch0_mrctrl0_mr_addr_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_MR_ADDR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_mrr_done_clr_mask;
   assign regb_ddrc_ch0_mrctrl0_mrr_done_clr_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_MRR_DONE_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_dis_mrrw_trfc_mask;
   assign regb_ddrc_ch0_mrctrl0_dis_mrrw_trfc_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_DIS_MRRW_TRFC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_ppr_en_mask;
   assign regb_ddrc_ch0_mrctrl0_ppr_en_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_PPR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_ppr_pgmpst_en_mask;
   assign regb_ddrc_ch0_mrctrl0_ppr_pgmpst_en_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_PPR_PGMPST_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl0_mr_wr_mask;
   assign regb_ddrc_ch0_mrctrl0_mr_wr_mask = `REGB_DDRC_CH0_MSK_MRCTRL0_MR_WR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_mrctrl1_mr_data_mask;
   assign regb_ddrc_ch0_mrctrl1_mr_data_mask = `REGB_DDRC_CH0_MSK_MRCTRL1_MR_DATA;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_derate_enable_mask;
   assign regb_ddrc_ch0_deratectl0_derate_enable_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_DERATE_ENABLE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_lpddr4_refresh_mode_mask;
   assign regb_ddrc_ch0_deratectl0_lpddr4_refresh_mode_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_LPDDR4_REFRESH_MODE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_derate_mr4_pause_fc_mask;
   assign regb_ddrc_ch0_deratectl0_derate_mr4_pause_fc_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_DERATE_MR4_PAUSE_FC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_dis_trefi_x6x8_mask;
   assign regb_ddrc_ch0_deratectl0_dis_trefi_x6x8_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_DIS_TREFI_X6X8;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_dis_trefi_x0125_mask;
   assign regb_ddrc_ch0_deratectl0_dis_trefi_x0125_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_DIS_TREFI_X0125;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_temp_mask;
   assign regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_temp_mask = `REGB_DDRC_CH0_MSK_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl1_active_derate_byte_rank0_mask;
   assign regb_ddrc_ch0_deratectl1_active_derate_byte_rank0_mask = `REGB_DDRC_CH0_MSK_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl2_active_derate_byte_rank1_mask;
   assign regb_ddrc_ch0_deratectl2_active_derate_byte_rank1_mask = `REGB_DDRC_CH0_MSK_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_en_mask;
   assign regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_en_mask = `REGB_DDRC_CH0_MSK_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_clr_mask;
   assign regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_clr_mask = `REGB_DDRC_CH0_MSK_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_force_mask;
   assign regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_force_mask = `REGB_DDRC_CH0_MSK_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratectl6_derate_mr4_tuf_dis_mask;
   assign regb_ddrc_ch0_deratectl6_derate_mr4_tuf_dis_mask = `REGB_DDRC_CH0_MSK_DERATECTL6_DERATE_MR4_TUF_DIS;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_sel_mask;
   assign regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_sel_mask = `REGB_DDRC_CH0_MSK_DERATEDBGCTL_DBG_MR4_RANK_SEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_selfref_en_mask;
   assign regb_ddrc_ch0_pwrctl_selfref_en_mask = `REGB_DDRC_CH0_MSK_PWRCTL_SELFREF_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_powerdown_en_mask;
   assign regb_ddrc_ch0_pwrctl_powerdown_en_mask = `REGB_DDRC_CH0_MSK_PWRCTL_POWERDOWN_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_en_dfi_dram_clk_disable_mask;
   assign regb_ddrc_ch0_pwrctl_en_dfi_dram_clk_disable_mask = `REGB_DDRC_CH0_MSK_PWRCTL_EN_DFI_DRAM_CLK_DISABLE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_selfref_sw_mask;
   assign regb_ddrc_ch0_pwrctl_selfref_sw_mask = `REGB_DDRC_CH0_MSK_PWRCTL_SELFREF_SW;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_stay_in_selfref_mask;
   assign regb_ddrc_ch0_pwrctl_stay_in_selfref_mask = `REGB_DDRC_CH0_MSK_PWRCTL_STAY_IN_SELFREF;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_dis_cam_drain_selfref_mask;
   assign regb_ddrc_ch0_pwrctl_dis_cam_drain_selfref_mask = `REGB_DDRC_CH0_MSK_PWRCTL_DIS_CAM_DRAIN_SELFREF;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_lpddr4_sr_allowed_mask;
   assign regb_ddrc_ch0_pwrctl_lpddr4_sr_allowed_mask = `REGB_DDRC_CH0_MSK_PWRCTL_LPDDR4_SR_ALLOWED;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_pwrctl_dsm_en_mask;
   assign regb_ddrc_ch0_pwrctl_dsm_en_mask = `REGB_DDRC_CH0_MSK_PWRCTL_DSM_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwlpctl_hw_lp_en_mask;
   assign regb_ddrc_ch0_hwlpctl_hw_lp_en_mask = `REGB_DDRC_CH0_MSK_HWLPCTL_HW_LP_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwlpctl_hw_lp_exit_idle_en_mask;
   assign regb_ddrc_ch0_hwlpctl_hw_lp_exit_idle_en_mask = `REGB_DDRC_CH0_MSK_HWLPCTL_HW_LP_EXIT_IDLE_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_clkgatectl_bsm_clk_on_mask;
   assign regb_ddrc_ch0_clkgatectl_bsm_clk_on_mask = `REGB_DDRC_CH0_MSK_CLKGATECTL_BSM_CLK_ON;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshmod0_refresh_burst_mask;
   assign regb_ddrc_ch0_rfshmod0_refresh_burst_mask = `REGB_DDRC_CH0_MSK_RFSHMOD0_REFRESH_BURST;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshmod0_auto_refab_en_mask;
   assign regb_ddrc_ch0_rfshmod0_auto_refab_en_mask = `REGB_DDRC_CH0_MSK_RFSHMOD0_AUTO_REFAB_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshmod0_per_bank_refresh_mask;
   assign regb_ddrc_ch0_rfshmod0_per_bank_refresh_mask = `REGB_DDRC_CH0_MSK_RFSHMOD0_PER_BANK_REFRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_en_mask;
   assign regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_en_mask = `REGB_DDRC_CH0_MSK_RFSHMOD0_PER_BANK_REFRESH_OPT_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_en_mask;
   assign regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_en_mask = `REGB_DDRC_CH0_MSK_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshctl0_dis_auto_refresh_mask;
   assign regb_ddrc_ch0_rfshctl0_dis_auto_refresh_mask = `REGB_DDRC_CH0_MSK_RFSHCTL0_DIS_AUTO_REFRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfshctl0_refresh_update_level_mask;
   assign regb_ddrc_ch0_rfshctl0_refresh_update_level_mask = `REGB_DDRC_CH0_MSK_RFSHCTL0_REFRESH_UPDATE_LEVEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_rfm_en_mask;
   assign regb_ddrc_ch0_rfmmod0_rfm_en_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RFM_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_rfmsbc_mask;
   assign regb_ddrc_ch0_rfmmod0_rfmsbc_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RFMSBC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_raaimt_mask;
   assign regb_ddrc_ch0_rfmmod0_raaimt_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RAAIMT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_raamult_mask;
   assign regb_ddrc_ch0_rfmmod0_raamult_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RAAMULT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_raadec_mask;
   assign regb_ddrc_ch0_rfmmod0_raadec_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RAADEC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod0_rfmth_rm_thr_mask;
   assign regb_ddrc_ch0_rfmmod0_rfmth_rm_thr_mask = `REGB_DDRC_CH0_MSK_RFMMOD0_RFMTH_RM_THR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmmod1_init_raa_cnt_mask;
   assign regb_ddrc_ch0_rfmmod1_init_raa_cnt_mask = `REGB_DDRC_CH0_MSK_RFMMOD1_INIT_RAA_CNT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmctl_dbg_raa_rank_mask;
   assign regb_ddrc_ch0_rfmctl_dbg_raa_rank_mask = `REGB_DDRC_CH0_MSK_RFMCTL_DBG_RAA_RANK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rfmctl_dbg_raa_bg_bank_mask;
   assign regb_ddrc_ch0_rfmctl_dbg_raa_bg_bank_mask = `REGB_DDRC_CH0_MSK_RFMCTL_DBG_RAA_BG_BANK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_zqctl0_zq_resistor_shared_mask;
   assign regb_ddrc_ch0_zqctl0_zq_resistor_shared_mask = `REGB_DDRC_CH0_MSK_ZQCTL0_ZQ_RESISTOR_SHARED;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_zqctl0_dis_auto_zq_mask;
   assign regb_ddrc_ch0_zqctl0_dis_auto_zq_mask = `REGB_DDRC_CH0_MSK_ZQCTL0_DIS_AUTO_ZQ;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_zqctl1_zq_reset_mask;
   assign regb_ddrc_ch0_zqctl1_zq_reset_mask = `REGB_DDRC_CH0_MSK_ZQCTL1_ZQ_RESET;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_zqctl2_dis_srx_zqcl_mask;
   assign regb_ddrc_ch0_zqctl2_dis_srx_zqcl_mask = `REGB_DDRC_CH0_MSK_ZQCTL2_DIS_SRX_ZQCL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_zqctl2_dis_srx_zqcl_hwffc_mask;
   assign regb_ddrc_ch0_zqctl2_dis_srx_zqcl_hwffc_mask = `REGB_DDRC_CH0_MSK_ZQCTL2_DIS_SRX_ZQCL_HWFFC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dqsoscruntime_dqsosc_runtime_mask;
   assign regb_ddrc_ch0_dqsoscruntime_dqsosc_runtime_mask = `REGB_DDRC_CH0_MSK_DQSOSCRUNTIME_DQSOSC_RUNTIME;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dqsoscruntime_wck2dqo_runtime_mask;
   assign regb_ddrc_ch0_dqsoscruntime_wck2dqo_runtime_mask = `REGB_DDRC_CH0_MSK_DQSOSCRUNTIME_WCK2DQO_RUNTIME;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dqsosccfg0_dis_dqsosc_srx_mask;
   assign regb_ddrc_ch0_dqsosccfg0_dis_dqsosc_srx_mask = `REGB_DDRC_CH0_MSK_DQSOSCCFG0_DIS_DQSOSC_SRX;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_dis_opt_wrecc_collision_flush_mask;
   assign regb_ddrc_ch0_sched0_dis_opt_wrecc_collision_flush_mask = `REGB_DDRC_CH0_MSK_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_prefer_write_mask;
   assign regb_ddrc_ch0_sched0_prefer_write_mask = `REGB_DDRC_CH0_MSK_SCHED0_PREFER_WRITE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_pageclose_mask;
   assign regb_ddrc_ch0_sched0_pageclose_mask = `REGB_DDRC_CH0_MSK_SCHED0_PAGECLOSE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_opt_wrcam_fill_level_mask;
   assign regb_ddrc_ch0_sched0_opt_wrcam_fill_level_mask = `REGB_DDRC_CH0_MSK_SCHED0_OPT_WRCAM_FILL_LEVEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_dis_opt_ntt_by_act_mask;
   assign regb_ddrc_ch0_sched0_dis_opt_ntt_by_act_mask = `REGB_DDRC_CH0_MSK_SCHED0_DIS_OPT_NTT_BY_ACT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_dis_opt_ntt_by_pre_mask;
   assign regb_ddrc_ch0_sched0_dis_opt_ntt_by_pre_mask = `REGB_DDRC_CH0_MSK_SCHED0_DIS_OPT_NTT_BY_PRE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_autopre_rmw_mask;
   assign regb_ddrc_ch0_sched0_autopre_rmw_mask = `REGB_DDRC_CH0_MSK_SCHED0_AUTOPRE_RMW;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_lpr_num_entries_mask;
   assign regb_ddrc_ch0_sched0_lpr_num_entries_mask = `REGB_DDRC_CH0_MSK_SCHED0_LPR_NUM_ENTRIES;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_lpddr4_opt_act_timing_mask;
   assign regb_ddrc_ch0_sched0_lpddr4_opt_act_timing_mask = `REGB_DDRC_CH0_MSK_SCHED0_LPDDR4_OPT_ACT_TIMING;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_lpddr5_opt_act_timing_mask;
   assign regb_ddrc_ch0_sched0_lpddr5_opt_act_timing_mask = `REGB_DDRC_CH0_MSK_SCHED0_LPDDR5_OPT_ACT_TIMING;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_w_starve_free_running_mask;
   assign regb_ddrc_ch0_sched0_w_starve_free_running_mask = `REGB_DDRC_CH0_MSK_SCHED0_W_STARVE_FREE_RUNNING;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_opt_act_lat_mask;
   assign regb_ddrc_ch0_sched0_opt_act_lat_mask = `REGB_DDRC_CH0_MSK_SCHED0_OPT_ACT_LAT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_prefer_read_mask;
   assign regb_ddrc_ch0_sched0_prefer_read_mask = `REGB_DDRC_CH0_MSK_SCHED0_PREFER_READ;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_dis_speculative_act_mask;
   assign regb_ddrc_ch0_sched0_dis_speculative_act_mask = `REGB_DDRC_CH0_MSK_SCHED0_DIS_SPECULATIVE_ACT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched0_opt_vprw_sch_mask;
   assign regb_ddrc_ch0_sched0_opt_vprw_sch_mask = `REGB_DDRC_CH0_MSK_SCHED0_OPT_VPRW_SCH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_delay_switch_write_mask;
   assign regb_ddrc_ch0_sched1_delay_switch_write_mask = `REGB_DDRC_CH0_MSK_SCHED1_DELAY_SWITCH_WRITE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_visible_window_limit_wr_mask;
   assign regb_ddrc_ch0_sched1_visible_window_limit_wr_mask = `REGB_DDRC_CH0_MSK_SCHED1_VISIBLE_WINDOW_LIMIT_WR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_visible_window_limit_rd_mask;
   assign regb_ddrc_ch0_sched1_visible_window_limit_rd_mask = `REGB_DDRC_CH0_MSK_SCHED1_VISIBLE_WINDOW_LIMIT_RD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_page_hit_limit_wr_mask;
   assign regb_ddrc_ch0_sched1_page_hit_limit_wr_mask = `REGB_DDRC_CH0_MSK_SCHED1_PAGE_HIT_LIMIT_WR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_page_hit_limit_rd_mask;
   assign regb_ddrc_ch0_sched1_page_hit_limit_rd_mask = `REGB_DDRC_CH0_MSK_SCHED1_PAGE_HIT_LIMIT_RD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched1_opt_hit_gt_hpr_mask;
   assign regb_ddrc_ch0_sched1_opt_hit_gt_hpr_mask = `REGB_DDRC_CH0_MSK_SCHED1_OPT_HIT_GT_HPR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched3_wrcam_lowthresh_mask;
   assign regb_ddrc_ch0_sched3_wrcam_lowthresh_mask = `REGB_DDRC_CH0_MSK_SCHED3_WRCAM_LOWTHRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched3_wrcam_highthresh_mask;
   assign regb_ddrc_ch0_sched3_wrcam_highthresh_mask = `REGB_DDRC_CH0_MSK_SCHED3_WRCAM_HIGHTHRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched3_wr_pghit_num_thresh_mask;
   assign regb_ddrc_ch0_sched3_wr_pghit_num_thresh_mask = `REGB_DDRC_CH0_MSK_SCHED3_WR_PGHIT_NUM_THRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched3_rd_pghit_num_thresh_mask;
   assign regb_ddrc_ch0_sched3_rd_pghit_num_thresh_mask = `REGB_DDRC_CH0_MSK_SCHED3_RD_PGHIT_NUM_THRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched4_rd_act_idle_gap_mask;
   assign regb_ddrc_ch0_sched4_rd_act_idle_gap_mask = `REGB_DDRC_CH0_MSK_SCHED4_RD_ACT_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched4_wr_act_idle_gap_mask;
   assign regb_ddrc_ch0_sched4_wr_act_idle_gap_mask = `REGB_DDRC_CH0_MSK_SCHED4_WR_ACT_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched4_rd_page_exp_cycles_mask;
   assign regb_ddrc_ch0_sched4_rd_page_exp_cycles_mask = `REGB_DDRC_CH0_MSK_SCHED4_RD_PAGE_EXP_CYCLES;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched4_wr_page_exp_cycles_mask;
   assign regb_ddrc_ch0_sched4_wr_page_exp_cycles_mask = `REGB_DDRC_CH0_MSK_SCHED4_WR_PAGE_EXP_CYCLES;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched5_wrecc_cam_lowthresh_mask;
   assign regb_ddrc_ch0_sched5_wrecc_cam_lowthresh_mask = `REGB_DDRC_CH0_MSK_SCHED5_WRECC_CAM_LOWTHRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched5_wrecc_cam_highthresh_mask;
   assign regb_ddrc_ch0_sched5_wrecc_cam_highthresh_mask = `REGB_DDRC_CH0_MSK_SCHED5_WRECC_CAM_HIGHTHRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched5_dis_opt_loaded_wrecc_cam_fill_level_mask;
   assign regb_ddrc_ch0_sched5_dis_opt_loaded_wrecc_cam_fill_level_mask = `REGB_DDRC_CH0_MSK_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_sched5_dis_opt_valid_wrecc_cam_fill_level_mask;
   assign regb_ddrc_ch0_sched5_dis_opt_valid_wrecc_cam_fill_level_mask = `REGB_DDRC_CH0_MSK_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_hwffc_en_mask;
   assign regb_ddrc_ch0_hwffcctl_hwffc_en_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_HWFFC_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_init_fsp_mask;
   assign regb_ddrc_ch0_hwffcctl_init_fsp_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_INIT_FSP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_init_vrcg_mask;
   assign regb_ddrc_ch0_hwffcctl_init_vrcg_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_INIT_VRCG;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_target_vrcg_mask;
   assign regb_ddrc_ch0_hwffcctl_target_vrcg_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_TARGET_VRCG;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_skip_mrw_odtvref_mask;
   assign regb_ddrc_ch0_hwffcctl_skip_mrw_odtvref_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_SKIP_MRW_ODTVREF;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_skip_zq_stop_start_mask;
   assign regb_ddrc_ch0_hwffcctl_skip_zq_stop_start_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_SKIP_ZQ_STOP_START;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_zq_interval_mask;
   assign regb_ddrc_ch0_hwffcctl_zq_interval_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_ZQ_INTERVAL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_hwffcctl_hwffc_mode_mask;
   assign regb_ddrc_ch0_hwffcctl_hwffc_mode_mask = `REGB_DDRC_CH0_MSK_HWFFCCTL_HWFFC_MODE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pd_mask;
   assign regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pd_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_DFI_LP_EN_PD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_sr_mask;
   assign regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_sr_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_DFI_LP_EN_SR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsm_mask;
   assign regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsm_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_DFI_LP_EN_DSM;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_data_mask;
   assign regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_data_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_DFI_LP_EN_DATA;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_en_mask;
   assign regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_en_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_DFI_LP_DATA_REQ_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_data_mask;
   assign regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_data_mask = `REGB_DDRC_CH0_MSK_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiupd0_dfi_phyupd_en_mask;
   assign regb_ddrc_ch0_dfiupd0_dfi_phyupd_en_mask = `REGB_DDRC_CH0_MSK_DFIUPD0_DFI_PHYUPD_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srx_mask;
   assign regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srx_mask = `REGB_DDRC_CH0_MSK_DFIUPD0_CTRLUPD_PRE_SRX;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srx_mask;
   assign regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srx_mask = `REGB_DDRC_CH0_MSK_DFIUPD0_DIS_AUTO_CTRLUPD_SRX;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_mask;
   assign regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_mask = `REGB_DDRC_CH0_MSK_DFIUPD0_DIS_AUTO_CTRLUPD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_init_complete_en_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_init_complete_en_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_INIT_COMPLETE_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_phy_dbi_mode_mask;
   assign regb_ddrc_ch0_dfimisc_phy_dbi_mode_mask = `REGB_DDRC_CH0_MSK_DFIMISC_PHY_DBI_MODE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_data_cs_polarity_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_data_cs_polarity_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_DATA_CS_POLARITY;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_reset_n_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_reset_n_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_RESET_N;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_init_start_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_init_start_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_INIT_START;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_lp_optimized_write_mask;
   assign regb_ddrc_ch0_dfimisc_lp_optimized_write_mask = `REGB_DDRC_CH0_MSK_DFIMISC_LP_OPTIMIZED_WRITE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_frequency_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_frequency_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_FREQUENCY;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_freq_fsp_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_freq_fsp_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_FREQ_FSP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfimisc_dfi_channel_mode_mask;
   assign regb_ddrc_ch0_dfimisc_dfi_channel_mode_mask = `REGB_DDRC_CH0_MSK_DFIMISC_DFI_CHANNEL_MODE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiphymstr_dfi_phymstr_en_mask;
   assign regb_ddrc_ch0_dfiphymstr_dfi_phymstr_en_mask = `REGB_DDRC_CH0_MSK_DFIPHYMSTR_DFI_PHYMSTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32_mask;
   assign regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32_mask = `REGB_DDRC_CH0_MSK_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_wr_poison_slverr_en_mask;
   assign regb_ddrc_ch0_poisoncfg_wr_poison_slverr_en_mask = `REGB_DDRC_CH0_MSK_POISONCFG_WR_POISON_SLVERR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_wr_poison_intr_en_mask;
   assign regb_ddrc_ch0_poisoncfg_wr_poison_intr_en_mask = `REGB_DDRC_CH0_MSK_POISONCFG_WR_POISON_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_wr_poison_intr_clr_mask;
   assign regb_ddrc_ch0_poisoncfg_wr_poison_intr_clr_mask = `REGB_DDRC_CH0_MSK_POISONCFG_WR_POISON_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_rd_poison_slverr_en_mask;
   assign regb_ddrc_ch0_poisoncfg_rd_poison_slverr_en_mask = `REGB_DDRC_CH0_MSK_POISONCFG_RD_POISON_SLVERR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_rd_poison_intr_en_mask;
   assign regb_ddrc_ch0_poisoncfg_rd_poison_intr_en_mask = `REGB_DDRC_CH0_MSK_POISONCFG_RD_POISON_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_poisoncfg_rd_poison_intr_clr_mask;
   assign regb_ddrc_ch0_poisoncfg_rd_poison_intr_clr_mask = `REGB_DDRC_CH0_MSK_POISONCFG_RD_POISON_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_mode_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_mode_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_MODE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_ap_en_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_ap_en_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_AP_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_region_remap_en_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_region_remap_en_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_REGION_REMAP_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_region_map_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_region_map_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_REGION_MAP;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_blk_channel_idle_time_x32_mask;
   assign regb_ddrc_ch0_ecccfg0_blk_channel_idle_time_x32_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_ap_err_threshold_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_ap_err_threshold_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_AP_ERR_THRESHOLD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_region_map_other_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_region_map_other_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_REGION_MAP_OTHER;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg0_ecc_region_map_granu_mask;
   assign regb_ddrc_ch0_ecccfg0_ecc_region_map_granu_mask = `REGB_DDRC_CH0_MSK_ECCCFG0_ECC_REGION_MAP_GRANU;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_data_poison_en_mask;
   assign regb_ddrc_ch0_ecccfg1_data_poison_en_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_DATA_POISON_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_data_poison_bit_mask;
   assign regb_ddrc_ch0_ecccfg1_data_poison_bit_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_DATA_POISON_BIT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_ecc_region_parity_lock_mask;
   assign regb_ddrc_ch0_ecccfg1_ecc_region_parity_lock_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_ECC_REGION_PARITY_LOCK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_ecc_region_waste_lock_mask;
   assign regb_ddrc_ch0_ecccfg1_ecc_region_waste_lock_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_ECC_REGION_WASTE_LOCK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_med_ecc_en_mask;
   assign regb_ddrc_ch0_ecccfg1_med_ecc_en_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_MED_ECC_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_blk_channel_active_term_mask;
   assign regb_ddrc_ch0_ecccfg1_blk_channel_active_term_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ecccfg1_active_blk_channel_mask;
   assign regb_ddrc_ch0_ecccfg1_active_blk_channel_mask = `REGB_DDRC_CH0_MSK_ECCCFG1_ACTIVE_BLK_CHANNEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_corrected_err_clr_mask;
   assign regb_ddrc_ch0_eccctl_ecc_corrected_err_clr_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_CORRECTED_ERR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_uncorrected_err_clr_mask;
   assign regb_ddrc_ch0_eccctl_ecc_uncorrected_err_clr_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_UNCORRECTED_ERR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_corr_err_cnt_clr_mask;
   assign regb_ddrc_ch0_eccctl_ecc_corr_err_cnt_clr_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_CORR_ERR_CNT_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_uncorr_err_cnt_clr_mask;
   assign regb_ddrc_ch0_eccctl_ecc_uncorr_err_cnt_clr_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_UNCORR_ERR_CNT_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_ap_err_intr_clr_mask;
   assign regb_ddrc_ch0_eccctl_ecc_ap_err_intr_clr_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_AP_ERR_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_en_mask;
   assign regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_en_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_CORRECTED_ERR_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_en_mask;
   assign regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_en_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_ap_err_intr_en_mask;
   assign regb_ddrc_ch0_eccctl_ecc_ap_err_intr_en_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_AP_ERR_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_force_mask;
   assign regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_force_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_force_mask;
   assign regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_force_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccctl_ecc_ap_err_intr_force_mask;
   assign regb_ddrc_ch0_eccctl_ecc_ap_err_intr_force_mask = `REGB_DDRC_CH0_MSK_ECCCTL_ECC_AP_ERR_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_col_mask;
   assign regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_col_mask = `REGB_DDRC_CH0_MSK_ECCPOISONADDR0_ECC_POISON_COL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_rank_mask;
   assign regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_rank_mask = `REGB_DDRC_CH0_MSK_ECCPOISONADDR0_ECC_POISON_RANK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_row_mask;
   assign regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_row_mask = `REGB_DDRC_CH0_MSK_ECCPOISONADDR1_ECC_POISON_ROW;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bank_mask;
   assign regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bank_mask = `REGB_DDRC_CH0_MSK_ECCPOISONADDR1_ECC_POISON_BANK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bg_mask;
   assign regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bg_mask = `REGB_DDRC_CH0_MSK_ECCPOISONADDR1_ECC_POISON_BG;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonpat0_ecc_poison_data_31_0_mask;
   assign regb_ddrc_ch0_eccpoisonpat0_ecc_poison_data_31_0_mask = `REGB_DDRC_CH0_MSK_ECCPOISONPAT0_ECC_POISON_DATA_31_0;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_eccpoisonpat2_ecc_poison_data_71_64_mask;
   assign regb_ddrc_ch0_eccpoisonpat2_ecc_poison_data_71_64_mask = `REGB_DDRC_CH0_MSK_ECCPOISONPAT2_ECC_POISON_DATA_71_64;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_en_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_en_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_clr_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_clr_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_cnt_clr_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_cnt_clr_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_force_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_force_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_en_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_en_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_clr_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_clr_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_cnt_clr_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_cnt_clr_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_force_mask;
   assign regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_force_mask = `REGB_DDRC_CH0_MSK_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_inject_en_mask;
   assign regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_inject_en_mask = `REGB_DDRC_CH0_MSK_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_type_mask;
   assign regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_type_mask = `REGB_DDRC_CH0_MSK_LNKECCPOISONCTL0_LINKECC_POISON_TYPE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_rw_mask;
   assign regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_rw_mask = `REGB_DDRC_CH0_MSK_LNKECCPOISONCTL0_LINKECC_POISON_RW;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_dmi_sel_mask;
   assign regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_dmi_sel_mask = `REGB_DDRC_CH0_MSK_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_byte_sel_mask;
   assign regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_byte_sel_mask = `REGB_DDRC_CH0_MSK_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_byte_sel_mask;
   assign regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_byte_sel_mask = `REGB_DDRC_CH0_MSK_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_rank_sel_mask;
   assign regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_rank_sel_mask = `REGB_DDRC_CH0_MSK_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrl0_dis_wc_mask;
   assign regb_ddrc_ch0_opctrl0_dis_wc_mask = `REGB_DDRC_CH0_MSK_OPCTRL0_DIS_WC;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrl0_dis_max_rank_rd_opt_mask;
   assign regb_ddrc_ch0_opctrl0_dis_max_rank_rd_opt_mask = `REGB_DDRC_CH0_MSK_OPCTRL0_DIS_MAX_RANK_RD_OPT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrl0_dis_max_rank_wr_opt_mask;
   assign regb_ddrc_ch0_opctrl0_dis_max_rank_wr_opt_mask = `REGB_DDRC_CH0_MSK_OPCTRL0_DIS_MAX_RANK_WR_OPT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrl1_dis_dq_mask;
   assign regb_ddrc_ch0_opctrl1_dis_dq_mask = `REGB_DDRC_CH0_MSK_OPCTRL1_DIS_DQ;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrl1_dis_hif_mask;
   assign regb_ddrc_ch0_opctrl1_dis_hif_mask = `REGB_DDRC_CH0_MSK_OPCTRL1_DIS_HIF;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrlcmd_zq_calib_short_mask;
   assign regb_ddrc_ch0_opctrlcmd_zq_calib_short_mask = `REGB_DDRC_CH0_MSK_OPCTRLCMD_ZQ_CALIB_SHORT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrlcmd_ctrlupd_mask;
   assign regb_ddrc_ch0_opctrlcmd_ctrlupd_mask = `REGB_DDRC_CH0_MSK_OPCTRLCMD_CTRLUPD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_opctrlcmd_ctrlupd_burst_mask;
   assign regb_ddrc_ch0_opctrlcmd_ctrlupd_burst_mask = `REGB_DDRC_CH0_MSK_OPCTRLCMD_CTRLUPD_BURST;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_oprefctrl0_rank0_refresh_mask;
   assign regb_ddrc_ch0_oprefctrl0_rank0_refresh_mask = `REGB_DDRC_CH0_MSK_OPREFCTRL0_RANK0_REFRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_oprefctrl0_rank1_refresh_mask;
   assign regb_ddrc_ch0_oprefctrl0_rank1_refresh_mask = `REGB_DDRC_CH0_MSK_OPREFCTRL0_RANK1_REFRESH;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_swctl_sw_done_mask;
   assign regb_ddrc_ch0_swctl_sw_done_mask = `REGB_DDRC_CH0_MSK_SWCTL_SW_DONE;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rankctl_max_rank_rd_mask;
   assign regb_ddrc_ch0_rankctl_max_rank_rd_mask = `REGB_DDRC_CH0_MSK_RANKCTL_MAX_RANK_RD;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_rankctl_max_rank_wr_mask;
   assign regb_ddrc_ch0_rankctl_max_rank_wr_mask = `REGB_DDRC_CH0_MSK_RANKCTL_MAX_RANK_WR;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dbictl_dm_en_mask;
   assign regb_ddrc_ch0_dbictl_dm_en_mask = `REGB_DDRC_CH0_MSK_DBICTL_DM_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dbictl_wr_dbi_en_mask;
   assign regb_ddrc_ch0_dbictl_wr_dbi_en_mask = `REGB_DDRC_CH0_MSK_DBICTL_WR_DBI_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_dbictl_rd_dbi_en_mask;
   assign regb_ddrc_ch0_dbictl_rd_dbi_en_mask = `REGB_DDRC_CH0_MSK_DBICTL_RD_DBI_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_odtmap_rank0_wr_odt_mask;
   assign regb_ddrc_ch0_odtmap_rank0_wr_odt_mask = `REGB_DDRC_CH0_MSK_ODTMAP_RANK0_WR_ODT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_odtmap_rank0_rd_odt_mask;
   assign regb_ddrc_ch0_odtmap_rank0_rd_odt_mask = `REGB_DDRC_CH0_MSK_ODTMAP_RANK0_RD_ODT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_odtmap_rank1_wr_odt_mask;
   assign regb_ddrc_ch0_odtmap_rank1_wr_odt_mask = `REGB_DDRC_CH0_MSK_ODTMAP_RANK1_WR_ODT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_odtmap_rank1_rd_odt_mask;
   assign regb_ddrc_ch0_odtmap_rank1_rd_odt_mask = `REGB_DDRC_CH0_MSK_ODTMAP_RANK1_RD_ODT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_datactl0_rd_data_copy_en_mask;
   assign regb_ddrc_ch0_datactl0_rd_data_copy_en_mask = `REGB_DDRC_CH0_MSK_DATACTL0_RD_DATA_COPY_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_datactl0_wr_data_copy_en_mask;
   assign regb_ddrc_ch0_datactl0_wr_data_copy_en_mask = `REGB_DDRC_CH0_MSK_DATACTL0_WR_DATA_COPY_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_datactl0_wr_data_x_en_mask;
   assign regb_ddrc_ch0_datactl0_wr_data_x_en_mask = `REGB_DDRC_CH0_MSK_DATACTL0_WR_DATA_X_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_swctlstatic_sw_static_unlock_mask;
   assign regb_ddrc_ch0_swctlstatic_sw_static_unlock_mask = `REGB_DDRC_CH0_MSK_SWCTLSTATIC_SW_STATIC_UNLOCK;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_cgctl_force_clk_te_en_mask;
   assign regb_ddrc_ch0_cgctl_force_clk_te_en_mask = `REGB_DDRC_CH0_MSK_CGCTL_FORCE_CLK_TE_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_cgctl_force_clk_arb_en_mask;
   assign regb_ddrc_ch0_cgctl_force_clk_arb_en_mask = `REGB_DDRC_CH0_MSK_CGCTL_FORCE_CLK_ARB_EN;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_inittmg0_pre_cke_x1024_mask;
   assign regb_ddrc_ch0_inittmg0_pre_cke_x1024_mask = `REGB_DDRC_CH0_MSK_INITTMG0_PRE_CKE_X1024;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_inittmg0_post_cke_x1024_mask;
   assign regb_ddrc_ch0_inittmg0_post_cke_x1024_mask = `REGB_DDRC_CH0_MSK_INITTMG0_POST_CKE_X1024;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_inittmg0_skip_dram_init_mask;
   assign regb_ddrc_ch0_inittmg0_skip_dram_init_mask = `REGB_DDRC_CH0_MSK_INITTMG0_SKIP_DRAM_INIT;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_num_mask;
   assign regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_num_mask = `REGB_DDRC_CH0_MSK_PPT2CTRL0_PPT2_BURST_NUM;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi0_mask;
   assign regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi0_mask = `REGB_DDRC_CH0_MSK_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi1_mask;
   assign regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi1_mask = `REGB_DDRC_CH0_MSK_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_mask;
   assign regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_mask = `REGB_DDRC_CH0_MSK_PPT2CTRL0_PPT2_BURST;
   wire [REG_WIDTH-1:0] regb_ddrc_ch0_ppt2ctrl0_ppt2_wait_ref_mask;
   assign regb_ddrc_ch0_ppt2ctrl0_ppt2_wait_ref_mask = `REGB_DDRC_CH0_MSK_PPT2CTRL0_PPT2_WAIT_REF;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap1_addrmap_cs_bit0_mask;
   assign regb_addr_map0_addrmap1_addrmap_cs_bit0_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP1_ADDRMAP_CS_BIT0;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap3_addrmap_bank_b0_mask;
   assign regb_addr_map0_addrmap3_addrmap_bank_b0_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP3_ADDRMAP_BANK_B0;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap3_addrmap_bank_b1_mask;
   assign regb_addr_map0_addrmap3_addrmap_bank_b1_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP3_ADDRMAP_BANK_B1;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap3_addrmap_bank_b2_mask;
   assign regb_addr_map0_addrmap3_addrmap_bank_b2_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP3_ADDRMAP_BANK_B2;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap4_addrmap_bg_b0_mask;
   assign regb_addr_map0_addrmap4_addrmap_bg_b0_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP4_ADDRMAP_BG_B0;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap4_addrmap_bg_b1_mask;
   assign regb_addr_map0_addrmap4_addrmap_bg_b1_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP4_ADDRMAP_BG_B1;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap5_addrmap_col_b7_mask;
   assign regb_addr_map0_addrmap5_addrmap_col_b7_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP5_ADDRMAP_COL_B7;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap5_addrmap_col_b8_mask;
   assign regb_addr_map0_addrmap5_addrmap_col_b8_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP5_ADDRMAP_COL_B8;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap5_addrmap_col_b9_mask;
   assign regb_addr_map0_addrmap5_addrmap_col_b9_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP5_ADDRMAP_COL_B9;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap5_addrmap_col_b10_mask;
   assign regb_addr_map0_addrmap5_addrmap_col_b10_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP5_ADDRMAP_COL_B10;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap6_addrmap_col_b3_mask;
   assign regb_addr_map0_addrmap6_addrmap_col_b3_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP6_ADDRMAP_COL_B3;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap6_addrmap_col_b4_mask;
   assign regb_addr_map0_addrmap6_addrmap_col_b4_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP6_ADDRMAP_COL_B4;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap6_addrmap_col_b5_mask;
   assign regb_addr_map0_addrmap6_addrmap_col_b5_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP6_ADDRMAP_COL_B5;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap6_addrmap_col_b6_mask;
   assign regb_addr_map0_addrmap6_addrmap_col_b6_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP6_ADDRMAP_COL_B6;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap7_addrmap_row_b14_mask;
   assign regb_addr_map0_addrmap7_addrmap_row_b14_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP7_ADDRMAP_ROW_B14;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap7_addrmap_row_b15_mask;
   assign regb_addr_map0_addrmap7_addrmap_row_b15_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP7_ADDRMAP_ROW_B15;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap7_addrmap_row_b16_mask;
   assign regb_addr_map0_addrmap7_addrmap_row_b16_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP7_ADDRMAP_ROW_B16;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap7_addrmap_row_b17_mask;
   assign regb_addr_map0_addrmap7_addrmap_row_b17_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP7_ADDRMAP_ROW_B17;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap8_addrmap_row_b10_mask;
   assign regb_addr_map0_addrmap8_addrmap_row_b10_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP8_ADDRMAP_ROW_B10;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap8_addrmap_row_b11_mask;
   assign regb_addr_map0_addrmap8_addrmap_row_b11_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP8_ADDRMAP_ROW_B11;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap8_addrmap_row_b12_mask;
   assign regb_addr_map0_addrmap8_addrmap_row_b12_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP8_ADDRMAP_ROW_B12;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap8_addrmap_row_b13_mask;
   assign regb_addr_map0_addrmap8_addrmap_row_b13_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP8_ADDRMAP_ROW_B13;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap9_addrmap_row_b6_mask;
   assign regb_addr_map0_addrmap9_addrmap_row_b6_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP9_ADDRMAP_ROW_B6;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap9_addrmap_row_b7_mask;
   assign regb_addr_map0_addrmap9_addrmap_row_b7_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP9_ADDRMAP_ROW_B7;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap9_addrmap_row_b8_mask;
   assign regb_addr_map0_addrmap9_addrmap_row_b8_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP9_ADDRMAP_ROW_B8;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap9_addrmap_row_b9_mask;
   assign regb_addr_map0_addrmap9_addrmap_row_b9_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP9_ADDRMAP_ROW_B9;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap10_addrmap_row_b2_mask;
   assign regb_addr_map0_addrmap10_addrmap_row_b2_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP10_ADDRMAP_ROW_B2;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap10_addrmap_row_b3_mask;
   assign regb_addr_map0_addrmap10_addrmap_row_b3_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP10_ADDRMAP_ROW_B3;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap10_addrmap_row_b4_mask;
   assign regb_addr_map0_addrmap10_addrmap_row_b4_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP10_ADDRMAP_ROW_B4;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap10_addrmap_row_b5_mask;
   assign regb_addr_map0_addrmap10_addrmap_row_b5_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP10_ADDRMAP_ROW_B5;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap11_addrmap_row_b0_mask;
   assign regb_addr_map0_addrmap11_addrmap_row_b0_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP11_ADDRMAP_ROW_B0;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap11_addrmap_row_b1_mask;
   assign regb_addr_map0_addrmap11_addrmap_row_b1_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP11_ADDRMAP_ROW_B1;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap12_nonbinary_device_density_mask;
   assign regb_addr_map0_addrmap12_nonbinary_device_density_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP12_NONBINARY_DEVICE_DENSITY;
   wire [REG_WIDTH-1:0] regb_addr_map0_addrmap12_bank_hash_en_mask;
   assign regb_addr_map0_addrmap12_bank_hash_en_mask = `REGB_ADDR_MAP0_MSK_ADDRMAP12_BANK_HASH_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pccfg_go2critical_en_mask;
   assign regb_arb_port0_pccfg_go2critical_en_mask = `REGB_ARB_PORT0_MSK_PCCFG_GO2CRITICAL_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pccfg_pagematch_limit_mask;
   assign regb_arb_port0_pccfg_pagematch_limit_mask = `REGB_ARB_PORT0_MSK_PCCFG_PAGEMATCH_LIMIT;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgr_rd_port_priority_mask;
   assign regb_arb_port0_pcfgr_rd_port_priority_mask = `REGB_ARB_PORT0_MSK_PCFGR_RD_PORT_PRIORITY;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgr_rd_port_aging_en_mask;
   assign regb_arb_port0_pcfgr_rd_port_aging_en_mask = `REGB_ARB_PORT0_MSK_PCFGR_RD_PORT_AGING_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgr_rd_port_urgent_en_mask;
   assign regb_arb_port0_pcfgr_rd_port_urgent_en_mask = `REGB_ARB_PORT0_MSK_PCFGR_RD_PORT_URGENT_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgr_rd_port_pagematch_en_mask;
   assign regb_arb_port0_pcfgr_rd_port_pagematch_en_mask = `REGB_ARB_PORT0_MSK_PCFGR_RD_PORT_PAGEMATCH_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgr_rrb_lock_threshold_mask;
   assign regb_arb_port0_pcfgr_rrb_lock_threshold_mask = `REGB_ARB_PORT0_MSK_PCFGR_RRB_LOCK_THRESHOLD;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgw_wr_port_priority_mask;
   assign regb_arb_port0_pcfgw_wr_port_priority_mask = `REGB_ARB_PORT0_MSK_PCFGW_WR_PORT_PRIORITY;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgw_wr_port_aging_en_mask;
   assign regb_arb_port0_pcfgw_wr_port_aging_en_mask = `REGB_ARB_PORT0_MSK_PCFGW_WR_PORT_AGING_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgw_wr_port_urgent_en_mask;
   assign regb_arb_port0_pcfgw_wr_port_urgent_en_mask = `REGB_ARB_PORT0_MSK_PCFGW_WR_PORT_URGENT_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgw_wr_port_pagematch_en_mask;
   assign regb_arb_port0_pcfgw_wr_port_pagematch_en_mask = `REGB_ARB_PORT0_MSK_PCFGW_WR_PORT_PAGEMATCH_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pctrl_port_en_mask;
   assign regb_arb_port0_pctrl_port_en_mask = `REGB_ARB_PORT0_MSK_PCTRL_PORT_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos0_rqos_map_level1_mask;
   assign regb_arb_port0_pcfgqos0_rqos_map_level1_mask = `REGB_ARB_PORT0_MSK_PCFGQOS0_RQOS_MAP_LEVEL1;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos0_rqos_map_level2_mask;
   assign regb_arb_port0_pcfgqos0_rqos_map_level2_mask = `REGB_ARB_PORT0_MSK_PCFGQOS0_RQOS_MAP_LEVEL2;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos0_rqos_map_region0_mask;
   assign regb_arb_port0_pcfgqos0_rqos_map_region0_mask = `REGB_ARB_PORT0_MSK_PCFGQOS0_RQOS_MAP_REGION0;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos0_rqos_map_region1_mask;
   assign regb_arb_port0_pcfgqos0_rqos_map_region1_mask = `REGB_ARB_PORT0_MSK_PCFGQOS0_RQOS_MAP_REGION1;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos0_rqos_map_region2_mask;
   assign regb_arb_port0_pcfgqos0_rqos_map_region2_mask = `REGB_ARB_PORT0_MSK_PCFGQOS0_RQOS_MAP_REGION2;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos1_rqos_map_timeoutb_mask;
   assign regb_arb_port0_pcfgqos1_rqos_map_timeoutb_mask = `REGB_ARB_PORT0_MSK_PCFGQOS1_RQOS_MAP_TIMEOUTB;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgqos1_rqos_map_timeoutr_mask;
   assign regb_arb_port0_pcfgqos1_rqos_map_timeoutr_mask = `REGB_ARB_PORT0_MSK_PCFGQOS1_RQOS_MAP_TIMEOUTR;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos0_wqos_map_level1_mask;
   assign regb_arb_port0_pcfgwqos0_wqos_map_level1_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS0_WQOS_MAP_LEVEL1;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos0_wqos_map_level2_mask;
   assign regb_arb_port0_pcfgwqos0_wqos_map_level2_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS0_WQOS_MAP_LEVEL2;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos0_wqos_map_region0_mask;
   assign regb_arb_port0_pcfgwqos0_wqos_map_region0_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS0_WQOS_MAP_REGION0;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos0_wqos_map_region1_mask;
   assign regb_arb_port0_pcfgwqos0_wqos_map_region1_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS0_WQOS_MAP_REGION1;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos0_wqos_map_region2_mask;
   assign regb_arb_port0_pcfgwqos0_wqos_map_region2_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS0_WQOS_MAP_REGION2;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos1_wqos_map_timeout1_mask;
   assign regb_arb_port0_pcfgwqos1_wqos_map_timeout1_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS1_WQOS_MAP_TIMEOUT1;
   wire [REG_WIDTH-1:0] regb_arb_port0_pcfgwqos1_wqos_map_timeout2_mask;
   assign regb_arb_port0_pcfgwqos1_wqos_map_timeout2_mask = `REGB_ARB_PORT0_MSK_PCFGWQOS1_WQOS_MAP_TIMEOUT2;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_en_mask;
   assign regb_arb_port0_sbrctl_scrub_en_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_EN;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_during_lowpower_mask;
   assign regb_arb_port0_sbrctl_scrub_during_lowpower_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_DURING_LOWPOWER;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_burst_length_nm_mask;
   assign regb_arb_port0_sbrctl_scrub_burst_length_nm_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_BURST_LENGTH_NM;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_interval_mask;
   assign regb_arb_port0_sbrctl_scrub_interval_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_INTERVAL;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_cmd_type_mask;
   assign regb_arb_port0_sbrctl_scrub_cmd_type_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_CMD_TYPE;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrctl_scrub_burst_length_lp_mask;
   assign regb_arb_port0_sbrctl_scrub_burst_length_lp_mask = `REGB_ARB_PORT0_MSK_SBRCTL_SCRUB_BURST_LENGTH_LP;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrwdata0_scrub_pattern0_mask;
   assign regb_arb_port0_sbrwdata0_scrub_pattern0_mask = `REGB_ARB_PORT0_MSK_SBRWDATA0_SCRUB_PATTERN0;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrstart0_sbr_address_start_mask_0_mask;
   assign regb_arb_port0_sbrstart0_sbr_address_start_mask_0_mask = `REGB_ARB_PORT0_MSK_SBRSTART0_SBR_ADDRESS_START_MASK_0;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrstart1_sbr_address_start_mask_1_mask;
   assign regb_arb_port0_sbrstart1_sbr_address_start_mask_1_mask = `REGB_ARB_PORT0_MSK_SBRSTART1_SBR_ADDRESS_START_MASK_1;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrrange0_sbr_address_range_mask_0_mask;
   assign regb_arb_port0_sbrrange0_sbr_address_range_mask_0_mask = `REGB_ARB_PORT0_MSK_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0;
   wire [REG_WIDTH-1:0] regb_arb_port0_sbrrange1_sbr_address_range_mask_1_mask;
   assign regb_arb_port0_sbrrange1_sbr_address_range_mask_1_mask = `REGB_ARB_PORT0_MSK_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg0_t_ras_min_mask;
   assign regb_freq0_ch0_dramset1tmg0_t_ras_min_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG0_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg0_t_ras_max_mask;
   assign regb_freq0_ch0_dramset1tmg0_t_ras_max_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG0_T_RAS_MAX;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg0_t_faw_mask;
   assign regb_freq0_ch0_dramset1tmg0_t_faw_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG0_T_FAW;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg0_wr2pre_mask;
   assign regb_freq0_ch0_dramset1tmg0_wr2pre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG0_WR2PRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg1_t_rc_mask;
   assign regb_freq0_ch0_dramset1tmg1_t_rc_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG1_T_RC;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg1_rd2pre_mask;
   assign regb_freq0_ch0_dramset1tmg1_rd2pre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG1_RD2PRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg1_t_xp_mask;
   assign regb_freq0_ch0_dramset1tmg1_t_xp_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG1_T_XP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg1_t_rcd_write_mask;
   assign regb_freq0_ch0_dramset1tmg1_t_rcd_write_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG1_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg2_wr2rd_mask;
   assign regb_freq0_ch0_dramset1tmg2_wr2rd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG2_WR2RD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg2_rd2wr_mask;
   assign regb_freq0_ch0_dramset1tmg2_rd2wr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG2_RD2WR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg2_read_latency_mask;
   assign regb_freq0_ch0_dramset1tmg2_read_latency_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG2_READ_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg2_write_latency_mask;
   assign regb_freq0_ch0_dramset1tmg2_write_latency_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG2_WRITE_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg3_wr2mr_mask;
   assign regb_freq0_ch0_dramset1tmg3_wr2mr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG3_WR2MR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg3_rd2mr_mask;
   assign regb_freq0_ch0_dramset1tmg3_rd2mr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG3_RD2MR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg3_t_mr_mask;
   assign regb_freq0_ch0_dramset1tmg3_t_mr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG3_T_MR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg4_t_rp_mask;
   assign regb_freq0_ch0_dramset1tmg4_t_rp_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG4_T_RP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg4_t_rrd_mask;
   assign regb_freq0_ch0_dramset1tmg4_t_rrd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG4_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg4_t_ccd_mask;
   assign regb_freq0_ch0_dramset1tmg4_t_ccd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG4_T_CCD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg4_t_rcd_mask;
   assign regb_freq0_ch0_dramset1tmg4_t_rcd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG4_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg5_t_cke_mask;
   assign regb_freq0_ch0_dramset1tmg5_t_cke_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG5_T_CKE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg5_t_ckesr_mask;
   assign regb_freq0_ch0_dramset1tmg5_t_ckesr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG5_T_CKESR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg5_t_cksre_mask;
   assign regb_freq0_ch0_dramset1tmg5_t_cksre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG5_T_CKSRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg5_t_cksrx_mask;
   assign regb_freq0_ch0_dramset1tmg5_t_cksrx_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG5_T_CKSRX;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg6_t_ckcsx_mask;
   assign regb_freq0_ch0_dramset1tmg6_t_ckcsx_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG6_T_CKCSX;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg7_t_csh_mask;
   assign regb_freq0_ch0_dramset1tmg7_t_csh_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG7_T_CSH;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg9_wr2rd_s_mask;
   assign regb_freq0_ch0_dramset1tmg9_wr2rd_s_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG9_WR2RD_S;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg9_t_rrd_s_mask;
   assign regb_freq0_ch0_dramset1tmg9_t_rrd_s_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG9_T_RRD_S;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg9_t_ccd_s_mask;
   assign regb_freq0_ch0_dramset1tmg9_t_ccd_s_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG9_T_CCD_S;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg12_t_cmdcke_mask;
   assign regb_freq0_ch0_dramset1tmg12_t_cmdcke_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG12_T_CMDCKE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg13_t_ppd_mask;
   assign regb_freq0_ch0_dramset1tmg13_t_ppd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG13_T_PPD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg13_t_ccd_mw_mask;
   assign regb_freq0_ch0_dramset1tmg13_t_ccd_mw_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG13_T_CCD_MW;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg13_odtloff_mask;
   assign regb_freq0_ch0_dramset1tmg13_odtloff_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG13_ODTLOFF;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg14_t_xsr_mask;
   assign regb_freq0_ch0_dramset1tmg14_t_xsr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG14_T_XSR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg14_t_osco_mask;
   assign regb_freq0_ch0_dramset1tmg14_t_osco_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG14_T_OSCO;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg17_t_vrcg_disable_mask;
   assign regb_freq0_ch0_dramset1tmg17_t_vrcg_disable_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG17_T_VRCG_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg17_t_vrcg_enable_mask;
   assign regb_freq0_ch0_dramset1tmg17_t_vrcg_enable_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG17_T_VRCG_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg23_t_pdn_mask;
   assign regb_freq0_ch0_dramset1tmg23_t_pdn_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG23_T_PDN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask;
   assign regb_freq0_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG23_T_XSR_DSM_X1024;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg24_max_wr_sync_mask;
   assign regb_freq0_ch0_dramset1tmg24_max_wr_sync_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG24_MAX_WR_SYNC;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg24_max_rd_sync_mask;
   assign regb_freq0_ch0_dramset1tmg24_max_rd_sync_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG24_MAX_RD_SYNC;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg24_rd2wr_s_mask;
   assign regb_freq0_ch0_dramset1tmg24_rd2wr_s_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG24_RD2WR_S;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg24_bank_org_mask;
   assign regb_freq0_ch0_dramset1tmg24_bank_org_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG24_BANK_ORG;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg25_rda2pre_mask;
   assign regb_freq0_ch0_dramset1tmg25_rda2pre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG25_RDA2PRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg25_wra2pre_mask;
   assign regb_freq0_ch0_dramset1tmg25_wra2pre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG25_WRA2PRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask;
   assign regb_freq0_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg30_mrr2rd_mask;
   assign regb_freq0_ch0_dramset1tmg30_mrr2rd_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG30_MRR2RD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg30_mrr2wr_mask;
   assign regb_freq0_ch0_dramset1tmg30_mrr2wr_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG30_MRR2WR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg30_mrr2mrw_mask;
   assign regb_freq0_ch0_dramset1tmg30_mrr2mrw_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG30_MRR2MRW;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg32_ws_fs2wck_sus_mask;
   assign regb_freq0_ch0_dramset1tmg32_ws_fs2wck_sus_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG32_WS_FS2WCK_SUS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg32_t_wcksus_mask;
   assign regb_freq0_ch0_dramset1tmg32_t_wcksus_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG32_T_WCKSUS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dramset1tmg32_ws_off2ws_fs_mask;
   assign regb_freq0_ch0_dramset1tmg32_ws_off2ws_fs_mask = `REGB_FREQ0_CH0_MSK_DRAMSET1TMG32_WS_OFF2WS_FS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr0_emr_mask;
   assign regb_freq0_ch0_initmr0_emr_mask = `REGB_FREQ0_CH0_MSK_INITMR0_EMR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr0_mr_mask;
   assign regb_freq0_ch0_initmr0_mr_mask = `REGB_FREQ0_CH0_MSK_INITMR0_MR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr1_emr3_mask;
   assign regb_freq0_ch0_initmr1_emr3_mask = `REGB_FREQ0_CH0_MSK_INITMR1_EMR3;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr1_emr2_mask;
   assign regb_freq0_ch0_initmr1_emr2_mask = `REGB_FREQ0_CH0_MSK_INITMR1_EMR2;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr2_mr5_mask;
   assign regb_freq0_ch0_initmr2_mr5_mask = `REGB_FREQ0_CH0_MSK_INITMR2_MR5;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr2_mr4_mask;
   assign regb_freq0_ch0_initmr2_mr4_mask = `REGB_FREQ0_CH0_MSK_INITMR2_MR4;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr3_mr6_mask;
   assign regb_freq0_ch0_initmr3_mr6_mask = `REGB_FREQ0_CH0_MSK_INITMR3_MR6;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_initmr3_mr22_mask;
   assign regb_freq0_ch0_initmr3_mr22_mask = `REGB_FREQ0_CH0_MSK_INITMR3_MR22;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg0_dfi_tphy_wrlat_mask;
   assign regb_freq0_ch0_dfitmg0_dfi_tphy_wrlat_mask = `REGB_FREQ0_CH0_MSK_DFITMG0_DFI_TPHY_WRLAT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg0_dfi_tphy_wrdata_mask;
   assign regb_freq0_ch0_dfitmg0_dfi_tphy_wrdata_mask = `REGB_FREQ0_CH0_MSK_DFITMG0_DFI_TPHY_WRDATA;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg0_dfi_t_rddata_en_mask;
   assign regb_freq0_ch0_dfitmg0_dfi_t_rddata_en_mask = `REGB_FREQ0_CH0_MSK_DFITMG0_DFI_T_RDDATA_EN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg0_dfi_t_ctrl_delay_mask;
   assign regb_freq0_ch0_dfitmg0_dfi_t_ctrl_delay_mask = `REGB_FREQ0_CH0_MSK_DFITMG0_DFI_T_CTRL_DELAY;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_enable_mask;
   assign regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_enable_mask = `REGB_FREQ0_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_disable_mask;
   assign regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_disable_mask = `REGB_FREQ0_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg1_dfi_t_wrdata_delay_mask;
   assign regb_freq0_ch0_dfitmg1_dfi_t_wrdata_delay_mask = `REGB_FREQ0_CH0_MSK_DFITMG1_DFI_T_WRDATA_DELAY;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg2_dfi_tphy_wrcslat_mask;
   assign regb_freq0_ch0_dfitmg2_dfi_tphy_wrcslat_mask = `REGB_FREQ0_CH0_MSK_DFITMG2_DFI_TPHY_WRCSLAT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg2_dfi_tphy_rdcslat_mask;
   assign regb_freq0_ch0_dfitmg2_dfi_tphy_rdcslat_mask = `REGB_FREQ0_CH0_MSK_DFITMG2_DFI_TPHY_RDCSLAT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg2_dfi_twck_delay_mask;
   assign regb_freq0_ch0_dfitmg2_dfi_twck_delay_mask = `REGB_FREQ0_CH0_MSK_DFITMG2_DFI_TWCK_DELAY;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg4_dfi_twck_dis_mask;
   assign regb_freq0_ch0_dfitmg4_dfi_twck_dis_mask = `REGB_FREQ0_CH0_MSK_DFITMG4_DFI_TWCK_DIS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg4_dfi_twck_en_fs_mask;
   assign regb_freq0_ch0_dfitmg4_dfi_twck_en_fs_mask = `REGB_FREQ0_CH0_MSK_DFITMG4_DFI_TWCK_EN_FS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg4_dfi_twck_en_wr_mask;
   assign regb_freq0_ch0_dfitmg4_dfi_twck_en_wr_mask = `REGB_FREQ0_CH0_MSK_DFITMG4_DFI_TWCK_EN_WR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg4_dfi_twck_en_rd_mask;
   assign regb_freq0_ch0_dfitmg4_dfi_twck_en_rd_mask = `REGB_FREQ0_CH0_MSK_DFITMG4_DFI_TWCK_EN_RD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg5_dfi_twck_toggle_post_mask;
   assign regb_freq0_ch0_dfitmg5_dfi_twck_toggle_post_mask = `REGB_FREQ0_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_POST;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg5_dfi_twck_toggle_cs_mask;
   assign regb_freq0_ch0_dfitmg5_dfi_twck_toggle_cs_mask = `REGB_FREQ0_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_CS;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg5_dfi_twck_toggle_mask;
   assign regb_freq0_ch0_dfitmg5_dfi_twck_toggle_mask = `REGB_FREQ0_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg5_dfi_twck_fast_toggle_mask;
   assign regb_freq0_ch0_dfitmg5_dfi_twck_fast_toggle_mask = `REGB_FREQ0_CH0_MSK_DFITMG5_DFI_TWCK_FAST_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask;
   assign regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask = `REGB_FREQ0_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask;
   assign regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask = `REGB_FREQ0_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pd_mask;
   assign regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pd_mask = `REGB_FREQ0_CH0_MSK_DFILPTMG0_DFI_LP_WAKEUP_PD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_sr_mask;
   assign regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_sr_mask = `REGB_FREQ0_CH0_MSK_DFILPTMG0_DFI_LP_WAKEUP_SR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsm_mask;
   assign regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsm_mask = `REGB_FREQ0_CH0_MSK_DFILPTMG0_DFI_LP_WAKEUP_DSM;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_data_mask;
   assign regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_data_mask = `REGB_FREQ0_CH0_MSK_DFILPTMG1_DFI_LP_WAKEUP_DATA;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfilptmg1_dfi_tlp_resp_mask;
   assign regb_freq0_ch0_dfilptmg1_dfi_tlp_resp_mask = `REGB_FREQ0_CH0_MSK_DFILPTMG1_DFI_TLP_RESP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_min_mask;
   assign regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_min_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG0_DFI_T_CTRLUP_MIN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_max_mask;
   assign regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_max_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG0_DFI_T_CTRLUP_MAX;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask;
   assign regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask;
   assign regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask;
   assign regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask;
   assign regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg2_ppt2_override_mask;
   assign regb_freq0_ch0_dfiupdtmg2_ppt2_override_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG2_PPT2_OVERRIDE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg2_ppt2_en_mask;
   assign regb_freq0_ch0_dfiupdtmg2_ppt2_en_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG2_PPT2_EN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask;
   assign regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask;
   assign regb_freq0_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask = `REGB_FREQ0_CH0_MSK_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg0_t_refi_x1_x32_mask;
   assign regb_freq0_ch0_rfshset1tmg0_t_refi_x1_x32_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_x32_mask;
   assign regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_x32_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg0_refresh_margin_mask;
   assign regb_freq0_ch0_rfshset1tmg0_refresh_margin_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG0_REFRESH_MARGIN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_sel_mask;
   assign regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_sel_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg0_t_refi_x1_sel_mask;
   assign regb_freq0_ch0_rfshset1tmg0_t_refi_x1_sel_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg1_t_rfc_min_mask;
   assign regb_freq0_ch0_rfshset1tmg1_t_rfc_min_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg1_t_rfc_min_ab_mask;
   assign regb_freq0_ch0_rfshset1tmg1_t_rfc_min_ab_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN_AB;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg2_t_pbr2pbr_mask;
   assign regb_freq0_ch0_rfshset1tmg2_t_pbr2pbr_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG2_T_PBR2PBR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg2_t_pbr2act_mask;
   assign regb_freq0_ch0_rfshset1tmg2_t_pbr2act_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG2_T_PBR2ACT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg3_refresh_to_ab_x32_mask;
   assign regb_freq0_ch0_rfshset1tmg3_refresh_to_ab_x32_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG3_REFRESH_TO_AB_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask;
   assign regb_freq0_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask;
   assign regb_freq0_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask = `REGB_FREQ0_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_rfmset1tmg0_t_rfmpb_mask;
   assign regb_freq0_ch0_rfmset1tmg0_t_rfmpb_mask = `REGB_FREQ0_CH0_MSK_RFMSET1TMG0_T_RFMPB;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_zqset1tmg0_t_zq_long_nop_mask;
   assign regb_freq0_ch0_zqset1tmg0_t_zq_long_nop_mask = `REGB_FREQ0_CH0_MSK_ZQSET1TMG0_T_ZQ_LONG_NOP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_zqset1tmg0_t_zq_short_nop_mask;
   assign regb_freq0_ch0_zqset1tmg0_t_zq_short_nop_mask = `REGB_FREQ0_CH0_MSK_ZQSET1TMG0_T_ZQ_SHORT_NOP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask;
   assign regb_freq0_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask = `REGB_FREQ0_CH0_MSK_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_zqset1tmg1_t_zq_reset_nop_mask;
   assign regb_freq0_ch0_zqset1tmg1_t_zq_reset_nop_mask = `REGB_FREQ0_CH0_MSK_ZQSET1TMG1_T_ZQ_RESET_NOP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_zqset1tmg2_t_zq_stop_mask;
   assign regb_freq0_ch0_zqset1tmg2_t_zq_stop_mask = `REGB_FREQ0_CH0_MSK_ZQSET1TMG2_T_ZQ_STOP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dqsoscctl0_dqsosc_enable_mask;
   assign regb_freq0_ch0_dqsoscctl0_dqsosc_enable_mask = `REGB_FREQ0_CH0_MSK_DQSOSCCTL0_DQSOSC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dqsoscctl0_dqsosc_interval_unit_mask;
   assign regb_freq0_ch0_dqsoscctl0_dqsosc_interval_unit_mask = `REGB_FREQ0_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dqsoscctl0_dqsosc_interval_mask;
   assign regb_freq0_ch0_dqsoscctl0_dqsosc_interval_mask = `REGB_FREQ0_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateint_mr4_read_interval_mask;
   assign regb_freq0_ch0_derateint_mr4_read_interval_mask = `REGB_FREQ0_CH0_MSK_DERATEINT_MR4_READ_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval0_derated_t_rrd_mask;
   assign regb_freq0_ch0_derateval0_derated_t_rrd_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL0_DERATED_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval0_derated_t_rp_mask;
   assign regb_freq0_ch0_derateval0_derated_t_rp_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL0_DERATED_T_RP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval0_derated_t_ras_min_mask;
   assign regb_freq0_ch0_derateval0_derated_t_ras_min_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL0_DERATED_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval0_derated_t_rcd_mask;
   assign regb_freq0_ch0_derateval0_derated_t_rcd_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL0_DERATED_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval1_derated_t_rc_mask;
   assign regb_freq0_ch0_derateval1_derated_t_rc_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL1_DERATED_T_RC;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_derateval1_derated_t_rcd_write_mask;
   assign regb_freq0_ch0_derateval1_derated_t_rcd_write_mask = `REGB_FREQ0_CH0_MSK_DERATEVAL1_DERATED_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_hwlptmg0_hw_lp_idle_x32_mask;
   assign regb_freq0_ch0_hwlptmg0_hw_lp_idle_x32_mask = `REGB_FREQ0_CH0_MSK_HWLPTMG0_HW_LP_IDLE_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_dvfsctl0_dvfsq_enable_mask;
   assign regb_freq0_ch0_dvfsctl0_dvfsq_enable_mask = `REGB_FREQ0_CH0_MSK_DVFSCTL0_DVFSQ_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_schedtmg0_pageclose_timer_mask;
   assign regb_freq0_ch0_schedtmg0_pageclose_timer_mask = `REGB_FREQ0_CH0_MSK_SCHEDTMG0_PAGECLOSE_TIMER;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_schedtmg0_rdwr_idle_gap_mask;
   assign regb_freq0_ch0_schedtmg0_rdwr_idle_gap_mask = `REGB_FREQ0_CH0_MSK_SCHEDTMG0_RDWR_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perfhpr1_hpr_max_starve_mask;
   assign regb_freq0_ch0_perfhpr1_hpr_max_starve_mask = `REGB_FREQ0_CH0_MSK_PERFHPR1_HPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perfhpr1_hpr_xact_run_length_mask;
   assign regb_freq0_ch0_perfhpr1_hpr_xact_run_length_mask = `REGB_FREQ0_CH0_MSK_PERFHPR1_HPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perflpr1_lpr_max_starve_mask;
   assign regb_freq0_ch0_perflpr1_lpr_max_starve_mask = `REGB_FREQ0_CH0_MSK_PERFLPR1_LPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perflpr1_lpr_xact_run_length_mask;
   assign regb_freq0_ch0_perflpr1_lpr_xact_run_length_mask = `REGB_FREQ0_CH0_MSK_PERFLPR1_LPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perfwr1_w_max_starve_mask;
   assign regb_freq0_ch0_perfwr1_w_max_starve_mask = `REGB_FREQ0_CH0_MSK_PERFWR1_W_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_perfwr1_w_xact_run_length_mask;
   assign regb_freq0_ch0_perfwr1_w_xact_run_length_mask = `REGB_FREQ0_CH0_MSK_PERFWR1_W_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_tmgcfg_frequency_ratio_mask;
   assign regb_freq0_ch0_tmgcfg_frequency_ratio_mask = `REGB_FREQ0_CH0_MSK_TMGCFG_FREQUENCY_RATIO;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ranktmg0_diff_rank_rd_gap_mask;
   assign regb_freq0_ch0_ranktmg0_diff_rank_rd_gap_mask = `REGB_FREQ0_CH0_MSK_RANKTMG0_DIFF_RANK_RD_GAP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ranktmg0_diff_rank_wr_gap_mask;
   assign regb_freq0_ch0_ranktmg0_diff_rank_wr_gap_mask = `REGB_FREQ0_CH0_MSK_RANKTMG0_DIFF_RANK_WR_GAP;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ranktmg1_wr2rd_dr_mask;
   assign regb_freq0_ch0_ranktmg1_wr2rd_dr_mask = `REGB_FREQ0_CH0_MSK_RANKTMG1_WR2RD_DR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ranktmg1_rd2wr_dr_mask;
   assign regb_freq0_ch0_ranktmg1_rd2wr_dr_mask = `REGB_FREQ0_CH0_MSK_RANKTMG1_RD2WR_DR;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_pwrtmg_powerdown_to_x32_mask;
   assign regb_freq0_ch0_pwrtmg_powerdown_to_x32_mask = `REGB_FREQ0_CH0_MSK_PWRTMG_POWERDOWN_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_pwrtmg_selfref_to_x32_mask;
   assign regb_freq0_ch0_pwrtmg_selfref_to_x32_mask = `REGB_FREQ0_CH0_MSK_PWRTMG_SELFREF_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask;
   assign regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask = `REGB_FREQ0_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_X1024;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask;
   assign regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask = `REGB_FREQ0_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ddr4pprtmg1_t_pgmpst_x32_mask;
   assign regb_freq0_ch0_ddr4pprtmg1_t_pgmpst_x32_mask = `REGB_FREQ0_CH0_MSK_DDR4PPRTMG1_T_PGMPST_X32;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_ddr4pprtmg1_t_pgm_exit_mask;
   assign regb_freq0_ch0_ddr4pprtmg1_t_pgm_exit_mask = `REGB_FREQ0_CH0_MSK_DDR4PPRTMG1_T_PGM_EXIT;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enable_mask;
   assign regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enable_mask = `REGB_FREQ0_CH0_MSK_LNKECCCTL0_WR_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enable_mask;
   assign regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enable_mask = `REGB_FREQ0_CH0_MSK_LNKECCCTL0_RD_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg0_t_ras_min_mask;
   assign regb_freq1_ch0_dramset1tmg0_t_ras_min_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG0_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg0_t_ras_max_mask;
   assign regb_freq1_ch0_dramset1tmg0_t_ras_max_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG0_T_RAS_MAX;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg0_t_faw_mask;
   assign regb_freq1_ch0_dramset1tmg0_t_faw_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG0_T_FAW;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg0_wr2pre_mask;
   assign regb_freq1_ch0_dramset1tmg0_wr2pre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG0_WR2PRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg1_t_rc_mask;
   assign regb_freq1_ch0_dramset1tmg1_t_rc_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG1_T_RC;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg1_rd2pre_mask;
   assign regb_freq1_ch0_dramset1tmg1_rd2pre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG1_RD2PRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg1_t_xp_mask;
   assign regb_freq1_ch0_dramset1tmg1_t_xp_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG1_T_XP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg1_t_rcd_write_mask;
   assign regb_freq1_ch0_dramset1tmg1_t_rcd_write_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG1_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg2_wr2rd_mask;
   assign regb_freq1_ch0_dramset1tmg2_wr2rd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG2_WR2RD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg2_rd2wr_mask;
   assign regb_freq1_ch0_dramset1tmg2_rd2wr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG2_RD2WR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg2_read_latency_mask;
   assign regb_freq1_ch0_dramset1tmg2_read_latency_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG2_READ_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg2_write_latency_mask;
   assign regb_freq1_ch0_dramset1tmg2_write_latency_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG2_WRITE_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg3_wr2mr_mask;
   assign regb_freq1_ch0_dramset1tmg3_wr2mr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG3_WR2MR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg3_rd2mr_mask;
   assign regb_freq1_ch0_dramset1tmg3_rd2mr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG3_RD2MR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg3_t_mr_mask;
   assign regb_freq1_ch0_dramset1tmg3_t_mr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG3_T_MR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg4_t_rp_mask;
   assign regb_freq1_ch0_dramset1tmg4_t_rp_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG4_T_RP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg4_t_rrd_mask;
   assign regb_freq1_ch0_dramset1tmg4_t_rrd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG4_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg4_t_ccd_mask;
   assign regb_freq1_ch0_dramset1tmg4_t_ccd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG4_T_CCD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg4_t_rcd_mask;
   assign regb_freq1_ch0_dramset1tmg4_t_rcd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG4_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg5_t_cke_mask;
   assign regb_freq1_ch0_dramset1tmg5_t_cke_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG5_T_CKE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg5_t_ckesr_mask;
   assign regb_freq1_ch0_dramset1tmg5_t_ckesr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG5_T_CKESR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg5_t_cksre_mask;
   assign regb_freq1_ch0_dramset1tmg5_t_cksre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG5_T_CKSRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg5_t_cksrx_mask;
   assign regb_freq1_ch0_dramset1tmg5_t_cksrx_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG5_T_CKSRX;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg6_t_ckcsx_mask;
   assign regb_freq1_ch0_dramset1tmg6_t_ckcsx_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG6_T_CKCSX;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg7_t_csh_mask;
   assign regb_freq1_ch0_dramset1tmg7_t_csh_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG7_T_CSH;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg9_wr2rd_s_mask;
   assign regb_freq1_ch0_dramset1tmg9_wr2rd_s_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG9_WR2RD_S;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg9_t_rrd_s_mask;
   assign regb_freq1_ch0_dramset1tmg9_t_rrd_s_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG9_T_RRD_S;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg9_t_ccd_s_mask;
   assign regb_freq1_ch0_dramset1tmg9_t_ccd_s_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG9_T_CCD_S;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg12_t_cmdcke_mask;
   assign regb_freq1_ch0_dramset1tmg12_t_cmdcke_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG12_T_CMDCKE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg13_t_ppd_mask;
   assign regb_freq1_ch0_dramset1tmg13_t_ppd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG13_T_PPD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg13_t_ccd_mw_mask;
   assign regb_freq1_ch0_dramset1tmg13_t_ccd_mw_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG13_T_CCD_MW;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg13_odtloff_mask;
   assign regb_freq1_ch0_dramset1tmg13_odtloff_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG13_ODTLOFF;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg14_t_xsr_mask;
   assign regb_freq1_ch0_dramset1tmg14_t_xsr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG14_T_XSR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg14_t_osco_mask;
   assign regb_freq1_ch0_dramset1tmg14_t_osco_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG14_T_OSCO;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg17_t_vrcg_disable_mask;
   assign regb_freq1_ch0_dramset1tmg17_t_vrcg_disable_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG17_T_VRCG_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg17_t_vrcg_enable_mask;
   assign regb_freq1_ch0_dramset1tmg17_t_vrcg_enable_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG17_T_VRCG_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg23_t_pdn_mask;
   assign regb_freq1_ch0_dramset1tmg23_t_pdn_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG23_T_PDN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask;
   assign regb_freq1_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG23_T_XSR_DSM_X1024;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg24_max_wr_sync_mask;
   assign regb_freq1_ch0_dramset1tmg24_max_wr_sync_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG24_MAX_WR_SYNC;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg24_max_rd_sync_mask;
   assign regb_freq1_ch0_dramset1tmg24_max_rd_sync_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG24_MAX_RD_SYNC;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg24_rd2wr_s_mask;
   assign regb_freq1_ch0_dramset1tmg24_rd2wr_s_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG24_RD2WR_S;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg24_bank_org_mask;
   assign regb_freq1_ch0_dramset1tmg24_bank_org_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG24_BANK_ORG;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg25_rda2pre_mask;
   assign regb_freq1_ch0_dramset1tmg25_rda2pre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG25_RDA2PRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg25_wra2pre_mask;
   assign regb_freq1_ch0_dramset1tmg25_wra2pre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG25_WRA2PRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask;
   assign regb_freq1_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg30_mrr2rd_mask;
   assign regb_freq1_ch0_dramset1tmg30_mrr2rd_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG30_MRR2RD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg30_mrr2wr_mask;
   assign regb_freq1_ch0_dramset1tmg30_mrr2wr_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG30_MRR2WR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg30_mrr2mrw_mask;
   assign regb_freq1_ch0_dramset1tmg30_mrr2mrw_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG30_MRR2MRW;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg32_ws_fs2wck_sus_mask;
   assign regb_freq1_ch0_dramset1tmg32_ws_fs2wck_sus_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG32_WS_FS2WCK_SUS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg32_t_wcksus_mask;
   assign regb_freq1_ch0_dramset1tmg32_t_wcksus_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG32_T_WCKSUS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dramset1tmg32_ws_off2ws_fs_mask;
   assign regb_freq1_ch0_dramset1tmg32_ws_off2ws_fs_mask = `REGB_FREQ1_CH0_MSK_DRAMSET1TMG32_WS_OFF2WS_FS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr0_emr_mask;
   assign regb_freq1_ch0_initmr0_emr_mask = `REGB_FREQ1_CH0_MSK_INITMR0_EMR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr0_mr_mask;
   assign regb_freq1_ch0_initmr0_mr_mask = `REGB_FREQ1_CH0_MSK_INITMR0_MR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr1_emr3_mask;
   assign regb_freq1_ch0_initmr1_emr3_mask = `REGB_FREQ1_CH0_MSK_INITMR1_EMR3;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr1_emr2_mask;
   assign regb_freq1_ch0_initmr1_emr2_mask = `REGB_FREQ1_CH0_MSK_INITMR1_EMR2;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr2_mr5_mask;
   assign regb_freq1_ch0_initmr2_mr5_mask = `REGB_FREQ1_CH0_MSK_INITMR2_MR5;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr2_mr4_mask;
   assign regb_freq1_ch0_initmr2_mr4_mask = `REGB_FREQ1_CH0_MSK_INITMR2_MR4;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr3_mr6_mask;
   assign regb_freq1_ch0_initmr3_mr6_mask = `REGB_FREQ1_CH0_MSK_INITMR3_MR6;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_initmr3_mr22_mask;
   assign regb_freq1_ch0_initmr3_mr22_mask = `REGB_FREQ1_CH0_MSK_INITMR3_MR22;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg0_dfi_tphy_wrlat_mask;
   assign regb_freq1_ch0_dfitmg0_dfi_tphy_wrlat_mask = `REGB_FREQ1_CH0_MSK_DFITMG0_DFI_TPHY_WRLAT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg0_dfi_tphy_wrdata_mask;
   assign regb_freq1_ch0_dfitmg0_dfi_tphy_wrdata_mask = `REGB_FREQ1_CH0_MSK_DFITMG0_DFI_TPHY_WRDATA;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg0_dfi_t_rddata_en_mask;
   assign regb_freq1_ch0_dfitmg0_dfi_t_rddata_en_mask = `REGB_FREQ1_CH0_MSK_DFITMG0_DFI_T_RDDATA_EN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg0_dfi_t_ctrl_delay_mask;
   assign regb_freq1_ch0_dfitmg0_dfi_t_ctrl_delay_mask = `REGB_FREQ1_CH0_MSK_DFITMG0_DFI_T_CTRL_DELAY;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_enable_mask;
   assign regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_enable_mask = `REGB_FREQ1_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_disable_mask;
   assign regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_disable_mask = `REGB_FREQ1_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg1_dfi_t_wrdata_delay_mask;
   assign regb_freq1_ch0_dfitmg1_dfi_t_wrdata_delay_mask = `REGB_FREQ1_CH0_MSK_DFITMG1_DFI_T_WRDATA_DELAY;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg2_dfi_tphy_wrcslat_mask;
   assign regb_freq1_ch0_dfitmg2_dfi_tphy_wrcslat_mask = `REGB_FREQ1_CH0_MSK_DFITMG2_DFI_TPHY_WRCSLAT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg2_dfi_tphy_rdcslat_mask;
   assign regb_freq1_ch0_dfitmg2_dfi_tphy_rdcslat_mask = `REGB_FREQ1_CH0_MSK_DFITMG2_DFI_TPHY_RDCSLAT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg2_dfi_twck_delay_mask;
   assign regb_freq1_ch0_dfitmg2_dfi_twck_delay_mask = `REGB_FREQ1_CH0_MSK_DFITMG2_DFI_TWCK_DELAY;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg4_dfi_twck_dis_mask;
   assign regb_freq1_ch0_dfitmg4_dfi_twck_dis_mask = `REGB_FREQ1_CH0_MSK_DFITMG4_DFI_TWCK_DIS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg4_dfi_twck_en_fs_mask;
   assign regb_freq1_ch0_dfitmg4_dfi_twck_en_fs_mask = `REGB_FREQ1_CH0_MSK_DFITMG4_DFI_TWCK_EN_FS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg4_dfi_twck_en_wr_mask;
   assign regb_freq1_ch0_dfitmg4_dfi_twck_en_wr_mask = `REGB_FREQ1_CH0_MSK_DFITMG4_DFI_TWCK_EN_WR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg4_dfi_twck_en_rd_mask;
   assign regb_freq1_ch0_dfitmg4_dfi_twck_en_rd_mask = `REGB_FREQ1_CH0_MSK_DFITMG4_DFI_TWCK_EN_RD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg5_dfi_twck_toggle_post_mask;
   assign regb_freq1_ch0_dfitmg5_dfi_twck_toggle_post_mask = `REGB_FREQ1_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_POST;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg5_dfi_twck_toggle_cs_mask;
   assign regb_freq1_ch0_dfitmg5_dfi_twck_toggle_cs_mask = `REGB_FREQ1_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_CS;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg5_dfi_twck_toggle_mask;
   assign regb_freq1_ch0_dfitmg5_dfi_twck_toggle_mask = `REGB_FREQ1_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg5_dfi_twck_fast_toggle_mask;
   assign regb_freq1_ch0_dfitmg5_dfi_twck_fast_toggle_mask = `REGB_FREQ1_CH0_MSK_DFITMG5_DFI_TWCK_FAST_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask;
   assign regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask = `REGB_FREQ1_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask;
   assign regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask = `REGB_FREQ1_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask;
   assign regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask;
   assign regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask;
   assign regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask;
   assign regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg2_ppt2_override_mask;
   assign regb_freq1_ch0_dfiupdtmg2_ppt2_override_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG2_PPT2_OVERRIDE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg2_ppt2_en_mask;
   assign regb_freq1_ch0_dfiupdtmg2_ppt2_en_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG2_PPT2_EN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask;
   assign regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask;
   assign regb_freq1_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask = `REGB_FREQ1_CH0_MSK_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg0_t_refi_x1_x32_mask;
   assign regb_freq1_ch0_rfshset1tmg0_t_refi_x1_x32_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_x32_mask;
   assign regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_x32_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg0_refresh_margin_mask;
   assign regb_freq1_ch0_rfshset1tmg0_refresh_margin_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG0_REFRESH_MARGIN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_sel_mask;
   assign regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_sel_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg0_t_refi_x1_sel_mask;
   assign regb_freq1_ch0_rfshset1tmg0_t_refi_x1_sel_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg1_t_rfc_min_mask;
   assign regb_freq1_ch0_rfshset1tmg1_t_rfc_min_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg1_t_rfc_min_ab_mask;
   assign regb_freq1_ch0_rfshset1tmg1_t_rfc_min_ab_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN_AB;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg2_t_pbr2pbr_mask;
   assign regb_freq1_ch0_rfshset1tmg2_t_pbr2pbr_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG2_T_PBR2PBR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg2_t_pbr2act_mask;
   assign regb_freq1_ch0_rfshset1tmg2_t_pbr2act_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG2_T_PBR2ACT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg3_refresh_to_ab_x32_mask;
   assign regb_freq1_ch0_rfshset1tmg3_refresh_to_ab_x32_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG3_REFRESH_TO_AB_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask;
   assign regb_freq1_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask;
   assign regb_freq1_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask = `REGB_FREQ1_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_rfmset1tmg0_t_rfmpb_mask;
   assign regb_freq1_ch0_rfmset1tmg0_t_rfmpb_mask = `REGB_FREQ1_CH0_MSK_RFMSET1TMG0_T_RFMPB;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_zqset1tmg0_t_zq_long_nop_mask;
   assign regb_freq1_ch0_zqset1tmg0_t_zq_long_nop_mask = `REGB_FREQ1_CH0_MSK_ZQSET1TMG0_T_ZQ_LONG_NOP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_zqset1tmg0_t_zq_short_nop_mask;
   assign regb_freq1_ch0_zqset1tmg0_t_zq_short_nop_mask = `REGB_FREQ1_CH0_MSK_ZQSET1TMG0_T_ZQ_SHORT_NOP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask;
   assign regb_freq1_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask = `REGB_FREQ1_CH0_MSK_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_zqset1tmg1_t_zq_reset_nop_mask;
   assign regb_freq1_ch0_zqset1tmg1_t_zq_reset_nop_mask = `REGB_FREQ1_CH0_MSK_ZQSET1TMG1_T_ZQ_RESET_NOP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_zqset1tmg2_t_zq_stop_mask;
   assign regb_freq1_ch0_zqset1tmg2_t_zq_stop_mask = `REGB_FREQ1_CH0_MSK_ZQSET1TMG2_T_ZQ_STOP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dqsoscctl0_dqsosc_enable_mask;
   assign regb_freq1_ch0_dqsoscctl0_dqsosc_enable_mask = `REGB_FREQ1_CH0_MSK_DQSOSCCTL0_DQSOSC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dqsoscctl0_dqsosc_interval_unit_mask;
   assign regb_freq1_ch0_dqsoscctl0_dqsosc_interval_unit_mask = `REGB_FREQ1_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dqsoscctl0_dqsosc_interval_mask;
   assign regb_freq1_ch0_dqsoscctl0_dqsosc_interval_mask = `REGB_FREQ1_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateint_mr4_read_interval_mask;
   assign regb_freq1_ch0_derateint_mr4_read_interval_mask = `REGB_FREQ1_CH0_MSK_DERATEINT_MR4_READ_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval0_derated_t_rrd_mask;
   assign regb_freq1_ch0_derateval0_derated_t_rrd_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL0_DERATED_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval0_derated_t_rp_mask;
   assign regb_freq1_ch0_derateval0_derated_t_rp_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL0_DERATED_T_RP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval0_derated_t_ras_min_mask;
   assign regb_freq1_ch0_derateval0_derated_t_ras_min_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL0_DERATED_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval0_derated_t_rcd_mask;
   assign regb_freq1_ch0_derateval0_derated_t_rcd_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL0_DERATED_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval1_derated_t_rc_mask;
   assign regb_freq1_ch0_derateval1_derated_t_rc_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL1_DERATED_T_RC;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_derateval1_derated_t_rcd_write_mask;
   assign regb_freq1_ch0_derateval1_derated_t_rcd_write_mask = `REGB_FREQ1_CH0_MSK_DERATEVAL1_DERATED_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_hwlptmg0_hw_lp_idle_x32_mask;
   assign regb_freq1_ch0_hwlptmg0_hw_lp_idle_x32_mask = `REGB_FREQ1_CH0_MSK_HWLPTMG0_HW_LP_IDLE_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_dvfsctl0_dvfsq_enable_mask;
   assign regb_freq1_ch0_dvfsctl0_dvfsq_enable_mask = `REGB_FREQ1_CH0_MSK_DVFSCTL0_DVFSQ_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_schedtmg0_pageclose_timer_mask;
   assign regb_freq1_ch0_schedtmg0_pageclose_timer_mask = `REGB_FREQ1_CH0_MSK_SCHEDTMG0_PAGECLOSE_TIMER;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_schedtmg0_rdwr_idle_gap_mask;
   assign regb_freq1_ch0_schedtmg0_rdwr_idle_gap_mask = `REGB_FREQ1_CH0_MSK_SCHEDTMG0_RDWR_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perfhpr1_hpr_max_starve_mask;
   assign regb_freq1_ch0_perfhpr1_hpr_max_starve_mask = `REGB_FREQ1_CH0_MSK_PERFHPR1_HPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perfhpr1_hpr_xact_run_length_mask;
   assign regb_freq1_ch0_perfhpr1_hpr_xact_run_length_mask = `REGB_FREQ1_CH0_MSK_PERFHPR1_HPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perflpr1_lpr_max_starve_mask;
   assign regb_freq1_ch0_perflpr1_lpr_max_starve_mask = `REGB_FREQ1_CH0_MSK_PERFLPR1_LPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perflpr1_lpr_xact_run_length_mask;
   assign regb_freq1_ch0_perflpr1_lpr_xact_run_length_mask = `REGB_FREQ1_CH0_MSK_PERFLPR1_LPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perfwr1_w_max_starve_mask;
   assign regb_freq1_ch0_perfwr1_w_max_starve_mask = `REGB_FREQ1_CH0_MSK_PERFWR1_W_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_perfwr1_w_xact_run_length_mask;
   assign regb_freq1_ch0_perfwr1_w_xact_run_length_mask = `REGB_FREQ1_CH0_MSK_PERFWR1_W_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_tmgcfg_frequency_ratio_mask;
   assign regb_freq1_ch0_tmgcfg_frequency_ratio_mask = `REGB_FREQ1_CH0_MSK_TMGCFG_FREQUENCY_RATIO;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ranktmg0_diff_rank_rd_gap_mask;
   assign regb_freq1_ch0_ranktmg0_diff_rank_rd_gap_mask = `REGB_FREQ1_CH0_MSK_RANKTMG0_DIFF_RANK_RD_GAP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ranktmg0_diff_rank_wr_gap_mask;
   assign regb_freq1_ch0_ranktmg0_diff_rank_wr_gap_mask = `REGB_FREQ1_CH0_MSK_RANKTMG0_DIFF_RANK_WR_GAP;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ranktmg1_wr2rd_dr_mask;
   assign regb_freq1_ch0_ranktmg1_wr2rd_dr_mask = `REGB_FREQ1_CH0_MSK_RANKTMG1_WR2RD_DR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ranktmg1_rd2wr_dr_mask;
   assign regb_freq1_ch0_ranktmg1_rd2wr_dr_mask = `REGB_FREQ1_CH0_MSK_RANKTMG1_RD2WR_DR;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_pwrtmg_powerdown_to_x32_mask;
   assign regb_freq1_ch0_pwrtmg_powerdown_to_x32_mask = `REGB_FREQ1_CH0_MSK_PWRTMG_POWERDOWN_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_pwrtmg_selfref_to_x32_mask;
   assign regb_freq1_ch0_pwrtmg_selfref_to_x32_mask = `REGB_FREQ1_CH0_MSK_PWRTMG_SELFREF_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask;
   assign regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask = `REGB_FREQ1_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_X1024;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask;
   assign regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask = `REGB_FREQ1_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ddr4pprtmg1_t_pgmpst_x32_mask;
   assign regb_freq1_ch0_ddr4pprtmg1_t_pgmpst_x32_mask = `REGB_FREQ1_CH0_MSK_DDR4PPRTMG1_T_PGMPST_X32;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_ddr4pprtmg1_t_pgm_exit_mask;
   assign regb_freq1_ch0_ddr4pprtmg1_t_pgm_exit_mask = `REGB_FREQ1_CH0_MSK_DDR4PPRTMG1_T_PGM_EXIT;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enable_mask;
   assign regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enable_mask = `REGB_FREQ1_CH0_MSK_LNKECCCTL0_WR_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enable_mask;
   assign regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enable_mask = `REGB_FREQ1_CH0_MSK_LNKECCCTL0_RD_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg0_t_ras_min_mask;
   assign regb_freq2_ch0_dramset1tmg0_t_ras_min_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG0_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg0_t_ras_max_mask;
   assign regb_freq2_ch0_dramset1tmg0_t_ras_max_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG0_T_RAS_MAX;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg0_t_faw_mask;
   assign regb_freq2_ch0_dramset1tmg0_t_faw_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG0_T_FAW;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg0_wr2pre_mask;
   assign regb_freq2_ch0_dramset1tmg0_wr2pre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG0_WR2PRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg1_t_rc_mask;
   assign regb_freq2_ch0_dramset1tmg1_t_rc_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG1_T_RC;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg1_rd2pre_mask;
   assign regb_freq2_ch0_dramset1tmg1_rd2pre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG1_RD2PRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg1_t_xp_mask;
   assign regb_freq2_ch0_dramset1tmg1_t_xp_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG1_T_XP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg1_t_rcd_write_mask;
   assign regb_freq2_ch0_dramset1tmg1_t_rcd_write_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG1_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg2_wr2rd_mask;
   assign regb_freq2_ch0_dramset1tmg2_wr2rd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG2_WR2RD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg2_rd2wr_mask;
   assign regb_freq2_ch0_dramset1tmg2_rd2wr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG2_RD2WR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg2_read_latency_mask;
   assign regb_freq2_ch0_dramset1tmg2_read_latency_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG2_READ_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg2_write_latency_mask;
   assign regb_freq2_ch0_dramset1tmg2_write_latency_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG2_WRITE_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg3_wr2mr_mask;
   assign regb_freq2_ch0_dramset1tmg3_wr2mr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG3_WR2MR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg3_rd2mr_mask;
   assign regb_freq2_ch0_dramset1tmg3_rd2mr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG3_RD2MR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg3_t_mr_mask;
   assign regb_freq2_ch0_dramset1tmg3_t_mr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG3_T_MR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg4_t_rp_mask;
   assign regb_freq2_ch0_dramset1tmg4_t_rp_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG4_T_RP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg4_t_rrd_mask;
   assign regb_freq2_ch0_dramset1tmg4_t_rrd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG4_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg4_t_ccd_mask;
   assign regb_freq2_ch0_dramset1tmg4_t_ccd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG4_T_CCD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg4_t_rcd_mask;
   assign regb_freq2_ch0_dramset1tmg4_t_rcd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG4_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg5_t_cke_mask;
   assign regb_freq2_ch0_dramset1tmg5_t_cke_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG5_T_CKE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg5_t_ckesr_mask;
   assign regb_freq2_ch0_dramset1tmg5_t_ckesr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG5_T_CKESR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg5_t_cksre_mask;
   assign regb_freq2_ch0_dramset1tmg5_t_cksre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG5_T_CKSRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg5_t_cksrx_mask;
   assign regb_freq2_ch0_dramset1tmg5_t_cksrx_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG5_T_CKSRX;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg6_t_ckcsx_mask;
   assign regb_freq2_ch0_dramset1tmg6_t_ckcsx_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG6_T_CKCSX;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg7_t_csh_mask;
   assign regb_freq2_ch0_dramset1tmg7_t_csh_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG7_T_CSH;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg9_wr2rd_s_mask;
   assign regb_freq2_ch0_dramset1tmg9_wr2rd_s_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG9_WR2RD_S;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg9_t_rrd_s_mask;
   assign regb_freq2_ch0_dramset1tmg9_t_rrd_s_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG9_T_RRD_S;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg9_t_ccd_s_mask;
   assign regb_freq2_ch0_dramset1tmg9_t_ccd_s_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG9_T_CCD_S;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg12_t_cmdcke_mask;
   assign regb_freq2_ch0_dramset1tmg12_t_cmdcke_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG12_T_CMDCKE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg13_t_ppd_mask;
   assign regb_freq2_ch0_dramset1tmg13_t_ppd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG13_T_PPD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg13_t_ccd_mw_mask;
   assign regb_freq2_ch0_dramset1tmg13_t_ccd_mw_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG13_T_CCD_MW;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg13_odtloff_mask;
   assign regb_freq2_ch0_dramset1tmg13_odtloff_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG13_ODTLOFF;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg14_t_xsr_mask;
   assign regb_freq2_ch0_dramset1tmg14_t_xsr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG14_T_XSR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg14_t_osco_mask;
   assign regb_freq2_ch0_dramset1tmg14_t_osco_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG14_T_OSCO;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg17_t_vrcg_disable_mask;
   assign regb_freq2_ch0_dramset1tmg17_t_vrcg_disable_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG17_T_VRCG_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg17_t_vrcg_enable_mask;
   assign regb_freq2_ch0_dramset1tmg17_t_vrcg_enable_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG17_T_VRCG_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg23_t_pdn_mask;
   assign regb_freq2_ch0_dramset1tmg23_t_pdn_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG23_T_PDN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask;
   assign regb_freq2_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG23_T_XSR_DSM_X1024;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg24_max_wr_sync_mask;
   assign regb_freq2_ch0_dramset1tmg24_max_wr_sync_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG24_MAX_WR_SYNC;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg24_max_rd_sync_mask;
   assign regb_freq2_ch0_dramset1tmg24_max_rd_sync_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG24_MAX_RD_SYNC;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg24_rd2wr_s_mask;
   assign regb_freq2_ch0_dramset1tmg24_rd2wr_s_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG24_RD2WR_S;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg24_bank_org_mask;
   assign regb_freq2_ch0_dramset1tmg24_bank_org_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG24_BANK_ORG;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg25_rda2pre_mask;
   assign regb_freq2_ch0_dramset1tmg25_rda2pre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG25_RDA2PRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg25_wra2pre_mask;
   assign regb_freq2_ch0_dramset1tmg25_wra2pre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG25_WRA2PRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask;
   assign regb_freq2_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg30_mrr2rd_mask;
   assign regb_freq2_ch0_dramset1tmg30_mrr2rd_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG30_MRR2RD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg30_mrr2wr_mask;
   assign regb_freq2_ch0_dramset1tmg30_mrr2wr_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG30_MRR2WR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg30_mrr2mrw_mask;
   assign regb_freq2_ch0_dramset1tmg30_mrr2mrw_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG30_MRR2MRW;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg32_ws_fs2wck_sus_mask;
   assign regb_freq2_ch0_dramset1tmg32_ws_fs2wck_sus_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG32_WS_FS2WCK_SUS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg32_t_wcksus_mask;
   assign regb_freq2_ch0_dramset1tmg32_t_wcksus_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG32_T_WCKSUS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dramset1tmg32_ws_off2ws_fs_mask;
   assign regb_freq2_ch0_dramset1tmg32_ws_off2ws_fs_mask = `REGB_FREQ2_CH0_MSK_DRAMSET1TMG32_WS_OFF2WS_FS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr0_emr_mask;
   assign regb_freq2_ch0_initmr0_emr_mask = `REGB_FREQ2_CH0_MSK_INITMR0_EMR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr0_mr_mask;
   assign regb_freq2_ch0_initmr0_mr_mask = `REGB_FREQ2_CH0_MSK_INITMR0_MR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr1_emr3_mask;
   assign regb_freq2_ch0_initmr1_emr3_mask = `REGB_FREQ2_CH0_MSK_INITMR1_EMR3;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr1_emr2_mask;
   assign regb_freq2_ch0_initmr1_emr2_mask = `REGB_FREQ2_CH0_MSK_INITMR1_EMR2;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr2_mr5_mask;
   assign regb_freq2_ch0_initmr2_mr5_mask = `REGB_FREQ2_CH0_MSK_INITMR2_MR5;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr2_mr4_mask;
   assign regb_freq2_ch0_initmr2_mr4_mask = `REGB_FREQ2_CH0_MSK_INITMR2_MR4;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr3_mr6_mask;
   assign regb_freq2_ch0_initmr3_mr6_mask = `REGB_FREQ2_CH0_MSK_INITMR3_MR6;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_initmr3_mr22_mask;
   assign regb_freq2_ch0_initmr3_mr22_mask = `REGB_FREQ2_CH0_MSK_INITMR3_MR22;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg0_dfi_tphy_wrlat_mask;
   assign regb_freq2_ch0_dfitmg0_dfi_tphy_wrlat_mask = `REGB_FREQ2_CH0_MSK_DFITMG0_DFI_TPHY_WRLAT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg0_dfi_tphy_wrdata_mask;
   assign regb_freq2_ch0_dfitmg0_dfi_tphy_wrdata_mask = `REGB_FREQ2_CH0_MSK_DFITMG0_DFI_TPHY_WRDATA;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg0_dfi_t_rddata_en_mask;
   assign regb_freq2_ch0_dfitmg0_dfi_t_rddata_en_mask = `REGB_FREQ2_CH0_MSK_DFITMG0_DFI_T_RDDATA_EN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg0_dfi_t_ctrl_delay_mask;
   assign regb_freq2_ch0_dfitmg0_dfi_t_ctrl_delay_mask = `REGB_FREQ2_CH0_MSK_DFITMG0_DFI_T_CTRL_DELAY;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_enable_mask;
   assign regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_enable_mask = `REGB_FREQ2_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_disable_mask;
   assign regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_disable_mask = `REGB_FREQ2_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg1_dfi_t_wrdata_delay_mask;
   assign regb_freq2_ch0_dfitmg1_dfi_t_wrdata_delay_mask = `REGB_FREQ2_CH0_MSK_DFITMG1_DFI_T_WRDATA_DELAY;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg2_dfi_tphy_wrcslat_mask;
   assign regb_freq2_ch0_dfitmg2_dfi_tphy_wrcslat_mask = `REGB_FREQ2_CH0_MSK_DFITMG2_DFI_TPHY_WRCSLAT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg2_dfi_tphy_rdcslat_mask;
   assign regb_freq2_ch0_dfitmg2_dfi_tphy_rdcslat_mask = `REGB_FREQ2_CH0_MSK_DFITMG2_DFI_TPHY_RDCSLAT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg2_dfi_twck_delay_mask;
   assign regb_freq2_ch0_dfitmg2_dfi_twck_delay_mask = `REGB_FREQ2_CH0_MSK_DFITMG2_DFI_TWCK_DELAY;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg4_dfi_twck_dis_mask;
   assign regb_freq2_ch0_dfitmg4_dfi_twck_dis_mask = `REGB_FREQ2_CH0_MSK_DFITMG4_DFI_TWCK_DIS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg4_dfi_twck_en_fs_mask;
   assign regb_freq2_ch0_dfitmg4_dfi_twck_en_fs_mask = `REGB_FREQ2_CH0_MSK_DFITMG4_DFI_TWCK_EN_FS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg4_dfi_twck_en_wr_mask;
   assign regb_freq2_ch0_dfitmg4_dfi_twck_en_wr_mask = `REGB_FREQ2_CH0_MSK_DFITMG4_DFI_TWCK_EN_WR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg4_dfi_twck_en_rd_mask;
   assign regb_freq2_ch0_dfitmg4_dfi_twck_en_rd_mask = `REGB_FREQ2_CH0_MSK_DFITMG4_DFI_TWCK_EN_RD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg5_dfi_twck_toggle_post_mask;
   assign regb_freq2_ch0_dfitmg5_dfi_twck_toggle_post_mask = `REGB_FREQ2_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_POST;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg5_dfi_twck_toggle_cs_mask;
   assign regb_freq2_ch0_dfitmg5_dfi_twck_toggle_cs_mask = `REGB_FREQ2_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_CS;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg5_dfi_twck_toggle_mask;
   assign regb_freq2_ch0_dfitmg5_dfi_twck_toggle_mask = `REGB_FREQ2_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg5_dfi_twck_fast_toggle_mask;
   assign regb_freq2_ch0_dfitmg5_dfi_twck_fast_toggle_mask = `REGB_FREQ2_CH0_MSK_DFITMG5_DFI_TWCK_FAST_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask;
   assign regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask = `REGB_FREQ2_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask;
   assign regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask = `REGB_FREQ2_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask;
   assign regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask;
   assign regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask;
   assign regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask;
   assign regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg2_ppt2_override_mask;
   assign regb_freq2_ch0_dfiupdtmg2_ppt2_override_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG2_PPT2_OVERRIDE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg2_ppt2_en_mask;
   assign regb_freq2_ch0_dfiupdtmg2_ppt2_en_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG2_PPT2_EN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask;
   assign regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask;
   assign regb_freq2_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask = `REGB_FREQ2_CH0_MSK_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg0_t_refi_x1_x32_mask;
   assign regb_freq2_ch0_rfshset1tmg0_t_refi_x1_x32_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_x32_mask;
   assign regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_x32_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg0_refresh_margin_mask;
   assign regb_freq2_ch0_rfshset1tmg0_refresh_margin_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG0_REFRESH_MARGIN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_sel_mask;
   assign regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_sel_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg0_t_refi_x1_sel_mask;
   assign regb_freq2_ch0_rfshset1tmg0_t_refi_x1_sel_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg1_t_rfc_min_mask;
   assign regb_freq2_ch0_rfshset1tmg1_t_rfc_min_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg1_t_rfc_min_ab_mask;
   assign regb_freq2_ch0_rfshset1tmg1_t_rfc_min_ab_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN_AB;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg2_t_pbr2pbr_mask;
   assign regb_freq2_ch0_rfshset1tmg2_t_pbr2pbr_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG2_T_PBR2PBR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg2_t_pbr2act_mask;
   assign regb_freq2_ch0_rfshset1tmg2_t_pbr2act_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG2_T_PBR2ACT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg3_refresh_to_ab_x32_mask;
   assign regb_freq2_ch0_rfshset1tmg3_refresh_to_ab_x32_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG3_REFRESH_TO_AB_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask;
   assign regb_freq2_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask;
   assign regb_freq2_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask = `REGB_FREQ2_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_rfmset1tmg0_t_rfmpb_mask;
   assign regb_freq2_ch0_rfmset1tmg0_t_rfmpb_mask = `REGB_FREQ2_CH0_MSK_RFMSET1TMG0_T_RFMPB;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_zqset1tmg0_t_zq_long_nop_mask;
   assign regb_freq2_ch0_zqset1tmg0_t_zq_long_nop_mask = `REGB_FREQ2_CH0_MSK_ZQSET1TMG0_T_ZQ_LONG_NOP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_zqset1tmg0_t_zq_short_nop_mask;
   assign regb_freq2_ch0_zqset1tmg0_t_zq_short_nop_mask = `REGB_FREQ2_CH0_MSK_ZQSET1TMG0_T_ZQ_SHORT_NOP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask;
   assign regb_freq2_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask = `REGB_FREQ2_CH0_MSK_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_zqset1tmg1_t_zq_reset_nop_mask;
   assign regb_freq2_ch0_zqset1tmg1_t_zq_reset_nop_mask = `REGB_FREQ2_CH0_MSK_ZQSET1TMG1_T_ZQ_RESET_NOP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_zqset1tmg2_t_zq_stop_mask;
   assign regb_freq2_ch0_zqset1tmg2_t_zq_stop_mask = `REGB_FREQ2_CH0_MSK_ZQSET1TMG2_T_ZQ_STOP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dqsoscctl0_dqsosc_enable_mask;
   assign regb_freq2_ch0_dqsoscctl0_dqsosc_enable_mask = `REGB_FREQ2_CH0_MSK_DQSOSCCTL0_DQSOSC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dqsoscctl0_dqsosc_interval_unit_mask;
   assign regb_freq2_ch0_dqsoscctl0_dqsosc_interval_unit_mask = `REGB_FREQ2_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dqsoscctl0_dqsosc_interval_mask;
   assign regb_freq2_ch0_dqsoscctl0_dqsosc_interval_mask = `REGB_FREQ2_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateint_mr4_read_interval_mask;
   assign regb_freq2_ch0_derateint_mr4_read_interval_mask = `REGB_FREQ2_CH0_MSK_DERATEINT_MR4_READ_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval0_derated_t_rrd_mask;
   assign regb_freq2_ch0_derateval0_derated_t_rrd_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL0_DERATED_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval0_derated_t_rp_mask;
   assign regb_freq2_ch0_derateval0_derated_t_rp_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL0_DERATED_T_RP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval0_derated_t_ras_min_mask;
   assign regb_freq2_ch0_derateval0_derated_t_ras_min_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL0_DERATED_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval0_derated_t_rcd_mask;
   assign regb_freq2_ch0_derateval0_derated_t_rcd_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL0_DERATED_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval1_derated_t_rc_mask;
   assign regb_freq2_ch0_derateval1_derated_t_rc_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL1_DERATED_T_RC;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_derateval1_derated_t_rcd_write_mask;
   assign regb_freq2_ch0_derateval1_derated_t_rcd_write_mask = `REGB_FREQ2_CH0_MSK_DERATEVAL1_DERATED_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_hwlptmg0_hw_lp_idle_x32_mask;
   assign regb_freq2_ch0_hwlptmg0_hw_lp_idle_x32_mask = `REGB_FREQ2_CH0_MSK_HWLPTMG0_HW_LP_IDLE_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_dvfsctl0_dvfsq_enable_mask;
   assign regb_freq2_ch0_dvfsctl0_dvfsq_enable_mask = `REGB_FREQ2_CH0_MSK_DVFSCTL0_DVFSQ_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_schedtmg0_pageclose_timer_mask;
   assign regb_freq2_ch0_schedtmg0_pageclose_timer_mask = `REGB_FREQ2_CH0_MSK_SCHEDTMG0_PAGECLOSE_TIMER;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_schedtmg0_rdwr_idle_gap_mask;
   assign regb_freq2_ch0_schedtmg0_rdwr_idle_gap_mask = `REGB_FREQ2_CH0_MSK_SCHEDTMG0_RDWR_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perfhpr1_hpr_max_starve_mask;
   assign regb_freq2_ch0_perfhpr1_hpr_max_starve_mask = `REGB_FREQ2_CH0_MSK_PERFHPR1_HPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perfhpr1_hpr_xact_run_length_mask;
   assign regb_freq2_ch0_perfhpr1_hpr_xact_run_length_mask = `REGB_FREQ2_CH0_MSK_PERFHPR1_HPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perflpr1_lpr_max_starve_mask;
   assign regb_freq2_ch0_perflpr1_lpr_max_starve_mask = `REGB_FREQ2_CH0_MSK_PERFLPR1_LPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perflpr1_lpr_xact_run_length_mask;
   assign regb_freq2_ch0_perflpr1_lpr_xact_run_length_mask = `REGB_FREQ2_CH0_MSK_PERFLPR1_LPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perfwr1_w_max_starve_mask;
   assign regb_freq2_ch0_perfwr1_w_max_starve_mask = `REGB_FREQ2_CH0_MSK_PERFWR1_W_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_perfwr1_w_xact_run_length_mask;
   assign regb_freq2_ch0_perfwr1_w_xact_run_length_mask = `REGB_FREQ2_CH0_MSK_PERFWR1_W_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_tmgcfg_frequency_ratio_mask;
   assign regb_freq2_ch0_tmgcfg_frequency_ratio_mask = `REGB_FREQ2_CH0_MSK_TMGCFG_FREQUENCY_RATIO;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ranktmg0_diff_rank_rd_gap_mask;
   assign regb_freq2_ch0_ranktmg0_diff_rank_rd_gap_mask = `REGB_FREQ2_CH0_MSK_RANKTMG0_DIFF_RANK_RD_GAP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ranktmg0_diff_rank_wr_gap_mask;
   assign regb_freq2_ch0_ranktmg0_diff_rank_wr_gap_mask = `REGB_FREQ2_CH0_MSK_RANKTMG0_DIFF_RANK_WR_GAP;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ranktmg1_wr2rd_dr_mask;
   assign regb_freq2_ch0_ranktmg1_wr2rd_dr_mask = `REGB_FREQ2_CH0_MSK_RANKTMG1_WR2RD_DR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ranktmg1_rd2wr_dr_mask;
   assign regb_freq2_ch0_ranktmg1_rd2wr_dr_mask = `REGB_FREQ2_CH0_MSK_RANKTMG1_RD2WR_DR;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_pwrtmg_powerdown_to_x32_mask;
   assign regb_freq2_ch0_pwrtmg_powerdown_to_x32_mask = `REGB_FREQ2_CH0_MSK_PWRTMG_POWERDOWN_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_pwrtmg_selfref_to_x32_mask;
   assign regb_freq2_ch0_pwrtmg_selfref_to_x32_mask = `REGB_FREQ2_CH0_MSK_PWRTMG_SELFREF_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask;
   assign regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask = `REGB_FREQ2_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_X1024;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask;
   assign regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask = `REGB_FREQ2_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ddr4pprtmg1_t_pgmpst_x32_mask;
   assign regb_freq2_ch0_ddr4pprtmg1_t_pgmpst_x32_mask = `REGB_FREQ2_CH0_MSK_DDR4PPRTMG1_T_PGMPST_X32;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_ddr4pprtmg1_t_pgm_exit_mask;
   assign regb_freq2_ch0_ddr4pprtmg1_t_pgm_exit_mask = `REGB_FREQ2_CH0_MSK_DDR4PPRTMG1_T_PGM_EXIT;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enable_mask;
   assign regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enable_mask = `REGB_FREQ2_CH0_MSK_LNKECCCTL0_WR_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enable_mask;
   assign regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enable_mask = `REGB_FREQ2_CH0_MSK_LNKECCCTL0_RD_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg0_t_ras_min_mask;
   assign regb_freq3_ch0_dramset1tmg0_t_ras_min_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG0_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg0_t_ras_max_mask;
   assign regb_freq3_ch0_dramset1tmg0_t_ras_max_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG0_T_RAS_MAX;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg0_t_faw_mask;
   assign regb_freq3_ch0_dramset1tmg0_t_faw_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG0_T_FAW;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg0_wr2pre_mask;
   assign regb_freq3_ch0_dramset1tmg0_wr2pre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG0_WR2PRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg1_t_rc_mask;
   assign regb_freq3_ch0_dramset1tmg1_t_rc_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG1_T_RC;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg1_rd2pre_mask;
   assign regb_freq3_ch0_dramset1tmg1_rd2pre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG1_RD2PRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg1_t_xp_mask;
   assign regb_freq3_ch0_dramset1tmg1_t_xp_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG1_T_XP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg1_t_rcd_write_mask;
   assign regb_freq3_ch0_dramset1tmg1_t_rcd_write_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG1_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg2_wr2rd_mask;
   assign regb_freq3_ch0_dramset1tmg2_wr2rd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG2_WR2RD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg2_rd2wr_mask;
   assign regb_freq3_ch0_dramset1tmg2_rd2wr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG2_RD2WR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg2_read_latency_mask;
   assign regb_freq3_ch0_dramset1tmg2_read_latency_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG2_READ_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg2_write_latency_mask;
   assign regb_freq3_ch0_dramset1tmg2_write_latency_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG2_WRITE_LATENCY;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg3_wr2mr_mask;
   assign regb_freq3_ch0_dramset1tmg3_wr2mr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG3_WR2MR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg3_rd2mr_mask;
   assign regb_freq3_ch0_dramset1tmg3_rd2mr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG3_RD2MR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg3_t_mr_mask;
   assign regb_freq3_ch0_dramset1tmg3_t_mr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG3_T_MR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg4_t_rp_mask;
   assign regb_freq3_ch0_dramset1tmg4_t_rp_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG4_T_RP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg4_t_rrd_mask;
   assign regb_freq3_ch0_dramset1tmg4_t_rrd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG4_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg4_t_ccd_mask;
   assign regb_freq3_ch0_dramset1tmg4_t_ccd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG4_T_CCD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg4_t_rcd_mask;
   assign regb_freq3_ch0_dramset1tmg4_t_rcd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG4_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg5_t_cke_mask;
   assign regb_freq3_ch0_dramset1tmg5_t_cke_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG5_T_CKE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg5_t_ckesr_mask;
   assign regb_freq3_ch0_dramset1tmg5_t_ckesr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG5_T_CKESR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg5_t_cksre_mask;
   assign regb_freq3_ch0_dramset1tmg5_t_cksre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG5_T_CKSRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg5_t_cksrx_mask;
   assign regb_freq3_ch0_dramset1tmg5_t_cksrx_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG5_T_CKSRX;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg6_t_ckcsx_mask;
   assign regb_freq3_ch0_dramset1tmg6_t_ckcsx_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG6_T_CKCSX;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg7_t_csh_mask;
   assign regb_freq3_ch0_dramset1tmg7_t_csh_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG7_T_CSH;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg9_wr2rd_s_mask;
   assign regb_freq3_ch0_dramset1tmg9_wr2rd_s_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG9_WR2RD_S;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg9_t_rrd_s_mask;
   assign regb_freq3_ch0_dramset1tmg9_t_rrd_s_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG9_T_RRD_S;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg9_t_ccd_s_mask;
   assign regb_freq3_ch0_dramset1tmg9_t_ccd_s_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG9_T_CCD_S;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg12_t_cmdcke_mask;
   assign regb_freq3_ch0_dramset1tmg12_t_cmdcke_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG12_T_CMDCKE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg13_t_ppd_mask;
   assign regb_freq3_ch0_dramset1tmg13_t_ppd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG13_T_PPD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg13_t_ccd_mw_mask;
   assign regb_freq3_ch0_dramset1tmg13_t_ccd_mw_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG13_T_CCD_MW;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg13_odtloff_mask;
   assign regb_freq3_ch0_dramset1tmg13_odtloff_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG13_ODTLOFF;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg14_t_xsr_mask;
   assign regb_freq3_ch0_dramset1tmg14_t_xsr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG14_T_XSR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg14_t_osco_mask;
   assign regb_freq3_ch0_dramset1tmg14_t_osco_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG14_T_OSCO;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg17_t_vrcg_disable_mask;
   assign regb_freq3_ch0_dramset1tmg17_t_vrcg_disable_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG17_T_VRCG_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg17_t_vrcg_enable_mask;
   assign regb_freq3_ch0_dramset1tmg17_t_vrcg_enable_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG17_T_VRCG_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg23_t_pdn_mask;
   assign regb_freq3_ch0_dramset1tmg23_t_pdn_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG23_T_PDN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask;
   assign regb_freq3_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG23_T_XSR_DSM_X1024;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg24_max_wr_sync_mask;
   assign regb_freq3_ch0_dramset1tmg24_max_wr_sync_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG24_MAX_WR_SYNC;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg24_max_rd_sync_mask;
   assign regb_freq3_ch0_dramset1tmg24_max_rd_sync_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG24_MAX_RD_SYNC;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg24_rd2wr_s_mask;
   assign regb_freq3_ch0_dramset1tmg24_rd2wr_s_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG24_RD2WR_S;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg24_bank_org_mask;
   assign regb_freq3_ch0_dramset1tmg24_bank_org_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG24_BANK_ORG;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg25_rda2pre_mask;
   assign regb_freq3_ch0_dramset1tmg25_rda2pre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG25_RDA2PRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg25_wra2pre_mask;
   assign regb_freq3_ch0_dramset1tmg25_wra2pre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG25_WRA2PRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask;
   assign regb_freq3_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg30_mrr2rd_mask;
   assign regb_freq3_ch0_dramset1tmg30_mrr2rd_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG30_MRR2RD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg30_mrr2wr_mask;
   assign regb_freq3_ch0_dramset1tmg30_mrr2wr_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG30_MRR2WR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg30_mrr2mrw_mask;
   assign regb_freq3_ch0_dramset1tmg30_mrr2mrw_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG30_MRR2MRW;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg32_ws_fs2wck_sus_mask;
   assign regb_freq3_ch0_dramset1tmg32_ws_fs2wck_sus_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG32_WS_FS2WCK_SUS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg32_t_wcksus_mask;
   assign regb_freq3_ch0_dramset1tmg32_t_wcksus_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG32_T_WCKSUS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dramset1tmg32_ws_off2ws_fs_mask;
   assign regb_freq3_ch0_dramset1tmg32_ws_off2ws_fs_mask = `REGB_FREQ3_CH0_MSK_DRAMSET1TMG32_WS_OFF2WS_FS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr0_emr_mask;
   assign regb_freq3_ch0_initmr0_emr_mask = `REGB_FREQ3_CH0_MSK_INITMR0_EMR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr0_mr_mask;
   assign regb_freq3_ch0_initmr0_mr_mask = `REGB_FREQ3_CH0_MSK_INITMR0_MR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr1_emr3_mask;
   assign regb_freq3_ch0_initmr1_emr3_mask = `REGB_FREQ3_CH0_MSK_INITMR1_EMR3;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr1_emr2_mask;
   assign regb_freq3_ch0_initmr1_emr2_mask = `REGB_FREQ3_CH0_MSK_INITMR1_EMR2;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr2_mr5_mask;
   assign regb_freq3_ch0_initmr2_mr5_mask = `REGB_FREQ3_CH0_MSK_INITMR2_MR5;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr2_mr4_mask;
   assign regb_freq3_ch0_initmr2_mr4_mask = `REGB_FREQ3_CH0_MSK_INITMR2_MR4;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr3_mr6_mask;
   assign regb_freq3_ch0_initmr3_mr6_mask = `REGB_FREQ3_CH0_MSK_INITMR3_MR6;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_initmr3_mr22_mask;
   assign regb_freq3_ch0_initmr3_mr22_mask = `REGB_FREQ3_CH0_MSK_INITMR3_MR22;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg0_dfi_tphy_wrlat_mask;
   assign regb_freq3_ch0_dfitmg0_dfi_tphy_wrlat_mask = `REGB_FREQ3_CH0_MSK_DFITMG0_DFI_TPHY_WRLAT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg0_dfi_tphy_wrdata_mask;
   assign regb_freq3_ch0_dfitmg0_dfi_tphy_wrdata_mask = `REGB_FREQ3_CH0_MSK_DFITMG0_DFI_TPHY_WRDATA;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg0_dfi_t_rddata_en_mask;
   assign regb_freq3_ch0_dfitmg0_dfi_t_rddata_en_mask = `REGB_FREQ3_CH0_MSK_DFITMG0_DFI_T_RDDATA_EN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg0_dfi_t_ctrl_delay_mask;
   assign regb_freq3_ch0_dfitmg0_dfi_t_ctrl_delay_mask = `REGB_FREQ3_CH0_MSK_DFITMG0_DFI_T_CTRL_DELAY;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_enable_mask;
   assign regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_enable_mask = `REGB_FREQ3_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_disable_mask;
   assign regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_disable_mask = `REGB_FREQ3_CH0_MSK_DFITMG1_DFI_T_DRAM_CLK_DISABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg1_dfi_t_wrdata_delay_mask;
   assign regb_freq3_ch0_dfitmg1_dfi_t_wrdata_delay_mask = `REGB_FREQ3_CH0_MSK_DFITMG1_DFI_T_WRDATA_DELAY;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg2_dfi_tphy_wrcslat_mask;
   assign regb_freq3_ch0_dfitmg2_dfi_tphy_wrcslat_mask = `REGB_FREQ3_CH0_MSK_DFITMG2_DFI_TPHY_WRCSLAT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg2_dfi_tphy_rdcslat_mask;
   assign regb_freq3_ch0_dfitmg2_dfi_tphy_rdcslat_mask = `REGB_FREQ3_CH0_MSK_DFITMG2_DFI_TPHY_RDCSLAT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg2_dfi_twck_delay_mask;
   assign regb_freq3_ch0_dfitmg2_dfi_twck_delay_mask = `REGB_FREQ3_CH0_MSK_DFITMG2_DFI_TWCK_DELAY;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg4_dfi_twck_dis_mask;
   assign regb_freq3_ch0_dfitmg4_dfi_twck_dis_mask = `REGB_FREQ3_CH0_MSK_DFITMG4_DFI_TWCK_DIS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg4_dfi_twck_en_fs_mask;
   assign regb_freq3_ch0_dfitmg4_dfi_twck_en_fs_mask = `REGB_FREQ3_CH0_MSK_DFITMG4_DFI_TWCK_EN_FS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg4_dfi_twck_en_wr_mask;
   assign regb_freq3_ch0_dfitmg4_dfi_twck_en_wr_mask = `REGB_FREQ3_CH0_MSK_DFITMG4_DFI_TWCK_EN_WR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg4_dfi_twck_en_rd_mask;
   assign regb_freq3_ch0_dfitmg4_dfi_twck_en_rd_mask = `REGB_FREQ3_CH0_MSK_DFITMG4_DFI_TWCK_EN_RD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg5_dfi_twck_toggle_post_mask;
   assign regb_freq3_ch0_dfitmg5_dfi_twck_toggle_post_mask = `REGB_FREQ3_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_POST;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg5_dfi_twck_toggle_cs_mask;
   assign regb_freq3_ch0_dfitmg5_dfi_twck_toggle_cs_mask = `REGB_FREQ3_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE_CS;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg5_dfi_twck_toggle_mask;
   assign regb_freq3_ch0_dfitmg5_dfi_twck_toggle_mask = `REGB_FREQ3_CH0_MSK_DFITMG5_DFI_TWCK_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg5_dfi_twck_fast_toggle_mask;
   assign regb_freq3_ch0_dfitmg5_dfi_twck_fast_toggle_mask = `REGB_FREQ3_CH0_MSK_DFITMG5_DFI_TWCK_FAST_TOGGLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask;
   assign regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask = `REGB_FREQ3_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask;
   assign regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask = `REGB_FREQ3_CH0_MSK_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask;
   assign regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask;
   assign regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask;
   assign regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask;
   assign regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg2_ppt2_override_mask;
   assign regb_freq3_ch0_dfiupdtmg2_ppt2_override_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG2_PPT2_OVERRIDE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg2_ppt2_en_mask;
   assign regb_freq3_ch0_dfiupdtmg2_ppt2_en_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG2_PPT2_EN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask;
   assign regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask;
   assign regb_freq3_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask = `REGB_FREQ3_CH0_MSK_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg0_t_refi_x1_x32_mask;
   assign regb_freq3_ch0_rfshset1tmg0_t_refi_x1_x32_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_x32_mask;
   assign regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_x32_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg0_refresh_margin_mask;
   assign regb_freq3_ch0_rfshset1tmg0_refresh_margin_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG0_REFRESH_MARGIN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_sel_mask;
   assign regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_sel_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG0_REFRESH_TO_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg0_t_refi_x1_sel_mask;
   assign regb_freq3_ch0_rfshset1tmg0_t_refi_x1_sel_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG0_T_REFI_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg1_t_rfc_min_mask;
   assign regb_freq3_ch0_rfshset1tmg1_t_rfc_min_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg1_t_rfc_min_ab_mask;
   assign regb_freq3_ch0_rfshset1tmg1_t_rfc_min_ab_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG1_T_RFC_MIN_AB;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg2_t_pbr2pbr_mask;
   assign regb_freq3_ch0_rfshset1tmg2_t_pbr2pbr_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG2_T_PBR2PBR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg2_t_pbr2act_mask;
   assign regb_freq3_ch0_rfshset1tmg2_t_pbr2act_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG2_T_PBR2ACT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg3_refresh_to_ab_x32_mask;
   assign regb_freq3_ch0_rfshset1tmg3_refresh_to_ab_x32_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG3_REFRESH_TO_AB_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask;
   assign regb_freq3_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask;
   assign regb_freq3_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask = `REGB_FREQ3_CH0_MSK_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_rfmset1tmg0_t_rfmpb_mask;
   assign regb_freq3_ch0_rfmset1tmg0_t_rfmpb_mask = `REGB_FREQ3_CH0_MSK_RFMSET1TMG0_T_RFMPB;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_zqset1tmg0_t_zq_long_nop_mask;
   assign regb_freq3_ch0_zqset1tmg0_t_zq_long_nop_mask = `REGB_FREQ3_CH0_MSK_ZQSET1TMG0_T_ZQ_LONG_NOP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_zqset1tmg0_t_zq_short_nop_mask;
   assign regb_freq3_ch0_zqset1tmg0_t_zq_short_nop_mask = `REGB_FREQ3_CH0_MSK_ZQSET1TMG0_T_ZQ_SHORT_NOP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask;
   assign regb_freq3_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask = `REGB_FREQ3_CH0_MSK_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_zqset1tmg1_t_zq_reset_nop_mask;
   assign regb_freq3_ch0_zqset1tmg1_t_zq_reset_nop_mask = `REGB_FREQ3_CH0_MSK_ZQSET1TMG1_T_ZQ_RESET_NOP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_zqset1tmg2_t_zq_stop_mask;
   assign regb_freq3_ch0_zqset1tmg2_t_zq_stop_mask = `REGB_FREQ3_CH0_MSK_ZQSET1TMG2_T_ZQ_STOP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dqsoscctl0_dqsosc_enable_mask;
   assign regb_freq3_ch0_dqsoscctl0_dqsosc_enable_mask = `REGB_FREQ3_CH0_MSK_DQSOSCCTL0_DQSOSC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dqsoscctl0_dqsosc_interval_unit_mask;
   assign regb_freq3_ch0_dqsoscctl0_dqsosc_interval_unit_mask = `REGB_FREQ3_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dqsoscctl0_dqsosc_interval_mask;
   assign regb_freq3_ch0_dqsoscctl0_dqsosc_interval_mask = `REGB_FREQ3_CH0_MSK_DQSOSCCTL0_DQSOSC_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateint_mr4_read_interval_mask;
   assign regb_freq3_ch0_derateint_mr4_read_interval_mask = `REGB_FREQ3_CH0_MSK_DERATEINT_MR4_READ_INTERVAL;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval0_derated_t_rrd_mask;
   assign regb_freq3_ch0_derateval0_derated_t_rrd_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL0_DERATED_T_RRD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval0_derated_t_rp_mask;
   assign regb_freq3_ch0_derateval0_derated_t_rp_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL0_DERATED_T_RP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval0_derated_t_ras_min_mask;
   assign regb_freq3_ch0_derateval0_derated_t_ras_min_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL0_DERATED_T_RAS_MIN;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval0_derated_t_rcd_mask;
   assign regb_freq3_ch0_derateval0_derated_t_rcd_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL0_DERATED_T_RCD;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval1_derated_t_rc_mask;
   assign regb_freq3_ch0_derateval1_derated_t_rc_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL1_DERATED_T_RC;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_derateval1_derated_t_rcd_write_mask;
   assign regb_freq3_ch0_derateval1_derated_t_rcd_write_mask = `REGB_FREQ3_CH0_MSK_DERATEVAL1_DERATED_T_RCD_WRITE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_hwlptmg0_hw_lp_idle_x32_mask;
   assign regb_freq3_ch0_hwlptmg0_hw_lp_idle_x32_mask = `REGB_FREQ3_CH0_MSK_HWLPTMG0_HW_LP_IDLE_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_dvfsctl0_dvfsq_enable_mask;
   assign regb_freq3_ch0_dvfsctl0_dvfsq_enable_mask = `REGB_FREQ3_CH0_MSK_DVFSCTL0_DVFSQ_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_schedtmg0_pageclose_timer_mask;
   assign regb_freq3_ch0_schedtmg0_pageclose_timer_mask = `REGB_FREQ3_CH0_MSK_SCHEDTMG0_PAGECLOSE_TIMER;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_schedtmg0_rdwr_idle_gap_mask;
   assign regb_freq3_ch0_schedtmg0_rdwr_idle_gap_mask = `REGB_FREQ3_CH0_MSK_SCHEDTMG0_RDWR_IDLE_GAP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perfhpr1_hpr_max_starve_mask;
   assign regb_freq3_ch0_perfhpr1_hpr_max_starve_mask = `REGB_FREQ3_CH0_MSK_PERFHPR1_HPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perfhpr1_hpr_xact_run_length_mask;
   assign regb_freq3_ch0_perfhpr1_hpr_xact_run_length_mask = `REGB_FREQ3_CH0_MSK_PERFHPR1_HPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perflpr1_lpr_max_starve_mask;
   assign regb_freq3_ch0_perflpr1_lpr_max_starve_mask = `REGB_FREQ3_CH0_MSK_PERFLPR1_LPR_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perflpr1_lpr_xact_run_length_mask;
   assign regb_freq3_ch0_perflpr1_lpr_xact_run_length_mask = `REGB_FREQ3_CH0_MSK_PERFLPR1_LPR_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perfwr1_w_max_starve_mask;
   assign regb_freq3_ch0_perfwr1_w_max_starve_mask = `REGB_FREQ3_CH0_MSK_PERFWR1_W_MAX_STARVE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_perfwr1_w_xact_run_length_mask;
   assign regb_freq3_ch0_perfwr1_w_xact_run_length_mask = `REGB_FREQ3_CH0_MSK_PERFWR1_W_XACT_RUN_LENGTH;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_tmgcfg_frequency_ratio_mask;
   assign regb_freq3_ch0_tmgcfg_frequency_ratio_mask = `REGB_FREQ3_CH0_MSK_TMGCFG_FREQUENCY_RATIO;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ranktmg0_diff_rank_rd_gap_mask;
   assign regb_freq3_ch0_ranktmg0_diff_rank_rd_gap_mask = `REGB_FREQ3_CH0_MSK_RANKTMG0_DIFF_RANK_RD_GAP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ranktmg0_diff_rank_wr_gap_mask;
   assign regb_freq3_ch0_ranktmg0_diff_rank_wr_gap_mask = `REGB_FREQ3_CH0_MSK_RANKTMG0_DIFF_RANK_WR_GAP;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ranktmg1_wr2rd_dr_mask;
   assign regb_freq3_ch0_ranktmg1_wr2rd_dr_mask = `REGB_FREQ3_CH0_MSK_RANKTMG1_WR2RD_DR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ranktmg1_rd2wr_dr_mask;
   assign regb_freq3_ch0_ranktmg1_rd2wr_dr_mask = `REGB_FREQ3_CH0_MSK_RANKTMG1_RD2WR_DR;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_pwrtmg_powerdown_to_x32_mask;
   assign regb_freq3_ch0_pwrtmg_powerdown_to_x32_mask = `REGB_FREQ3_CH0_MSK_PWRTMG_POWERDOWN_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_pwrtmg_selfref_to_x32_mask;
   assign regb_freq3_ch0_pwrtmg_selfref_to_x32_mask = `REGB_FREQ3_CH0_MSK_PWRTMG_SELFREF_TO_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask;
   assign regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask = `REGB_FREQ3_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_X1024;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask;
   assign regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask = `REGB_FREQ3_CH0_MSK_DDR4PPRTMG0_T_PGM_X1_SEL;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ddr4pprtmg1_t_pgmpst_x32_mask;
   assign regb_freq3_ch0_ddr4pprtmg1_t_pgmpst_x32_mask = `REGB_FREQ3_CH0_MSK_DDR4PPRTMG1_T_PGMPST_X32;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_ddr4pprtmg1_t_pgm_exit_mask;
   assign regb_freq3_ch0_ddr4pprtmg1_t_pgm_exit_mask = `REGB_FREQ3_CH0_MSK_DDR4PPRTMG1_T_PGM_EXIT;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enable_mask;
   assign regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enable_mask = `REGB_FREQ3_CH0_MSK_LNKECCCTL0_WR_LINK_ECC_ENABLE;
   wire [REG_WIDTH-1:0] regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enable_mask;
   assign regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enable_mask = `REGB_FREQ3_CH0_MSK_LNKECCCTL0_RD_LINK_ECC_ENABLE;

   reg ff_regb_ddrc_ch0_lpddr4;
   reg ff_regb_ddrc_ch0_lpddr5;
   reg ff_regb_ddrc_ch0_lpddr5x;
   reg [`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH-1:0] ff_regb_ddrc_ch0_data_bus_width;
   reg [`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR-1:0] ff_regb_ddrc_ch0_burst_rdwr;
   reg [`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS-1:0] ff_regb_ddrc_ch0_active_ranks;
   reg [`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY-1:0] ff_regb_ddrc_ch0_target_frequency;
   reg ff_regb_ddrc_ch0_wck_on;
   reg ff_regb_ddrc_ch0_wck_suspend_en;
   reg ff_regb_ddrc_ch0_ws_off_en;
   reg ff_regb_ddrc_ch0_mr_type;
   reg ff_regb_ddrc_ch0_sw_init_int;
   reg [`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK-1:0] ff_regb_ddrc_ch0_mr_rank;
   reg [`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR-1:0] ff_regb_ddrc_ch0_mr_addr;
   reg ff_regb_ddrc_ch0_mrr_done_clr;
   reg ff_regb_ddrc_ch0_dis_mrrw_trfc;
   reg ff_regb_ddrc_ch0_ppr_en;
   reg ff_regb_ddrc_ch0_ppr_pgmpst_en;
   reg ff_regb_ddrc_ch0_mr_wr_todo;
   reg ff_regb_ddrc_ch0_mr_wr;
   reg [`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA-1:0] ff_regb_ddrc_ch0_mr_data;
   reg ff_regb_ddrc_ch0_derate_enable;
   reg ff_regb_ddrc_ch0_lpddr4_refresh_mode;
   reg ff_regb_ddrc_ch0_derate_mr4_pause_fc;
   reg ff_regb_ddrc_ch0_dis_trefi_x6x8;
   reg ff_regb_ddrc_ch0_dis_trefi_x0125;
   reg ff_regb_ddrc_ch0_use_slow_rm_in_low_temp;
   reg [`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0-1:0] ff_regb_ddrc_ch0_active_derate_byte_rank0;
   reg [`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1-1:0] ff_regb_ddrc_ch0_active_derate_byte_rank1;
   reg cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_en;
   reg cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr;
   reg cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force;
   reg ff_regb_ddrc_ch0_derate_mr4_tuf_dis;
   reg [`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL-1:0] ff_regb_ddrc_ch0_dbg_mr4_rank_sel;
   reg [`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN-1:0] ff_regb_ddrc_ch0_selfref_en;
   reg [`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN-1:0] ff_regb_ddrc_ch0_powerdown_en;
   reg ff_regb_ddrc_ch0_en_dfi_dram_clk_disable;
   reg ff_regb_ddrc_ch0_selfref_sw;
   reg ff_regb_ddrc_ch0_stay_in_selfref;
   reg ff_regb_ddrc_ch0_dis_cam_drain_selfref;
   reg ff_regb_ddrc_ch0_lpddr4_sr_allowed;
   reg ff_regb_ddrc_ch0_dsm_en;
   reg ff_regb_ddrc_ch0_hw_lp_en;
   reg ff_regb_ddrc_ch0_hw_lp_exit_idle_en;
   reg [`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON-1:0] ff_regb_ddrc_ch0_bsm_clk_on;
   reg [`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST-1:0] ff_regb_ddrc_ch0_refresh_burst;
   reg [`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN-1:0] ff_regb_ddrc_ch0_auto_refab_en;
   reg ff_regb_ddrc_ch0_per_bank_refresh;
   reg ff_regb_ddrc_ch0_per_bank_refresh_opt_en;
   reg ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en;
   reg ff_regb_ddrc_ch0_dis_auto_refresh;
   reg ff_regb_ddrc_ch0_refresh_update_level;
   reg ff_regb_ddrc_ch0_rfm_en;
   reg ff_regb_ddrc_ch0_rfmsbc;
   reg [`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT-1:0] ff_regb_ddrc_ch0_raaimt;
   reg [`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT-1:0] ff_regb_ddrc_ch0_raamult;
   reg [`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC-1:0] ff_regb_ddrc_ch0_raadec;
   reg [`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR-1:0] ff_regb_ddrc_ch0_rfmth_rm_thr;
   reg [`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT-1:0] ff_regb_ddrc_ch0_init_raa_cnt;
   reg [`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK-1:0] ff_regb_ddrc_ch0_dbg_raa_rank;
   reg [`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK-1:0] ff_regb_ddrc_ch0_dbg_raa_bg_bank;
   reg ff_regb_ddrc_ch0_zq_resistor_shared;
   reg ff_regb_ddrc_ch0_dis_auto_zq;
   reg ff_regb_ddrc_ch0_zq_reset_todo;
   reg ff_regb_ddrc_ch0_zq_reset;
   reg cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl;
   reg cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl_hwffc;
   reg [`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME-1:0] cfgs_ff_regb_ddrc_ch0_dqsosc_runtime;
   reg [`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME-1:0] cfgs_ff_regb_ddrc_ch0_wck2dqo_runtime;
   reg cfgs_ff_regb_ddrc_ch0_dis_dqsosc_srx;
   reg cfgs_ff_regb_ddrc_ch0_dis_opt_wrecc_collision_flush;
   reg cfgs_ff_regb_ddrc_ch0_prefer_write;
   reg cfgs_ff_regb_ddrc_ch0_pageclose;
   reg cfgs_ff_regb_ddrc_ch0_opt_wrcam_fill_level;
   reg cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_act;
   reg cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_pre;
   reg cfgs_ff_regb_ddrc_ch0_autopre_rmw;
   reg [`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES-1:0] cfgs_ff_regb_ddrc_ch0_lpr_num_entries;
   reg cfgs_ff_regb_ddrc_ch0_lpddr4_opt_act_timing;
   reg cfgs_ff_regb_ddrc_ch0_lpddr5_opt_act_timing;
   reg cfgs_ff_regb_ddrc_ch0_w_starve_free_running;
   reg cfgs_ff_regb_ddrc_ch0_opt_act_lat;
   reg cfgs_ff_regb_ddrc_ch0_prefer_read;
   reg cfgs_ff_regb_ddrc_ch0_dis_speculative_act;
   reg cfgs_ff_regb_ddrc_ch0_opt_vprw_sch;
   reg [`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE-1:0] cfgs_ff_regb_ddrc_ch0_delay_switch_write;
   reg [`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR-1:0] cfgs_ff_regb_ddrc_ch0_visible_window_limit_wr;
   reg [`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD-1:0] cfgs_ff_regb_ddrc_ch0_visible_window_limit_rd;
   reg [`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR-1:0] cfgs_ff_regb_ddrc_ch0_page_hit_limit_wr;
   reg [`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD-1:0] cfgs_ff_regb_ddrc_ch0_page_hit_limit_rd;
   reg cfgs_ff_regb_ddrc_ch0_opt_hit_gt_hpr;
   reg [`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH-1:0] cfgs_ff_regb_ddrc_ch0_wrcam_lowthresh;
   reg [`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH-1:0] cfgs_ff_regb_ddrc_ch0_wrcam_highthresh;
   reg [`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH-1:0] cfgs_ff_regb_ddrc_ch0_wr_pghit_num_thresh;
   reg [`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH-1:0] cfgs_ff_regb_ddrc_ch0_rd_pghit_num_thresh;
   reg [`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP-1:0] cfgs_ff_regb_ddrc_ch0_rd_act_idle_gap;
   reg [`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP-1:0] cfgs_ff_regb_ddrc_ch0_wr_act_idle_gap;
   reg [`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES-1:0] cfgs_ff_regb_ddrc_ch0_rd_page_exp_cycles;
   reg [`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES-1:0] cfgs_ff_regb_ddrc_ch0_wr_page_exp_cycles;
   reg [`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH-1:0] cfgs_ff_regb_ddrc_ch0_wrecc_cam_lowthresh;
   reg [`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH-1:0] cfgs_ff_regb_ddrc_ch0_wrecc_cam_highthresh;
   reg cfgs_ff_regb_ddrc_ch0_dis_opt_loaded_wrecc_cam_fill_level;
   reg cfgs_ff_regb_ddrc_ch0_dis_opt_valid_wrecc_cam_fill_level;
   reg [`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN-1:0] ff_regb_ddrc_ch0_hwffc_en;
   reg ff_regb_ddrc_ch0_init_fsp;
   reg ff_regb_ddrc_ch0_init_vrcg;
   reg ff_regb_ddrc_ch0_target_vrcg;
   reg ff_regb_ddrc_ch0_skip_mrw_odtvref;
   reg ff_regb_ddrc_ch0_skip_zq_stop_start;
   reg [`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL-1:0] ff_regb_ddrc_ch0_zq_interval;
   reg ff_regb_ddrc_ch0_hwffc_mode;
   reg ff_regb_ddrc_ch0_dfi_lp_en_pd;
   reg ff_regb_ddrc_ch0_dfi_lp_en_sr;
   reg ff_regb_ddrc_ch0_dfi_lp_en_dsm;
   reg ff_regb_ddrc_ch0_dfi_lp_en_data;
   reg ff_regb_ddrc_ch0_dfi_lp_data_req_en;
   reg [`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA-1:0] ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data;
   reg ff_regb_ddrc_ch0_dfi_phyupd_en;
   reg ff_regb_ddrc_ch0_ctrlupd_pre_srx;
   reg ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx;
   reg ff_regb_ddrc_ch0_dis_auto_ctrlupd;
   reg ff_regb_ddrc_ch0_dfi_init_complete_en;
   reg ff_regb_ddrc_ch0_phy_dbi_mode;
   reg ff_regb_ddrc_ch0_dfi_data_cs_polarity;
   reg ff_regb_ddrc_ch0_dfi_reset_n;
   reg ff_regb_ddrc_ch0_dfi_init_start;
   reg ff_regb_ddrc_ch0_lp_optimized_write;
   reg [`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY-1:0] ff_regb_ddrc_ch0_dfi_frequency;
   reg [`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP-1:0] ff_regb_ddrc_ch0_dfi_freq_fsp;
   reg [`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE-1:0] ff_regb_ddrc_ch0_dfi_channel_mode;
   reg ff_regb_ddrc_ch0_dfi_phymstr_en;
   reg [`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32-1:0] ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32;
   reg ff_regb_ddrc_ch0_wr_poison_slverr_en;
   reg ff_regb_ddrc_ch0_wr_poison_intr_en;
   reg ff_regb_ddrc_ch0_wr_poison_intr_clr;
   reg ff_regb_ddrc_ch0_rd_poison_slverr_en;
   reg ff_regb_ddrc_ch0_rd_poison_intr_en;
   reg ff_regb_ddrc_ch0_rd_poison_intr_clr;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE-1:0] ff_regb_ddrc_ch0_ecc_mode;
   reg ff_regb_ddrc_ch0_ecc_ap_en;
   reg ff_regb_ddrc_ch0_ecc_region_remap_en;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP-1:0] ff_regb_ddrc_ch0_ecc_region_map;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32-1:0] ff_regb_ddrc_ch0_blk_channel_idle_time_x32;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD-1:0] ff_regb_ddrc_ch0_ecc_ap_err_threshold;
   reg ff_regb_ddrc_ch0_ecc_region_map_other;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU-1:0] ff_regb_ddrc_ch0_ecc_region_map_granu;
   reg cfgs_ff_regb_ddrc_ch0_data_poison_en;
   reg cfgs_ff_regb_ddrc_ch0_data_poison_bit;
   reg cfgs_ff_regb_ddrc_ch0_ecc_region_parity_lock;
   reg cfgs_ff_regb_ddrc_ch0_ecc_region_waste_lock;
   reg cfgs_ff_regb_ddrc_ch0_med_ecc_en;
   reg cfgs_ff_regb_ddrc_ch0_blk_channel_active_term;
   reg [`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL-1:0] cfgs_ff_regb_ddrc_ch0_active_blk_channel;
   reg ff_regb_ddrc_ch0_ecc_corrected_err_clr;
   reg ff_regb_ddrc_ch0_ecc_uncorrected_err_clr;
   reg ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr;
   reg ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr;
   reg ff_regb_ddrc_ch0_ecc_ap_err_intr_clr;
   reg ff_regb_ddrc_ch0_ecc_corrected_err_intr_en;
   reg ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_en;
   reg ff_regb_ddrc_ch0_ecc_ap_err_intr_en;
   reg ff_regb_ddrc_ch0_ecc_corrected_err_intr_force;
   reg ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force;
   reg ff_regb_ddrc_ch0_ecc_ap_err_intr_force;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_col;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_rank;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_row;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_bank;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_bg;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_data_31_0;
   reg [`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64-1:0] cfgs_ff_regb_ddrc_ch0_ecc_poison_data_71_64;
   reg ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_en;
   reg ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr;
   reg ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr;
   reg ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force;
   reg ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_en;
   reg ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr;
   reg ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr;
   reg ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force;
   reg ff_regb_ddrc_ch0_linkecc_poison_inject_en;
   reg ff_regb_ddrc_ch0_linkecc_poison_type;
   reg ff_regb_ddrc_ch0_linkecc_poison_rw;
   reg [`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL-1:0] ff_regb_ddrc_ch0_linkecc_poison_dmi_sel;
   reg [`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL-1:0] ff_regb_ddrc_ch0_linkecc_poison_byte_sel;
   reg [`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL-1:0] ff_regb_ddrc_ch0_rd_link_ecc_err_byte_sel;
   reg [`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL-1:0] ff_regb_ddrc_ch0_rd_link_ecc_err_rank_sel;
   reg cfgs_ff_regb_ddrc_ch0_dis_wc;
   reg cfgs_ff_regb_ddrc_ch0_dis_max_rank_rd_opt;
   reg cfgs_ff_regb_ddrc_ch0_dis_max_rank_wr_opt;
   reg ff_regb_ddrc_ch0_dis_dq;
   reg ff_regb_ddrc_ch0_dis_hif;
   reg ff_regb_ddrc_ch0_zq_calib_short_todo;
   reg ff_regb_ddrc_ch0_zq_calib_short;
   reg ff_regb_ddrc_ch0_ctrlupd_todo;
   reg ff_regb_ddrc_ch0_ctrlupd;
   reg ff_regb_ddrc_ch0_ctrlupd_burst;
   reg ff_regb_ddrc_ch0_rank0_refresh_todo;
   reg ff_regb_ddrc_ch0_rank0_refresh;
   reg ff_regb_ddrc_ch0_rank1_refresh_todo;
   reg ff_regb_ddrc_ch0_rank1_refresh;
   reg cfgs_ff_regb_ddrc_ch0_sw_done;
   reg [`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD-1:0] cfgs_ff_regb_ddrc_ch0_max_rank_rd;
   reg [`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR-1:0] cfgs_ff_regb_ddrc_ch0_max_rank_wr;
   reg ff_regb_ddrc_ch0_dm_en;
   reg ff_regb_ddrc_ch0_wr_dbi_en;
   reg ff_regb_ddrc_ch0_rd_dbi_en;
   reg [`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT-1:0] ff_regb_ddrc_ch0_rank0_wr_odt;
   reg [`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT-1:0] ff_regb_ddrc_ch0_rank0_rd_odt;
   reg [`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT-1:0] ff_regb_ddrc_ch0_rank1_wr_odt;
   reg [`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT-1:0] ff_regb_ddrc_ch0_rank1_rd_odt;
   reg ff_regb_ddrc_ch0_rd_data_copy_en;
   reg ff_regb_ddrc_ch0_wr_data_copy_en;
   reg ff_regb_ddrc_ch0_wr_data_x_en;
   reg cfgs_ff_regb_ddrc_ch0_sw_static_unlock;
   reg ff_regb_ddrc_ch0_force_clk_te_en;
   reg ff_regb_ddrc_ch0_force_clk_arb_en;
   reg [`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024-1:0] ff_regb_ddrc_ch0_pre_cke_x1024;
   reg [`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024-1:0] ff_regb_ddrc_ch0_post_cke_x1024;
   reg [`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT-1:0] ff_regb_ddrc_ch0_skip_dram_init;
   reg [`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM-1:0] ff_regb_ddrc_ch0_ppt2_burst_num;
   reg [`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0-1:0] ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi0;
   reg [`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1-1:0] ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi1;
   reg ff_regb_ddrc_ch0_ppt2_burst_todo;
   reg ff_regb_ddrc_ch0_ppt2_burst;
   reg ff_regb_ddrc_ch0_ppt2_wait_ref;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0-1:0] cfgs_ff_regb_addr_map0_addrmap_cs_bit0;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0-1:0] cfgs_ff_regb_addr_map0_addrmap_bank_b0;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1-1:0] cfgs_ff_regb_addr_map0_addrmap_bank_b1;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2-1:0] cfgs_ff_regb_addr_map0_addrmap_bank_b2;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0-1:0] cfgs_ff_regb_addr_map0_addrmap_bg_b0;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1-1:0] cfgs_ff_regb_addr_map0_addrmap_bg_b1;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b7;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b8;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b9;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b10;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b3;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b4;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b5;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6-1:0] cfgs_ff_regb_addr_map0_addrmap_col_b6;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b14;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b15;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b16;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b17;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b10;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b11;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b12;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b13;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b6;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b7;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b8;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b9;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b2;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b3;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b4;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b5;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b0;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1-1:0] cfgs_ff_regb_addr_map0_addrmap_row_b1;
   reg [`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY-1:0] ff_regb_addr_map0_nonbinary_device_density;
   reg ff_regb_addr_map0_bank_hash_en;
   reg cfgs_ff_regb_arb_port0_go2critical_en;
   reg cfgs_ff_regb_arb_port0_pagematch_limit;
   reg [`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY-1:0] cfgs_ff_regb_arb_port0_rd_port_priority;
   reg cfgs_ff_regb_arb_port0_rd_port_aging_en;
   reg cfgs_ff_regb_arb_port0_rd_port_urgent_en;
   reg cfgs_ff_regb_arb_port0_rd_port_pagematch_en;
   reg [`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD-1:0] cfgs_ff_regb_arb_port0_rrb_lock_threshold;
   reg [`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY-1:0] cfgs_ff_regb_arb_port0_wr_port_priority;
   reg cfgs_ff_regb_arb_port0_wr_port_aging_en;
   reg cfgs_ff_regb_arb_port0_wr_port_urgent_en;
   reg cfgs_ff_regb_arb_port0_wr_port_pagematch_en;
   reg ff_regb_arb_port0_port_en;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1-1:0] cfgs_ff_regb_arb_port0_rqos_map_level1;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2-1:0] cfgs_ff_regb_arb_port0_rqos_map_level2;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0-1:0] cfgs_ff_regb_arb_port0_rqos_map_region0;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1-1:0] cfgs_ff_regb_arb_port0_rqos_map_region1;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2-1:0] cfgs_ff_regb_arb_port0_rqos_map_region2;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB-1:0] cfgs_ff_regb_arb_port0_rqos_map_timeoutb;
   reg [`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR-1:0] cfgs_ff_regb_arb_port0_rqos_map_timeoutr;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1-1:0] cfgs_ff_regb_arb_port0_wqos_map_level1;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2-1:0] cfgs_ff_regb_arb_port0_wqos_map_level2;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0-1:0] cfgs_ff_regb_arb_port0_wqos_map_region0;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1-1:0] cfgs_ff_regb_arb_port0_wqos_map_region1;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2-1:0] cfgs_ff_regb_arb_port0_wqos_map_region2;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1-1:0] cfgs_ff_regb_arb_port0_wqos_map_timeout1;
   reg [`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2-1:0] cfgs_ff_regb_arb_port0_wqos_map_timeout2;
   reg ff_regb_arb_port0_scrub_en;
   reg ff_regb_arb_port0_scrub_during_lowpower;
   reg [`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM-1:0] ff_regb_arb_port0_scrub_burst_length_nm;
   reg [`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL-1:0] ff_regb_arb_port0_scrub_interval;
   reg [`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE-1:0] ff_regb_arb_port0_scrub_cmd_type;
   reg [`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP-1:0] ff_regb_arb_port0_scrub_burst_length_lp;
   reg [`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0-1:0] ff_regb_arb_port0_scrub_pattern0;
   reg [`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0-1:0] ff_regb_arb_port0_sbr_address_start_mask_0;
   reg [`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1-1:0] ff_regb_arb_port0_sbr_address_start_mask_1;
   reg [`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0-1:0] ff_regb_arb_port0_sbr_address_range_mask_0;
   reg [`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1-1:0] ff_regb_arb_port0_sbr_address_range_mask_1;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN-1:0] cfgs_ff_regb_freq0_ch0_t_ras_min;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX-1:0] cfgs_ff_regb_freq0_ch0_t_ras_max;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW-1:0] cfgs_ff_regb_freq0_ch0_t_faw;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE-1:0] cfgs_ff_regb_freq0_ch0_wr2pre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC-1:0] cfgs_ff_regb_freq0_ch0_t_rc;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE-1:0] cfgs_ff_regb_freq0_ch0_rd2pre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP-1:0] cfgs_ff_regb_freq0_ch0_t_xp;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE-1:0] cfgs_ff_regb_freq0_ch0_t_rcd_write;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD-1:0] cfgs_ff_regb_freq0_ch0_wr2rd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR-1:0] cfgs_ff_regb_freq0_ch0_rd2wr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY-1:0] cfgs_ff_regb_freq0_ch0_read_latency;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY-1:0] cfgs_ff_regb_freq0_ch0_write_latency;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR-1:0] cfgs_ff_regb_freq0_ch0_wr2mr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR-1:0] cfgs_ff_regb_freq0_ch0_rd2mr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR-1:0] cfgs_ff_regb_freq0_ch0_t_mr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP-1:0] cfgs_ff_regb_freq0_ch0_t_rp;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD-1:0] cfgs_ff_regb_freq0_ch0_t_rrd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD-1:0] cfgs_ff_regb_freq0_ch0_t_ccd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD-1:0] cfgs_ff_regb_freq0_ch0_t_rcd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE-1:0] ff_regb_freq0_ch0_t_cke;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR-1:0] ff_regb_freq0_ch0_t_ckesr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE-1:0] ff_regb_freq0_ch0_t_cksre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX-1:0] ff_regb_freq0_ch0_t_cksrx;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX-1:0] cfgs_ff_regb_freq0_ch0_t_ckcsx;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH-1:0] ff_regb_freq0_ch0_t_csh;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S-1:0] cfgs_ff_regb_freq0_ch0_wr2rd_s;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S-1:0] cfgs_ff_regb_freq0_ch0_t_rrd_s;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S-1:0] cfgs_ff_regb_freq0_ch0_t_ccd_s;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE-1:0] cfgs_ff_regb_freq0_ch0_t_cmdcke;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD-1:0] cfgs_ff_regb_freq0_ch0_t_ppd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW-1:0] cfgs_ff_regb_freq0_ch0_t_ccd_mw;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF-1:0] cfgs_ff_regb_freq0_ch0_odtloff;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR-1:0] cfgs_ff_regb_freq0_ch0_t_xsr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO-1:0] cfgs_ff_regb_freq0_ch0_t_osco;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE-1:0] cfgs_ff_regb_freq0_ch0_t_vrcg_disable;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE-1:0] cfgs_ff_regb_freq0_ch0_t_vrcg_enable;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN-1:0] ff_regb_freq0_ch0_t_pdn;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024-1:0] ff_regb_freq0_ch0_t_xsr_dsm_x1024;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC-1:0] cfgs_ff_regb_freq0_ch0_max_wr_sync;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC-1:0] cfgs_ff_regb_freq0_ch0_max_rd_sync;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S-1:0] cfgs_ff_regb_freq0_ch0_rd2wr_s;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG-1:0] cfgs_ff_regb_freq0_ch0_bank_org;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE-1:0] cfgs_ff_regb_freq0_ch0_rda2pre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE-1:0] cfgs_ff_regb_freq0_ch0_wra2pre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE-1:0] cfgs_ff_regb_freq0_ch0_lpddr4_diff_bank_rwa2pre;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD-1:0] ff_regb_freq0_ch0_mrr2rd;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR-1:0] ff_regb_freq0_ch0_mrr2wr;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW-1:0] ff_regb_freq0_ch0_mrr2mrw;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS-1:0] ff_regb_freq0_ch0_ws_fs2wck_sus;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS-1:0] ff_regb_freq0_ch0_t_wcksus;
   reg [`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS-1:0] ff_regb_freq0_ch0_ws_off2ws_fs;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR0_EMR-1:0] cfgs_ff_regb_freq0_ch0_emr;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR0_MR-1:0] cfgs_ff_regb_freq0_ch0_mr;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3-1:0] ff_regb_freq0_ch0_emr3;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2-1:0] ff_regb_freq0_ch0_emr2;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR2_MR5-1:0] cfgs_ff_regb_freq0_ch0_mr5;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR2_MR4-1:0] cfgs_ff_regb_freq0_ch0_mr4;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR3_MR6-1:0] cfgs_ff_regb_freq0_ch0_mr6;
   reg [`REGB_FREQ0_CH0_SIZE_INITMR3_MR22-1:0] cfgs_ff_regb_freq0_ch0_mr22;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT-1:0] ff_regb_freq0_ch0_dfi_tphy_wrlat;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA-1:0] ff_regb_freq0_ch0_dfi_tphy_wrdata;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN-1:0] ff_regb_freq0_ch0_dfi_t_rddata_en;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY-1:0] ff_regb_freq0_ch0_dfi_t_ctrl_delay;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE-1:0] ff_regb_freq0_ch0_dfi_t_dram_clk_enable;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE-1:0] ff_regb_freq0_ch0_dfi_t_dram_clk_disable;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY-1:0] ff_regb_freq0_ch0_dfi_t_wrdata_delay;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT-1:0] cfgs_ff_regb_freq0_ch0_dfi_tphy_wrcslat;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT-1:0] cfgs_ff_regb_freq0_ch0_dfi_tphy_rdcslat;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_delay;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_dis;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_en_fs;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_en_wr;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_en_rd;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_cs;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_toggle;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_fast_toggle;
   reg [`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD-1:0] cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd;
   reg cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd_en;
   reg [`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD-1:0] ff_regb_freq0_ch0_dfi_lp_wakeup_pd;
   reg [`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR-1:0] ff_regb_freq0_ch0_dfi_lp_wakeup_sr;
   reg [`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM-1:0] ff_regb_freq0_ch0_dfi_lp_wakeup_dsm;
   reg [`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA-1:0] ff_regb_freq0_ch0_dfi_lp_wakeup_data;
   reg [`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP-1:0] ff_regb_freq0_ch0_dfi_tlp_resp;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN-1:0] ff_regb_freq0_ch0_dfi_t_ctrlup_min;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX-1:0] ff_regb_freq0_ch0_dfi_t_ctrlup_max;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024-1:0] cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_max_x1024;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024-1:0] cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_min_x1024;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1-1:0] ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1;
   reg ff_regb_freq0_ch0_ctrlupd_after_dqsosc;
   reg ff_regb_freq0_ch0_ppt2_override;
   reg ff_regb_freq0_ch0_ppt2_en;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT-1:0] ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1_unit;
   reg [`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8-1:0] cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_burst_interval_x8;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32-1:0] ff_regb_freq0_ch0_t_refi_x1_x32;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32-1:0] ff_regb_freq0_ch0_refresh_to_x1_x32;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN-1:0] ff_regb_freq0_ch0_refresh_margin;
   reg ff_regb_freq0_ch0_refresh_to_x1_sel;
   reg ff_regb_freq0_ch0_t_refi_x1_sel;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN-1:0] ff_regb_freq0_ch0_t_rfc_min;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB-1:0] ff_regb_freq0_ch0_t_rfc_min_ab;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR-1:0] ff_regb_freq0_ch0_t_pbr2pbr;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT-1:0] ff_regb_freq0_ch0_t_pbr2act;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32-1:0] ff_regb_freq0_ch0_refresh_to_ab_x32;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32-1:0] ff_regb_freq0_ch0_refresh_timer0_start_value_x32;
   reg [`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32-1:0] ff_regb_freq0_ch0_refresh_timer1_start_value_x32;
   reg [`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB-1:0] ff_regb_freq0_ch0_t_rfmpb;
   reg [`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP-1:0] ff_regb_freq0_ch0_t_zq_long_nop;
   reg [`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP-1:0] ff_regb_freq0_ch0_t_zq_short_nop;
   reg [`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024-1:0] cfgs_ff_regb_freq0_ch0_t_zq_short_interval_x1024;
   reg [`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP-1:0] cfgs_ff_regb_freq0_ch0_t_zq_reset_nop;
   reg [`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP-1:0] ff_regb_freq0_ch0_t_zq_stop;
   reg ff_regb_freq0_ch0_dqsosc_enable;
   reg ff_regb_freq0_ch0_dqsosc_interval_unit;
   reg [`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL-1:0] ff_regb_freq0_ch0_dqsosc_interval;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL-1:0] cfgs_ff_regb_freq0_ch0_mr4_read_interval;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD-1:0] ff_regb_freq0_ch0_derated_t_rrd;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP-1:0] ff_regb_freq0_ch0_derated_t_rp;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN-1:0] ff_regb_freq0_ch0_derated_t_ras_min;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD-1:0] ff_regb_freq0_ch0_derated_t_rcd;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC-1:0] ff_regb_freq0_ch0_derated_t_rc;
   reg [`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE-1:0] ff_regb_freq0_ch0_derated_t_rcd_write;
   reg [`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32-1:0] cfgs_ff_regb_freq0_ch0_hw_lp_idle_x32;
   reg cfgs_ff_regb_freq0_ch0_dvfsq_enable;
   reg [`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER-1:0] cfgs_ff_regb_freq0_ch0_pageclose_timer;
   reg [`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP-1:0] cfgs_ff_regb_freq0_ch0_rdwr_idle_gap;
   reg [`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE-1:0] cfgs_ff_regb_freq0_ch0_hpr_max_starve;
   reg [`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq0_ch0_hpr_xact_run_length;
   reg [`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE-1:0] cfgs_ff_regb_freq0_ch0_lpr_max_starve;
   reg [`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq0_ch0_lpr_xact_run_length;
   reg [`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE-1:0] cfgs_ff_regb_freq0_ch0_w_max_starve;
   reg [`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq0_ch0_w_xact_run_length;
   reg ff_regb_freq0_ch0_frequency_ratio;
   reg [`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP-1:0] cfgs_ff_regb_freq0_ch0_diff_rank_rd_gap;
   reg [`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP-1:0] cfgs_ff_regb_freq0_ch0_diff_rank_wr_gap;
   reg [`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR-1:0] cfgs_ff_regb_freq0_ch0_wr2rd_dr;
   reg [`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR-1:0] cfgs_ff_regb_freq0_ch0_rd2wr_dr;
   reg [`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32-1:0] cfgs_ff_regb_freq0_ch0_powerdown_to_x32;
   reg [`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32-1:0] cfgs_ff_regb_freq0_ch0_selfref_to_x32;
   reg [`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024-1:0] cfgs_ff_regb_freq0_ch0_t_pgm_x1_x1024;
   reg cfgs_ff_regb_freq0_ch0_t_pgm_x1_sel;
   reg [`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32-1:0] cfgs_ff_regb_freq0_ch0_t_pgmpst_x32;
   reg [`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT-1:0] cfgs_ff_regb_freq0_ch0_t_pgm_exit;
   reg ff_regb_freq0_ch0_wr_link_ecc_enable;
   reg ff_regb_freq0_ch0_rd_link_ecc_enable;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN-1:0] cfgs_ff_regb_freq1_ch0_t_ras_min;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX-1:0] cfgs_ff_regb_freq1_ch0_t_ras_max;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW-1:0] cfgs_ff_regb_freq1_ch0_t_faw;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE-1:0] cfgs_ff_regb_freq1_ch0_wr2pre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC-1:0] cfgs_ff_regb_freq1_ch0_t_rc;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE-1:0] cfgs_ff_regb_freq1_ch0_rd2pre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP-1:0] cfgs_ff_regb_freq1_ch0_t_xp;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE-1:0] cfgs_ff_regb_freq1_ch0_t_rcd_write;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD-1:0] cfgs_ff_regb_freq1_ch0_wr2rd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR-1:0] cfgs_ff_regb_freq1_ch0_rd2wr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY-1:0] cfgs_ff_regb_freq1_ch0_read_latency;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY-1:0] cfgs_ff_regb_freq1_ch0_write_latency;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR-1:0] cfgs_ff_regb_freq1_ch0_wr2mr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR-1:0] cfgs_ff_regb_freq1_ch0_rd2mr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR-1:0] cfgs_ff_regb_freq1_ch0_t_mr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP-1:0] cfgs_ff_regb_freq1_ch0_t_rp;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD-1:0] cfgs_ff_regb_freq1_ch0_t_rrd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD-1:0] cfgs_ff_regb_freq1_ch0_t_ccd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD-1:0] cfgs_ff_regb_freq1_ch0_t_rcd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE-1:0] ff_regb_freq1_ch0_t_cke;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR-1:0] ff_regb_freq1_ch0_t_ckesr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE-1:0] ff_regb_freq1_ch0_t_cksre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX-1:0] ff_regb_freq1_ch0_t_cksrx;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX-1:0] cfgs_ff_regb_freq1_ch0_t_ckcsx;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH-1:0] ff_regb_freq1_ch0_t_csh;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S-1:0] cfgs_ff_regb_freq1_ch0_wr2rd_s;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S-1:0] cfgs_ff_regb_freq1_ch0_t_rrd_s;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S-1:0] cfgs_ff_regb_freq1_ch0_t_ccd_s;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE-1:0] cfgs_ff_regb_freq1_ch0_t_cmdcke;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD-1:0] cfgs_ff_regb_freq1_ch0_t_ppd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW-1:0] cfgs_ff_regb_freq1_ch0_t_ccd_mw;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF-1:0] cfgs_ff_regb_freq1_ch0_odtloff;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR-1:0] cfgs_ff_regb_freq1_ch0_t_xsr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO-1:0] cfgs_ff_regb_freq1_ch0_t_osco;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE-1:0] cfgs_ff_regb_freq1_ch0_t_vrcg_disable;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE-1:0] cfgs_ff_regb_freq1_ch0_t_vrcg_enable;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN-1:0] ff_regb_freq1_ch0_t_pdn;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024-1:0] ff_regb_freq1_ch0_t_xsr_dsm_x1024;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC-1:0] cfgs_ff_regb_freq1_ch0_max_wr_sync;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC-1:0] cfgs_ff_regb_freq1_ch0_max_rd_sync;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S-1:0] cfgs_ff_regb_freq1_ch0_rd2wr_s;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG-1:0] cfgs_ff_regb_freq1_ch0_bank_org;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE-1:0] cfgs_ff_regb_freq1_ch0_rda2pre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE-1:0] cfgs_ff_regb_freq1_ch0_wra2pre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE-1:0] cfgs_ff_regb_freq1_ch0_lpddr4_diff_bank_rwa2pre;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD-1:0] ff_regb_freq1_ch0_mrr2rd;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR-1:0] ff_regb_freq1_ch0_mrr2wr;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW-1:0] ff_regb_freq1_ch0_mrr2mrw;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS-1:0] ff_regb_freq1_ch0_ws_fs2wck_sus;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS-1:0] ff_regb_freq1_ch0_t_wcksus;
   reg [`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS-1:0] ff_regb_freq1_ch0_ws_off2ws_fs;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR0_EMR-1:0] cfgs_ff_regb_freq1_ch0_emr;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR0_MR-1:0] cfgs_ff_regb_freq1_ch0_mr;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3-1:0] ff_regb_freq1_ch0_emr3;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2-1:0] ff_regb_freq1_ch0_emr2;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR2_MR5-1:0] cfgs_ff_regb_freq1_ch0_mr5;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR2_MR4-1:0] cfgs_ff_regb_freq1_ch0_mr4;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR3_MR6-1:0] cfgs_ff_regb_freq1_ch0_mr6;
   reg [`REGB_FREQ1_CH0_SIZE_INITMR3_MR22-1:0] cfgs_ff_regb_freq1_ch0_mr22;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT-1:0] ff_regb_freq1_ch0_dfi_tphy_wrlat;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA-1:0] ff_regb_freq1_ch0_dfi_tphy_wrdata;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN-1:0] ff_regb_freq1_ch0_dfi_t_rddata_en;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY-1:0] ff_regb_freq1_ch0_dfi_t_ctrl_delay;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE-1:0] ff_regb_freq1_ch0_dfi_t_dram_clk_enable;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE-1:0] ff_regb_freq1_ch0_dfi_t_dram_clk_disable;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY-1:0] ff_regb_freq1_ch0_dfi_t_wrdata_delay;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT-1:0] cfgs_ff_regb_freq1_ch0_dfi_tphy_wrcslat;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT-1:0] cfgs_ff_regb_freq1_ch0_dfi_tphy_rdcslat;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_delay;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_dis;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_en_fs;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_en_wr;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_en_rd;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_cs;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_toggle;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_fast_toggle;
   reg [`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD-1:0] cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd;
   reg cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd_en;
   reg [`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024-1:0] cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_max_x1024;
   reg [`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024-1:0] cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_min_x1024;
   reg [`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1-1:0] ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1;
   reg ff_regb_freq1_ch0_ctrlupd_after_dqsosc;
   reg ff_regb_freq1_ch0_ppt2_override;
   reg ff_regb_freq1_ch0_ppt2_en;
   reg [`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT-1:0] ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1_unit;
   reg [`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8-1:0] cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_burst_interval_x8;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32-1:0] ff_regb_freq1_ch0_t_refi_x1_x32;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32-1:0] ff_regb_freq1_ch0_refresh_to_x1_x32;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN-1:0] ff_regb_freq1_ch0_refresh_margin;
   reg ff_regb_freq1_ch0_refresh_to_x1_sel;
   reg ff_regb_freq1_ch0_t_refi_x1_sel;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN-1:0] ff_regb_freq1_ch0_t_rfc_min;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB-1:0] ff_regb_freq1_ch0_t_rfc_min_ab;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR-1:0] ff_regb_freq1_ch0_t_pbr2pbr;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT-1:0] ff_regb_freq1_ch0_t_pbr2act;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32-1:0] ff_regb_freq1_ch0_refresh_to_ab_x32;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32-1:0] ff_regb_freq1_ch0_refresh_timer0_start_value_x32;
   reg [`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32-1:0] ff_regb_freq1_ch0_refresh_timer1_start_value_x32;
   reg [`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB-1:0] ff_regb_freq1_ch0_t_rfmpb;
   reg [`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP-1:0] ff_regb_freq1_ch0_t_zq_long_nop;
   reg [`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP-1:0] ff_regb_freq1_ch0_t_zq_short_nop;
   reg [`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024-1:0] cfgs_ff_regb_freq1_ch0_t_zq_short_interval_x1024;
   reg [`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP-1:0] cfgs_ff_regb_freq1_ch0_t_zq_reset_nop;
   reg [`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP-1:0] ff_regb_freq1_ch0_t_zq_stop;
   reg ff_regb_freq1_ch0_dqsosc_enable;
   reg ff_regb_freq1_ch0_dqsosc_interval_unit;
   reg [`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL-1:0] ff_regb_freq1_ch0_dqsosc_interval;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL-1:0] cfgs_ff_regb_freq1_ch0_mr4_read_interval;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD-1:0] ff_regb_freq1_ch0_derated_t_rrd;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP-1:0] ff_regb_freq1_ch0_derated_t_rp;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN-1:0] ff_regb_freq1_ch0_derated_t_ras_min;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD-1:0] ff_regb_freq1_ch0_derated_t_rcd;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC-1:0] ff_regb_freq1_ch0_derated_t_rc;
   reg [`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE-1:0] ff_regb_freq1_ch0_derated_t_rcd_write;
   reg [`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32-1:0] cfgs_ff_regb_freq1_ch0_hw_lp_idle_x32;
   reg cfgs_ff_regb_freq1_ch0_dvfsq_enable;
   reg [`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER-1:0] cfgs_ff_regb_freq1_ch0_pageclose_timer;
   reg [`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP-1:0] cfgs_ff_regb_freq1_ch0_rdwr_idle_gap;
   reg [`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE-1:0] cfgs_ff_regb_freq1_ch0_hpr_max_starve;
   reg [`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq1_ch0_hpr_xact_run_length;
   reg [`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE-1:0] cfgs_ff_regb_freq1_ch0_lpr_max_starve;
   reg [`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq1_ch0_lpr_xact_run_length;
   reg [`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE-1:0] cfgs_ff_regb_freq1_ch0_w_max_starve;
   reg [`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq1_ch0_w_xact_run_length;
   reg ff_regb_freq1_ch0_frequency_ratio;
   reg [`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP-1:0] cfgs_ff_regb_freq1_ch0_diff_rank_rd_gap;
   reg [`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP-1:0] cfgs_ff_regb_freq1_ch0_diff_rank_wr_gap;
   reg [`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR-1:0] cfgs_ff_regb_freq1_ch0_wr2rd_dr;
   reg [`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR-1:0] cfgs_ff_regb_freq1_ch0_rd2wr_dr;
   reg [`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32-1:0] cfgs_ff_regb_freq1_ch0_powerdown_to_x32;
   reg [`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32-1:0] cfgs_ff_regb_freq1_ch0_selfref_to_x32;
   reg [`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024-1:0] cfgs_ff_regb_freq1_ch0_t_pgm_x1_x1024;
   reg cfgs_ff_regb_freq1_ch0_t_pgm_x1_sel;
   reg [`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32-1:0] cfgs_ff_regb_freq1_ch0_t_pgmpst_x32;
   reg [`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT-1:0] cfgs_ff_regb_freq1_ch0_t_pgm_exit;
   reg ff_regb_freq1_ch0_wr_link_ecc_enable;
   reg ff_regb_freq1_ch0_rd_link_ecc_enable;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN-1:0] cfgs_ff_regb_freq2_ch0_t_ras_min;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX-1:0] cfgs_ff_regb_freq2_ch0_t_ras_max;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW-1:0] cfgs_ff_regb_freq2_ch0_t_faw;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE-1:0] cfgs_ff_regb_freq2_ch0_wr2pre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC-1:0] cfgs_ff_regb_freq2_ch0_t_rc;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE-1:0] cfgs_ff_regb_freq2_ch0_rd2pre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP-1:0] cfgs_ff_regb_freq2_ch0_t_xp;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE-1:0] cfgs_ff_regb_freq2_ch0_t_rcd_write;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD-1:0] cfgs_ff_regb_freq2_ch0_wr2rd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR-1:0] cfgs_ff_regb_freq2_ch0_rd2wr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY-1:0] cfgs_ff_regb_freq2_ch0_read_latency;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY-1:0] cfgs_ff_regb_freq2_ch0_write_latency;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR-1:0] cfgs_ff_regb_freq2_ch0_wr2mr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR-1:0] cfgs_ff_regb_freq2_ch0_rd2mr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR-1:0] cfgs_ff_regb_freq2_ch0_t_mr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP-1:0] cfgs_ff_regb_freq2_ch0_t_rp;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD-1:0] cfgs_ff_regb_freq2_ch0_t_rrd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD-1:0] cfgs_ff_regb_freq2_ch0_t_ccd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD-1:0] cfgs_ff_regb_freq2_ch0_t_rcd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE-1:0] ff_regb_freq2_ch0_t_cke;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR-1:0] ff_regb_freq2_ch0_t_ckesr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE-1:0] ff_regb_freq2_ch0_t_cksre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX-1:0] ff_regb_freq2_ch0_t_cksrx;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX-1:0] cfgs_ff_regb_freq2_ch0_t_ckcsx;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH-1:0] ff_regb_freq2_ch0_t_csh;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S-1:0] cfgs_ff_regb_freq2_ch0_wr2rd_s;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S-1:0] cfgs_ff_regb_freq2_ch0_t_rrd_s;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S-1:0] cfgs_ff_regb_freq2_ch0_t_ccd_s;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE-1:0] cfgs_ff_regb_freq2_ch0_t_cmdcke;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD-1:0] cfgs_ff_regb_freq2_ch0_t_ppd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW-1:0] cfgs_ff_regb_freq2_ch0_t_ccd_mw;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF-1:0] cfgs_ff_regb_freq2_ch0_odtloff;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR-1:0] cfgs_ff_regb_freq2_ch0_t_xsr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO-1:0] cfgs_ff_regb_freq2_ch0_t_osco;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE-1:0] cfgs_ff_regb_freq2_ch0_t_vrcg_disable;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE-1:0] cfgs_ff_regb_freq2_ch0_t_vrcg_enable;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN-1:0] ff_regb_freq2_ch0_t_pdn;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024-1:0] ff_regb_freq2_ch0_t_xsr_dsm_x1024;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC-1:0] cfgs_ff_regb_freq2_ch0_max_wr_sync;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC-1:0] cfgs_ff_regb_freq2_ch0_max_rd_sync;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S-1:0] cfgs_ff_regb_freq2_ch0_rd2wr_s;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG-1:0] cfgs_ff_regb_freq2_ch0_bank_org;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE-1:0] cfgs_ff_regb_freq2_ch0_rda2pre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE-1:0] cfgs_ff_regb_freq2_ch0_wra2pre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE-1:0] cfgs_ff_regb_freq2_ch0_lpddr4_diff_bank_rwa2pre;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD-1:0] ff_regb_freq2_ch0_mrr2rd;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR-1:0] ff_regb_freq2_ch0_mrr2wr;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW-1:0] ff_regb_freq2_ch0_mrr2mrw;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS-1:0] ff_regb_freq2_ch0_ws_fs2wck_sus;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS-1:0] ff_regb_freq2_ch0_t_wcksus;
   reg [`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS-1:0] ff_regb_freq2_ch0_ws_off2ws_fs;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR0_EMR-1:0] cfgs_ff_regb_freq2_ch0_emr;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR0_MR-1:0] cfgs_ff_regb_freq2_ch0_mr;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3-1:0] ff_regb_freq2_ch0_emr3;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2-1:0] ff_regb_freq2_ch0_emr2;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR2_MR5-1:0] cfgs_ff_regb_freq2_ch0_mr5;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR2_MR4-1:0] cfgs_ff_regb_freq2_ch0_mr4;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR3_MR6-1:0] cfgs_ff_regb_freq2_ch0_mr6;
   reg [`REGB_FREQ2_CH0_SIZE_INITMR3_MR22-1:0] cfgs_ff_regb_freq2_ch0_mr22;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT-1:0] ff_regb_freq2_ch0_dfi_tphy_wrlat;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA-1:0] ff_regb_freq2_ch0_dfi_tphy_wrdata;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN-1:0] ff_regb_freq2_ch0_dfi_t_rddata_en;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY-1:0] ff_regb_freq2_ch0_dfi_t_ctrl_delay;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE-1:0] ff_regb_freq2_ch0_dfi_t_dram_clk_enable;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE-1:0] ff_regb_freq2_ch0_dfi_t_dram_clk_disable;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY-1:0] ff_regb_freq2_ch0_dfi_t_wrdata_delay;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT-1:0] cfgs_ff_regb_freq2_ch0_dfi_tphy_wrcslat;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT-1:0] cfgs_ff_regb_freq2_ch0_dfi_tphy_rdcslat;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_delay;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_dis;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_en_fs;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_en_wr;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_en_rd;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_cs;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_toggle;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_fast_toggle;
   reg [`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD-1:0] cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd;
   reg cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd_en;
   reg [`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024-1:0] cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_max_x1024;
   reg [`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024-1:0] cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_min_x1024;
   reg [`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1-1:0] ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1;
   reg ff_regb_freq2_ch0_ctrlupd_after_dqsosc;
   reg ff_regb_freq2_ch0_ppt2_override;
   reg ff_regb_freq2_ch0_ppt2_en;
   reg [`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT-1:0] ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1_unit;
   reg [`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8-1:0] cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_burst_interval_x8;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32-1:0] ff_regb_freq2_ch0_t_refi_x1_x32;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32-1:0] ff_regb_freq2_ch0_refresh_to_x1_x32;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN-1:0] ff_regb_freq2_ch0_refresh_margin;
   reg ff_regb_freq2_ch0_refresh_to_x1_sel;
   reg ff_regb_freq2_ch0_t_refi_x1_sel;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN-1:0] ff_regb_freq2_ch0_t_rfc_min;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB-1:0] ff_regb_freq2_ch0_t_rfc_min_ab;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR-1:0] ff_regb_freq2_ch0_t_pbr2pbr;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT-1:0] ff_regb_freq2_ch0_t_pbr2act;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32-1:0] ff_regb_freq2_ch0_refresh_to_ab_x32;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32-1:0] ff_regb_freq2_ch0_refresh_timer0_start_value_x32;
   reg [`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32-1:0] ff_regb_freq2_ch0_refresh_timer1_start_value_x32;
   reg [`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB-1:0] ff_regb_freq2_ch0_t_rfmpb;
   reg [`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP-1:0] ff_regb_freq2_ch0_t_zq_long_nop;
   reg [`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP-1:0] ff_regb_freq2_ch0_t_zq_short_nop;
   reg [`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024-1:0] cfgs_ff_regb_freq2_ch0_t_zq_short_interval_x1024;
   reg [`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP-1:0] cfgs_ff_regb_freq2_ch0_t_zq_reset_nop;
   reg [`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP-1:0] ff_regb_freq2_ch0_t_zq_stop;
   reg ff_regb_freq2_ch0_dqsosc_enable;
   reg ff_regb_freq2_ch0_dqsosc_interval_unit;
   reg [`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL-1:0] ff_regb_freq2_ch0_dqsosc_interval;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL-1:0] cfgs_ff_regb_freq2_ch0_mr4_read_interval;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD-1:0] ff_regb_freq2_ch0_derated_t_rrd;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP-1:0] ff_regb_freq2_ch0_derated_t_rp;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN-1:0] ff_regb_freq2_ch0_derated_t_ras_min;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD-1:0] ff_regb_freq2_ch0_derated_t_rcd;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC-1:0] ff_regb_freq2_ch0_derated_t_rc;
   reg [`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE-1:0] ff_regb_freq2_ch0_derated_t_rcd_write;
   reg [`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32-1:0] cfgs_ff_regb_freq2_ch0_hw_lp_idle_x32;
   reg cfgs_ff_regb_freq2_ch0_dvfsq_enable;
   reg [`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER-1:0] cfgs_ff_regb_freq2_ch0_pageclose_timer;
   reg [`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP-1:0] cfgs_ff_regb_freq2_ch0_rdwr_idle_gap;
   reg [`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE-1:0] cfgs_ff_regb_freq2_ch0_hpr_max_starve;
   reg [`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq2_ch0_hpr_xact_run_length;
   reg [`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE-1:0] cfgs_ff_regb_freq2_ch0_lpr_max_starve;
   reg [`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq2_ch0_lpr_xact_run_length;
   reg [`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE-1:0] cfgs_ff_regb_freq2_ch0_w_max_starve;
   reg [`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq2_ch0_w_xact_run_length;
   reg ff_regb_freq2_ch0_frequency_ratio;
   reg [`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP-1:0] cfgs_ff_regb_freq2_ch0_diff_rank_rd_gap;
   reg [`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP-1:0] cfgs_ff_regb_freq2_ch0_diff_rank_wr_gap;
   reg [`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR-1:0] cfgs_ff_regb_freq2_ch0_wr2rd_dr;
   reg [`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR-1:0] cfgs_ff_regb_freq2_ch0_rd2wr_dr;
   reg [`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32-1:0] cfgs_ff_regb_freq2_ch0_powerdown_to_x32;
   reg [`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32-1:0] cfgs_ff_regb_freq2_ch0_selfref_to_x32;
   reg [`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024-1:0] cfgs_ff_regb_freq2_ch0_t_pgm_x1_x1024;
   reg cfgs_ff_regb_freq2_ch0_t_pgm_x1_sel;
   reg [`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32-1:0] cfgs_ff_regb_freq2_ch0_t_pgmpst_x32;
   reg [`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT-1:0] cfgs_ff_regb_freq2_ch0_t_pgm_exit;
   reg ff_regb_freq2_ch0_wr_link_ecc_enable;
   reg ff_regb_freq2_ch0_rd_link_ecc_enable;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN-1:0] cfgs_ff_regb_freq3_ch0_t_ras_min;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX-1:0] cfgs_ff_regb_freq3_ch0_t_ras_max;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW-1:0] cfgs_ff_regb_freq3_ch0_t_faw;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE-1:0] cfgs_ff_regb_freq3_ch0_wr2pre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC-1:0] cfgs_ff_regb_freq3_ch0_t_rc;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE-1:0] cfgs_ff_regb_freq3_ch0_rd2pre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP-1:0] cfgs_ff_regb_freq3_ch0_t_xp;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE-1:0] cfgs_ff_regb_freq3_ch0_t_rcd_write;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD-1:0] cfgs_ff_regb_freq3_ch0_wr2rd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR-1:0] cfgs_ff_regb_freq3_ch0_rd2wr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY-1:0] cfgs_ff_regb_freq3_ch0_read_latency;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY-1:0] cfgs_ff_regb_freq3_ch0_write_latency;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR-1:0] cfgs_ff_regb_freq3_ch0_wr2mr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR-1:0] cfgs_ff_regb_freq3_ch0_rd2mr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR-1:0] cfgs_ff_regb_freq3_ch0_t_mr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP-1:0] cfgs_ff_regb_freq3_ch0_t_rp;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD-1:0] cfgs_ff_regb_freq3_ch0_t_rrd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD-1:0] cfgs_ff_regb_freq3_ch0_t_ccd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD-1:0] cfgs_ff_regb_freq3_ch0_t_rcd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE-1:0] ff_regb_freq3_ch0_t_cke;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR-1:0] ff_regb_freq3_ch0_t_ckesr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE-1:0] ff_regb_freq3_ch0_t_cksre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX-1:0] ff_regb_freq3_ch0_t_cksrx;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX-1:0] cfgs_ff_regb_freq3_ch0_t_ckcsx;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH-1:0] ff_regb_freq3_ch0_t_csh;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S-1:0] cfgs_ff_regb_freq3_ch0_wr2rd_s;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S-1:0] cfgs_ff_regb_freq3_ch0_t_rrd_s;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S-1:0] cfgs_ff_regb_freq3_ch0_t_ccd_s;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE-1:0] cfgs_ff_regb_freq3_ch0_t_cmdcke;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD-1:0] cfgs_ff_regb_freq3_ch0_t_ppd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW-1:0] cfgs_ff_regb_freq3_ch0_t_ccd_mw;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF-1:0] cfgs_ff_regb_freq3_ch0_odtloff;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR-1:0] cfgs_ff_regb_freq3_ch0_t_xsr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO-1:0] cfgs_ff_regb_freq3_ch0_t_osco;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE-1:0] cfgs_ff_regb_freq3_ch0_t_vrcg_disable;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE-1:0] cfgs_ff_regb_freq3_ch0_t_vrcg_enable;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN-1:0] ff_regb_freq3_ch0_t_pdn;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024-1:0] ff_regb_freq3_ch0_t_xsr_dsm_x1024;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC-1:0] cfgs_ff_regb_freq3_ch0_max_wr_sync;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC-1:0] cfgs_ff_regb_freq3_ch0_max_rd_sync;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S-1:0] cfgs_ff_regb_freq3_ch0_rd2wr_s;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG-1:0] cfgs_ff_regb_freq3_ch0_bank_org;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE-1:0] cfgs_ff_regb_freq3_ch0_rda2pre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE-1:0] cfgs_ff_regb_freq3_ch0_wra2pre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE-1:0] cfgs_ff_regb_freq3_ch0_lpddr4_diff_bank_rwa2pre;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD-1:0] ff_regb_freq3_ch0_mrr2rd;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR-1:0] ff_regb_freq3_ch0_mrr2wr;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW-1:0] ff_regb_freq3_ch0_mrr2mrw;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS-1:0] ff_regb_freq3_ch0_ws_fs2wck_sus;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS-1:0] ff_regb_freq3_ch0_t_wcksus;
   reg [`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS-1:0] ff_regb_freq3_ch0_ws_off2ws_fs;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR0_EMR-1:0] cfgs_ff_regb_freq3_ch0_emr;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR0_MR-1:0] cfgs_ff_regb_freq3_ch0_mr;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3-1:0] ff_regb_freq3_ch0_emr3;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2-1:0] ff_regb_freq3_ch0_emr2;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR2_MR5-1:0] cfgs_ff_regb_freq3_ch0_mr5;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR2_MR4-1:0] cfgs_ff_regb_freq3_ch0_mr4;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR3_MR6-1:0] cfgs_ff_regb_freq3_ch0_mr6;
   reg [`REGB_FREQ3_CH0_SIZE_INITMR3_MR22-1:0] cfgs_ff_regb_freq3_ch0_mr22;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT-1:0] ff_regb_freq3_ch0_dfi_tphy_wrlat;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA-1:0] ff_regb_freq3_ch0_dfi_tphy_wrdata;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN-1:0] ff_regb_freq3_ch0_dfi_t_rddata_en;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY-1:0] ff_regb_freq3_ch0_dfi_t_ctrl_delay;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE-1:0] ff_regb_freq3_ch0_dfi_t_dram_clk_enable;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE-1:0] ff_regb_freq3_ch0_dfi_t_dram_clk_disable;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY-1:0] ff_regb_freq3_ch0_dfi_t_wrdata_delay;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT-1:0] cfgs_ff_regb_freq3_ch0_dfi_tphy_wrcslat;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT-1:0] cfgs_ff_regb_freq3_ch0_dfi_tphy_rdcslat;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_delay;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_dis;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_en_fs;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_en_wr;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_en_rd;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_cs;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_toggle;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_fast_toggle;
   reg [`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD-1:0] cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd;
   reg cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd_en;
   reg [`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024-1:0] cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_max_x1024;
   reg [`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024-1:0] cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_min_x1024;
   reg [`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1-1:0] ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1;
   reg ff_regb_freq3_ch0_ctrlupd_after_dqsosc;
   reg ff_regb_freq3_ch0_ppt2_override;
   reg ff_regb_freq3_ch0_ppt2_en;
   reg [`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT-1:0] ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1_unit;
   reg [`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8-1:0] cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_burst_interval_x8;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32-1:0] ff_regb_freq3_ch0_t_refi_x1_x32;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32-1:0] ff_regb_freq3_ch0_refresh_to_x1_x32;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN-1:0] ff_regb_freq3_ch0_refresh_margin;
   reg ff_regb_freq3_ch0_refresh_to_x1_sel;
   reg ff_regb_freq3_ch0_t_refi_x1_sel;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN-1:0] ff_regb_freq3_ch0_t_rfc_min;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB-1:0] ff_regb_freq3_ch0_t_rfc_min_ab;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR-1:0] ff_regb_freq3_ch0_t_pbr2pbr;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT-1:0] ff_regb_freq3_ch0_t_pbr2act;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32-1:0] ff_regb_freq3_ch0_refresh_to_ab_x32;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32-1:0] ff_regb_freq3_ch0_refresh_timer0_start_value_x32;
   reg [`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32-1:0] ff_regb_freq3_ch0_refresh_timer1_start_value_x32;
   reg [`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB-1:0] ff_regb_freq3_ch0_t_rfmpb;
   reg [`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP-1:0] ff_regb_freq3_ch0_t_zq_long_nop;
   reg [`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP-1:0] ff_regb_freq3_ch0_t_zq_short_nop;
   reg [`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024-1:0] cfgs_ff_regb_freq3_ch0_t_zq_short_interval_x1024;
   reg [`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP-1:0] cfgs_ff_regb_freq3_ch0_t_zq_reset_nop;
   reg [`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP-1:0] ff_regb_freq3_ch0_t_zq_stop;
   reg ff_regb_freq3_ch0_dqsosc_enable;
   reg ff_regb_freq3_ch0_dqsosc_interval_unit;
   reg [`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL-1:0] ff_regb_freq3_ch0_dqsosc_interval;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL-1:0] cfgs_ff_regb_freq3_ch0_mr4_read_interval;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD-1:0] ff_regb_freq3_ch0_derated_t_rrd;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP-1:0] ff_regb_freq3_ch0_derated_t_rp;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN-1:0] ff_regb_freq3_ch0_derated_t_ras_min;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD-1:0] ff_regb_freq3_ch0_derated_t_rcd;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC-1:0] ff_regb_freq3_ch0_derated_t_rc;
   reg [`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE-1:0] ff_regb_freq3_ch0_derated_t_rcd_write;
   reg [`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32-1:0] cfgs_ff_regb_freq3_ch0_hw_lp_idle_x32;
   reg cfgs_ff_regb_freq3_ch0_dvfsq_enable;
   reg [`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER-1:0] cfgs_ff_regb_freq3_ch0_pageclose_timer;
   reg [`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP-1:0] cfgs_ff_regb_freq3_ch0_rdwr_idle_gap;
   reg [`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE-1:0] cfgs_ff_regb_freq3_ch0_hpr_max_starve;
   reg [`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq3_ch0_hpr_xact_run_length;
   reg [`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE-1:0] cfgs_ff_regb_freq3_ch0_lpr_max_starve;
   reg [`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq3_ch0_lpr_xact_run_length;
   reg [`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE-1:0] cfgs_ff_regb_freq3_ch0_w_max_starve;
   reg [`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH-1:0] cfgs_ff_regb_freq3_ch0_w_xact_run_length;
   reg ff_regb_freq3_ch0_frequency_ratio;
   reg [`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP-1:0] cfgs_ff_regb_freq3_ch0_diff_rank_rd_gap;
   reg [`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP-1:0] cfgs_ff_regb_freq3_ch0_diff_rank_wr_gap;
   reg [`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR-1:0] cfgs_ff_regb_freq3_ch0_wr2rd_dr;
   reg [`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR-1:0] cfgs_ff_regb_freq3_ch0_rd2wr_dr;
   reg [`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32-1:0] cfgs_ff_regb_freq3_ch0_powerdown_to_x32;
   reg [`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32-1:0] cfgs_ff_regb_freq3_ch0_selfref_to_x32;
   reg [`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024-1:0] cfgs_ff_regb_freq3_ch0_t_pgm_x1_x1024;
   reg cfgs_ff_regb_freq3_ch0_t_pgm_x1_sel;
   reg [`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32-1:0] cfgs_ff_regb_freq3_ch0_t_pgmpst_x32;
   reg [`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT-1:0] cfgs_ff_regb_freq3_ch0_t_pgm_exit;
   reg ff_regb_freq3_ch0_wr_link_ecc_enable;
   reg ff_regb_freq3_ch0_rd_link_ecc_enable;



   //------------------------
   // Register REGB_DDRC_CH0.MSTR0
   //------------------------
   always_comb begin : r0_mstr0_combo_PROC
      r0_mstr0 = {REG_WIDTH {1'b0}};
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4] = ff_regb_ddrc_ch0_lpddr4;
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5] = ff_regb_ddrc_ch0_lpddr5;
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X] = ff_regb_ddrc_ch0_lpddr5x;
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH+:`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH] = ff_regb_ddrc_ch0_data_bus_width[(`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH) -1:0];
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR+:`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR] = ff_regb_ddrc_ch0_burst_rdwr[(`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR) -1:0];
      r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS+:`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS] = ff_regb_ddrc_ch0_active_ranks[(`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.MSTR2
   //------------------------
   always_comb begin : r2_mstr2_combo_PROC
      r2_mstr2 = {REG_WIDTH {1'b0}};
      r2_mstr2[`REGB_DDRC_CH0_OFFSET_MSTR2_TARGET_FREQUENCY+:`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY] = ff_regb_ddrc_ch0_target_frequency[(`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.MSTR4
   //------------------------
   always_comb begin : r4_mstr4_combo_PROC
      r4_mstr4 = {REG_WIDTH {1'b0}};
      r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_ON+:`REGB_DDRC_CH0_SIZE_MSTR4_WCK_ON] = ff_regb_ddrc_ch0_wck_on;
      r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_SUSPEND_EN+:`REGB_DDRC_CH0_SIZE_MSTR4_WCK_SUSPEND_EN] = ff_regb_ddrc_ch0_wck_suspend_en;
      r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WS_OFF_EN+:`REGB_DDRC_CH0_SIZE_MSTR4_WS_OFF_EN] = ff_regb_ddrc_ch0_ws_off_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL0
   //------------------------
   always_comb begin : r8_mrctrl0_combo_PROC
      r8_mrctrl0 = {REG_WIDTH {1'b0}};
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_TYPE+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_TYPE] = ff_regb_ddrc_ch0_mr_type;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_SW_INIT_INT+:`REGB_DDRC_CH0_SIZE_MRCTRL0_SW_INIT_INT] = ff_regb_ddrc_ch0_sw_init_int;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_RANK+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK] = ff_regb_ddrc_ch0_mr_rank[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK) -1:0];
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_ADDR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR] = ff_regb_ddrc_ch0_mr_addr[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR) -1:0];
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MRR_DONE_CLR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MRR_DONE_CLR] = ff_regb_ddrc_ch0_mrr_done_clr;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_DIS_MRRW_TRFC+:`REGB_DDRC_CH0_SIZE_MRCTRL0_DIS_MRRW_TRFC] = ff_regb_ddrc_ch0_dis_mrrw_trfc;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_EN+:`REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_EN] = ff_regb_ddrc_ch0_ppr_en;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_PGMPST_EN+:`REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_PGMPST_EN] = ff_regb_ddrc_ch0_ppr_pgmpst_en;
      r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_WR] = ff_regb_ddrc_ch0_mr_wr;
   end
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL1
   //------------------------
   always_comb begin : r9_mrctrl1_combo_PROC
      r9_mrctrl1 = {REG_WIDTH {1'b0}};
      r9_mrctrl1[`REGB_DDRC_CH0_OFFSET_MRCTRL1_MR_DATA+:`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA] = ff_regb_ddrc_ch0_mr_data[(`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL0
   //------------------------
   always_comb begin : r14_deratectl0_combo_PROC
      r14_deratectl0 = {REG_WIDTH {1'b0}};
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_ENABLE+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_ENABLE] = ff_regb_ddrc_ch0_derate_enable;
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_LPDDR4_REFRESH_MODE+:`REGB_DDRC_CH0_SIZE_DERATECTL0_LPDDR4_REFRESH_MODE] = ff_regb_ddrc_ch0_lpddr4_refresh_mode;
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_MR4_PAUSE_FC+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_MR4_PAUSE_FC] = ff_regb_ddrc_ch0_derate_mr4_pause_fc;
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X6X8+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X6X8] = ff_regb_ddrc_ch0_dis_trefi_x6x8;
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X0125+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X0125] = ff_regb_ddrc_ch0_dis_trefi_x0125;
      r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP+:`REGB_DDRC_CH0_SIZE_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP] = ff_regb_ddrc_ch0_use_slow_rm_in_low_temp;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL1
   //------------------------
   always_comb begin : r15_deratectl1_combo_PROC
      r15_deratectl1 = {REG_WIDTH {1'b0}};
      r15_deratectl1[`REGB_DDRC_CH0_OFFSET_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0+:`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0] = ff_regb_ddrc_ch0_active_derate_byte_rank0[(`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL2
   //------------------------
   always_comb begin : r16_deratectl2_combo_PROC
      r16_deratectl2 = {REG_WIDTH {1'b0}};
      r16_deratectl2[`REGB_DDRC_CH0_OFFSET_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1+:`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1] = ff_regb_ddrc_ch0_active_derate_byte_rank1[(`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL5
   //------------------------
   always_comb begin : r19_deratectl5_combo_PROC
      r19_deratectl5 = {REG_WIDTH {1'b0}};
      r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN] = cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_en;
      r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR] = cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr;
      r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE] = cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL6
   //------------------------
   always_comb begin : r20_deratectl6_combo_PROC
      r20_deratectl6 = {REG_WIDTH {1'b0}};
      r20_deratectl6[`REGB_DDRC_CH0_OFFSET_DERATECTL6_DERATE_MR4_TUF_DIS+:`REGB_DDRC_CH0_SIZE_DERATECTL6_DERATE_MR4_TUF_DIS] = ff_regb_ddrc_ch0_derate_mr4_tuf_dis;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGCTL
   //------------------------
   always_comb begin : r24_deratedbgctl_combo_PROC
      r24_deratedbgctl = {REG_WIDTH {1'b0}};
      r24_deratedbgctl[`REGB_DDRC_CH0_OFFSET_DERATEDBGCTL_DBG_MR4_RANK_SEL+:`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL] = ff_regb_ddrc_ch0_dbg_mr4_rank_sel[(`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.PWRCTL
   //------------------------
   always_comb begin : r26_pwrctl_combo_PROC
      r26_pwrctl = {REG_WIDTH {1'b0}};
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN] = ff_regb_ddrc_ch0_selfref_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN) -1:0];
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_POWERDOWN_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN] = ff_regb_ddrc_ch0_powerdown_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN) -1:0];
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_EN_DFI_DRAM_CLK_DISABLE+:`REGB_DDRC_CH0_SIZE_PWRCTL_EN_DFI_DRAM_CLK_DISABLE] = ff_regb_ddrc_ch0_en_dfi_dram_clk_disable;
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_SW+:`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_SW] = ff_regb_ddrc_ch0_selfref_sw;
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_STAY_IN_SELFREF+:`REGB_DDRC_CH0_SIZE_PWRCTL_STAY_IN_SELFREF] = ff_regb_ddrc_ch0_stay_in_selfref;
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_DIS_CAM_DRAIN_SELFREF+:`REGB_DDRC_CH0_SIZE_PWRCTL_DIS_CAM_DRAIN_SELFREF] = ff_regb_ddrc_ch0_dis_cam_drain_selfref;
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_LPDDR4_SR_ALLOWED+:`REGB_DDRC_CH0_SIZE_PWRCTL_LPDDR4_SR_ALLOWED] = ff_regb_ddrc_ch0_lpddr4_sr_allowed;
      r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_DSM_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_DSM_EN] = ff_regb_ddrc_ch0_dsm_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.HWLPCTL
   //------------------------
   always_comb begin : r27_hwlpctl_combo_PROC
      r27_hwlpctl = {REG_WIDTH {1'b0}};
      r27_hwlpctl[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EN+:`REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EN] = ff_regb_ddrc_ch0_hw_lp_en;
      r27_hwlpctl[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EXIT_IDLE_EN+:`REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EXIT_IDLE_EN] = ff_regb_ddrc_ch0_hw_lp_exit_idle_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.CLKGATECTL
   //------------------------
   always_comb begin : r29_clkgatectl_combo_PROC
      r29_clkgatectl = {REG_WIDTH {1'b0}};
      r29_clkgatectl[`REGB_DDRC_CH0_OFFSET_CLKGATECTL_BSM_CLK_ON+:`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON] = ff_regb_ddrc_ch0_bsm_clk_on[(`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.RFSHMOD0
   //------------------------
   always_comb begin : r30_rfshmod0_combo_PROC
      r30_rfshmod0 = {REG_WIDTH {1'b0}};
      r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_REFRESH_BURST+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST] = ff_regb_ddrc_ch0_refresh_burst[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST) -1:0];
      r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_AUTO_REFAB_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN] = ff_regb_ddrc_ch0_auto_refab_en[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN) -1:0];
      r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH] = ff_regb_ddrc_ch0_per_bank_refresh;
      r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH_OPT_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH_OPT_EN] = ff_regb_ddrc_ch0_per_bank_refresh_opt_en;
      r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN] = ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.RFSHCTL0
   //------------------------
   always_comb begin : r32_rfshctl0_combo_PROC
      r32_rfshctl0 = {REG_WIDTH {1'b0}};
      r32_rfshctl0[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_DIS_AUTO_REFRESH+:`REGB_DDRC_CH0_SIZE_RFSHCTL0_DIS_AUTO_REFRESH] = ff_regb_ddrc_ch0_dis_auto_refresh;
      r32_rfshctl0[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_REFRESH_UPDATE_LEVEL+:`REGB_DDRC_CH0_SIZE_RFSHCTL0_REFRESH_UPDATE_LEVEL] = ff_regb_ddrc_ch0_refresh_update_level;
   end
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD0
   //------------------------
   always_comb begin : r33_rfmmod0_combo_PROC
      r33_rfmmod0 = {REG_WIDTH {1'b0}};
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFM_EN+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFM_EN] = ff_regb_ddrc_ch0_rfm_en;
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMSBC+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMSBC] = ff_regb_ddrc_ch0_rfmsbc;
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAIMT+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT] = ff_regb_ddrc_ch0_raaimt[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT) -1:0];
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAMULT+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT] = ff_regb_ddrc_ch0_raamult[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT) -1:0];
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAADEC+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC] = ff_regb_ddrc_ch0_raadec[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC) -1:0];
      r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMTH_RM_THR+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR] = ff_regb_ddrc_ch0_rfmth_rm_thr[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD1
   //------------------------
   always_comb begin : r34_rfmmod1_combo_PROC
      r34_rfmmod1 = {REG_WIDTH {1'b0}};
      r34_rfmmod1[`REGB_DDRC_CH0_OFFSET_RFMMOD1_INIT_RAA_CNT+:`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT] = ff_regb_ddrc_ch0_init_raa_cnt[(`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.RFMCTL
   //------------------------
   always_comb begin : r35_rfmctl_combo_PROC
      r35_rfmctl = {REG_WIDTH {1'b0}};
      r35_rfmctl[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_RANK+:`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK] = ff_regb_ddrc_ch0_dbg_raa_rank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK) -1:0];
      r35_rfmctl[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_BG_BANK+:`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK] = ff_regb_ddrc_ch0_dbg_raa_bg_bank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL0
   //------------------------
   always_comb begin : r37_zqctl0_combo_PROC
      r37_zqctl0 = {REG_WIDTH {1'b0}};
      r37_zqctl0[`REGB_DDRC_CH0_OFFSET_ZQCTL0_ZQ_RESISTOR_SHARED+:`REGB_DDRC_CH0_SIZE_ZQCTL0_ZQ_RESISTOR_SHARED] = ff_regb_ddrc_ch0_zq_resistor_shared;
      r37_zqctl0[`REGB_DDRC_CH0_OFFSET_ZQCTL0_DIS_AUTO_ZQ+:`REGB_DDRC_CH0_SIZE_ZQCTL0_DIS_AUTO_ZQ] = ff_regb_ddrc_ch0_dis_auto_zq;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL1
   //------------------------
   always_comb begin : r38_zqctl1_combo_PROC
      r38_zqctl1 = {REG_WIDTH {1'b0}};
      r38_zqctl1[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET+:`REGB_DDRC_CH0_SIZE_ZQCTL1_ZQ_RESET] = ff_regb_ddrc_ch0_zq_reset;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL2
   //------------------------
   always_comb begin : r39_zqctl2_combo_PROC
      r39_zqctl2 = {REG_WIDTH {1'b0}};
      r39_zqctl2[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL+:`REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL] = cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl;
      r39_zqctl2[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL_HWFFC+:`REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL_HWFFC] = cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl_hwffc;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCRUNTIME
   //------------------------
   always_comb begin : r41_dqsoscruntime_combo_PROC
      r41_dqsoscruntime = {REG_WIDTH {1'b0}};
      r41_dqsoscruntime[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_DQSOSC_RUNTIME+:`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME] = cfgs_ff_regb_ddrc_ch0_dqsosc_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME) -1:0];
      r41_dqsoscruntime[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_WCK2DQO_RUNTIME+:`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME] = cfgs_ff_regb_ddrc_ch0_wck2dqo_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCCFG0
   //------------------------
   always_comb begin : r43_dqsosccfg0_combo_PROC
      r43_dqsosccfg0 = {REG_WIDTH {1'b0}};
      r43_dqsosccfg0[`REGB_DDRC_CH0_OFFSET_DQSOSCCFG0_DIS_DQSOSC_SRX+:`REGB_DDRC_CH0_SIZE_DQSOSCCFG0_DIS_DQSOSC_SRX] = cfgs_ff_regb_ddrc_ch0_dis_dqsosc_srx;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED0
   //------------------------
   always_comb begin : r45_sched0_combo_PROC
      r45_sched0 = {REG_WIDTH {1'b0}};
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH] = cfgs_ff_regb_ddrc_ch0_dis_opt_wrecc_collision_flush;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_WRITE+:`REGB_DDRC_CH0_SIZE_SCHED0_PREFER_WRITE] = cfgs_ff_regb_ddrc_ch0_prefer_write;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PAGECLOSE+:`REGB_DDRC_CH0_SIZE_SCHED0_PAGECLOSE] = cfgs_ff_regb_ddrc_ch0_pageclose;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_WRCAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_WRCAM_FILL_LEVEL] = cfgs_ff_regb_ddrc_ch0_opt_wrcam_fill_level;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_ACT+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_ACT] = cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_act;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_PRE+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_PRE] = cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_pre;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_AUTOPRE_RMW+:`REGB_DDRC_CH0_SIZE_SCHED0_AUTOPRE_RMW] = cfgs_ff_regb_ddrc_ch0_autopre_rmw;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPR_NUM_ENTRIES+:`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES] = cfgs_ff_regb_ddrc_ch0_lpr_num_entries[(`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES) -1:0];
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR4_OPT_ACT_TIMING+:`REGB_DDRC_CH0_SIZE_SCHED0_LPDDR4_OPT_ACT_TIMING] = cfgs_ff_regb_ddrc_ch0_lpddr4_opt_act_timing;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR5_OPT_ACT_TIMING+:`REGB_DDRC_CH0_SIZE_SCHED0_LPDDR5_OPT_ACT_TIMING] = cfgs_ff_regb_ddrc_ch0_lpddr5_opt_act_timing;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_W_STARVE_FREE_RUNNING+:`REGB_DDRC_CH0_SIZE_SCHED0_W_STARVE_FREE_RUNNING] = cfgs_ff_regb_ddrc_ch0_w_starve_free_running;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_ACT_LAT+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_ACT_LAT] = cfgs_ff_regb_ddrc_ch0_opt_act_lat;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_READ+:`REGB_DDRC_CH0_SIZE_SCHED0_PREFER_READ] = cfgs_ff_regb_ddrc_ch0_prefer_read;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_SPECULATIVE_ACT+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_SPECULATIVE_ACT] = cfgs_ff_regb_ddrc_ch0_dis_speculative_act;
      r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_VPRW_SCH+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_VPRW_SCH] = cfgs_ff_regb_ddrc_ch0_opt_vprw_sch;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED1
   //------------------------
   always_comb begin : r46_sched1_combo_PROC
      r46_sched1 = {REG_WIDTH {1'b0}};
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_DELAY_SWITCH_WRITE+:`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE] = cfgs_ff_regb_ddrc_ch0_delay_switch_write[(`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE) -1:0];
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_WR+:`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR] = cfgs_ff_regb_ddrc_ch0_visible_window_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR) -1:0];
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_RD+:`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD] = cfgs_ff_regb_ddrc_ch0_visible_window_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD) -1:0];
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_WR+:`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR] = cfgs_ff_regb_ddrc_ch0_page_hit_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR) -1:0];
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_RD+:`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD] = cfgs_ff_regb_ddrc_ch0_page_hit_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD) -1:0];
      r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_OPT_HIT_GT_HPR+:`REGB_DDRC_CH0_SIZE_SCHED1_OPT_HIT_GT_HPR] = cfgs_ff_regb_ddrc_ch0_opt_hit_gt_hpr;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED3
   //------------------------
   always_comb begin : r48_sched3_combo_PROC
      r48_sched3 = {REG_WIDTH {1'b0}};
      r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_LOWTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH] = cfgs_ff_regb_ddrc_ch0_wrcam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH) -1:0];
      r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_HIGHTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH] = cfgs_ff_regb_ddrc_ch0_wrcam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH) -1:0];
      r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WR_PGHIT_NUM_THRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH] = cfgs_ff_regb_ddrc_ch0_wr_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH) -1:0];
      r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_RD_PGHIT_NUM_THRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH] = cfgs_ff_regb_ddrc_ch0_rd_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED4
   //------------------------
   always_comb begin : r49_sched4_combo_PROC
      r49_sched4 = {REG_WIDTH {1'b0}};
      r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_ACT_IDLE_GAP+:`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP] = cfgs_ff_regb_ddrc_ch0_rd_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP) -1:0];
      r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_ACT_IDLE_GAP+:`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP] = cfgs_ff_regb_ddrc_ch0_wr_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP) -1:0];
      r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_PAGE_EXP_CYCLES+:`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES] = cfgs_ff_regb_ddrc_ch0_rd_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES) -1:0];
      r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_PAGE_EXP_CYCLES+:`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES] = cfgs_ff_regb_ddrc_ch0_wr_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED5
   //------------------------
   always_comb begin : r50_sched5_combo_PROC
      r50_sched5 = {REG_WIDTH {1'b0}};
      r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_LOWTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH] = cfgs_ff_regb_ddrc_ch0_wrecc_cam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH) -1:0];
      r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_HIGHTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH] = cfgs_ff_regb_ddrc_ch0_wrecc_cam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH) -1:0];
      r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL] = cfgs_ff_regb_ddrc_ch0_dis_opt_loaded_wrecc_cam_fill_level;
      r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL] = cfgs_ff_regb_ddrc_ch0_dis_opt_valid_wrecc_cam_fill_level;
   end
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCCTL
   //------------------------
   always_comb begin : r51_hwffcctl_combo_PROC
      r51_hwffcctl = {REG_WIDTH {1'b0}};
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_EN+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN] = ff_regb_ddrc_ch0_hwffc_en[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN) -1:0];
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_FSP+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_FSP] = ff_regb_ddrc_ch0_init_fsp;
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_VRCG+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_VRCG] = ff_regb_ddrc_ch0_init_vrcg;
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_TARGET_VRCG+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_TARGET_VRCG] = ff_regb_ddrc_ch0_target_vrcg;
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_MRW_ODTVREF+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_MRW_ODTVREF] = ff_regb_ddrc_ch0_skip_mrw_odtvref;
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_ZQ_STOP_START+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_ZQ_STOP_START] = ff_regb_ddrc_ch0_skip_zq_stop_start;
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_ZQ_INTERVAL+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL] = ff_regb_ddrc_ch0_zq_interval[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL) -1:0];
      r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_MODE+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_MODE] = ff_regb_ddrc_ch0_hwffc_mode;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFILPCFG0
   //------------------------
   always_comb begin : r62_dfilpcfg0_combo_PROC
      r62_dfilpcfg0 = {REG_WIDTH {1'b0}};
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_PD+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_PD] = ff_regb_ddrc_ch0_dfi_lp_en_pd;
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_SR+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_SR] = ff_regb_ddrc_ch0_dfi_lp_en_sr;
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DSM+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DSM] = ff_regb_ddrc_ch0_dfi_lp_en_dsm;
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DATA+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DATA] = ff_regb_ddrc_ch0_dfi_lp_en_data;
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_DATA_REQ_EN+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_DATA_REQ_EN] = ff_regb_ddrc_ch0_dfi_lp_data_req_en;
      r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA] = ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data[(`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFIUPD0
   //------------------------
   always_comb begin : r63_dfiupd0_combo_PROC
      r63_dfiupd0 = {REG_WIDTH {1'b0}};
      r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DFI_PHYUPD_EN+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DFI_PHYUPD_EN] = ff_regb_ddrc_ch0_dfi_phyupd_en;
      r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_CTRLUPD_PRE_SRX+:`REGB_DDRC_CH0_SIZE_DFIUPD0_CTRLUPD_PRE_SRX] = ff_regb_ddrc_ch0_ctrlupd_pre_srx;
      r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD_SRX+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD_SRX] = ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx;
      r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD] = ff_regb_ddrc_ch0_dis_auto_ctrlupd;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFIMISC
   //------------------------
   always_comb begin : r65_dfimisc_combo_PROC
      r65_dfimisc = {REG_WIDTH {1'b0}};
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_COMPLETE_EN+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_COMPLETE_EN] = ff_regb_ddrc_ch0_dfi_init_complete_en;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_PHY_DBI_MODE+:`REGB_DDRC_CH0_SIZE_DFIMISC_PHY_DBI_MODE] = ff_regb_ddrc_ch0_phy_dbi_mode;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_DATA_CS_POLARITY+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_DATA_CS_POLARITY] = ff_regb_ddrc_ch0_dfi_data_cs_polarity;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_RESET_N+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_RESET_N] = ff_regb_ddrc_ch0_dfi_reset_n;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_START+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_START] = ff_regb_ddrc_ch0_dfi_init_start;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_LP_OPTIMIZED_WRITE+:`REGB_DDRC_CH0_SIZE_DFIMISC_LP_OPTIMIZED_WRITE] = ff_regb_ddrc_ch0_lp_optimized_write;
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQUENCY+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY] = ff_regb_ddrc_ch0_dfi_frequency[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY) -1:0];
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQ_FSP+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP] = ff_regb_ddrc_ch0_dfi_freq_fsp[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP) -1:0];
      r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_CHANNEL_MODE+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE] = ff_regb_ddrc_ch0_dfi_channel_mode[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFIPHYMSTR
   //------------------------
   always_comb begin : r67_dfiphymstr_combo_PROC
      r67_dfiphymstr = {REG_WIDTH {1'b0}};
      r67_dfiphymstr[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_EN+:`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_EN] = ff_regb_ddrc_ch0_dfi_phymstr_en;
      r67_dfiphymstr[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32+:`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32] = ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32[(`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.POISONCFG
   //------------------------
   always_comb begin : r77_poisoncfg_combo_PROC
      r77_poisoncfg = {REG_WIDTH {1'b0}};
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_SLVERR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_SLVERR_EN] = ff_regb_ddrc_ch0_wr_poison_slverr_en;
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_EN] = ff_regb_ddrc_ch0_wr_poison_intr_en;
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_CLR+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_CLR] = ff_regb_ddrc_ch0_wr_poison_intr_clr;
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_SLVERR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_SLVERR_EN] = ff_regb_ddrc_ch0_rd_poison_slverr_en;
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_EN] = ff_regb_ddrc_ch0_rd_poison_intr_en;
      r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_CLR+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_CLR] = ff_regb_ddrc_ch0_rd_poison_intr_clr;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG0
   //------------------------
   always_comb begin : r79_ecccfg0_combo_PROC
      r79_ecccfg0 = {REG_WIDTH {1'b0}};
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_MODE+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE] = ff_regb_ddrc_ch0_ecc_mode[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE) -1:0];
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_EN] = ff_regb_ddrc_ch0_ecc_ap_en;
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_REMAP_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_REMAP_EN] = ff_regb_ddrc_ch0_ecc_region_remap_en;
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP] = ff_regb_ddrc_ch0_ecc_region_map[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP) -1:0];
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32+:`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32] = ff_regb_ddrc_ch0_blk_channel_idle_time_x32[(`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32) -1:0];
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_ERR_THRESHOLD+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD] = ff_regb_ddrc_ch0_ecc_ap_err_threshold[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD) -1:0];
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_OTHER+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_OTHER] = ff_regb_ddrc_ch0_ecc_region_map_other;
      r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_GRANU+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU] = ff_regb_ddrc_ch0_ecc_region_map_granu[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG1
   //------------------------
   always_comb begin : r80_ecccfg1_combo_PROC
      r80_ecccfg1 = {REG_WIDTH {1'b0}};
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_EN] = cfgs_ff_regb_ddrc_ch0_data_poison_en;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_BIT+:`REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_BIT] = cfgs_ff_regb_ddrc_ch0_data_poison_bit;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_PARITY_LOCK+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_PARITY_LOCK] = cfgs_ff_regb_ddrc_ch0_ecc_region_parity_lock;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_WASTE_LOCK+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_WASTE_LOCK] = cfgs_ff_regb_ddrc_ch0_ecc_region_waste_lock;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_MED_ECC_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG1_MED_ECC_EN] = cfgs_ff_regb_ddrc_ch0_med_ecc_en;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM+:`REGB_DDRC_CH0_SIZE_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM] = cfgs_ff_regb_ddrc_ch0_blk_channel_active_term;
      r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ACTIVE_BLK_CHANNEL+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL] = cfgs_ff_regb_ddrc_ch0_active_blk_channel[(`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCTL
   //------------------------
   always_comb begin : r82_eccctl_combo_PROC
      r82_eccctl = {REG_WIDTH {1'b0}};
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_CLR] = ff_regb_ddrc_ch0_ecc_corrected_err_clr;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_CLR] = ff_regb_ddrc_ch0_ecc_uncorrected_err_clr;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORR_ERR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORR_ERR_CNT_CLR] = ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORR_ERR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORR_ERR_CNT_CLR] = ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_CLR] = ff_regb_ddrc_ch0_ecc_ap_err_intr_clr;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_EN] = ff_regb_ddrc_ch0_ecc_corrected_err_intr_en;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN] = ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_en;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_EN] = ff_regb_ddrc_ch0_ecc_ap_err_intr_en;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE] = ff_regb_ddrc_ch0_ecc_corrected_err_intr_force;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE] = ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force;
      r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_FORCE] = ff_regb_ddrc_ch0_ecc_ap_err_intr_force;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR0
   //------------------------
   always_comb begin : r97_eccpoisonaddr0_combo_PROC
      r97_eccpoisonaddr0 = {REG_WIDTH {1'b0}};
      r97_eccpoisonaddr0[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_COL+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL] = cfgs_ff_regb_ddrc_ch0_ecc_poison_col[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL) -1:0];
      r97_eccpoisonaddr0[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_RANK+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK] = cfgs_ff_regb_ddrc_ch0_ecc_poison_rank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR1
   //------------------------
   always_comb begin : r98_eccpoisonaddr1_combo_PROC
      r98_eccpoisonaddr1 = {REG_WIDTH {1'b0}};
      r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_ROW+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW] = cfgs_ff_regb_ddrc_ch0_ecc_poison_row[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW) -1:0];
      r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BANK+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK] = cfgs_ff_regb_ddrc_ch0_ecc_poison_bank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK) -1:0];
      r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BG+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG] = cfgs_ff_regb_ddrc_ch0_ecc_poison_bg[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT0
   //------------------------
   always_comb begin : r101_eccpoisonpat0_combo_PROC
      r101_eccpoisonpat0 = {REG_WIDTH {1'b0}};
      r101_eccpoisonpat0[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT0_ECC_POISON_DATA_31_0+:`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0] = cfgs_ff_regb_ddrc_ch0_ecc_poison_data_31_0[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT2
   //------------------------
   always_comb begin : r103_eccpoisonpat2_combo_PROC
      r103_eccpoisonpat2 = {REG_WIDTH {1'b0}};
      r103_eccpoisonpat2[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT2_ECC_POISON_DATA_71_64+:`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64] = cfgs_ff_regb_ddrc_ch0_ecc_poison_data_71_64[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCTL1
   //------------------------
   always_comb begin : r161_lnkeccctl1_combo_PROC
      r161_lnkeccctl1 = {REG_WIDTH {1'b0}};
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN] = ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_en;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR] = ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR] = ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE] = ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN] = ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_en;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR] = ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR] = ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr;
      r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE] = ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force;
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONCTL0
   //------------------------
   always_comb begin : r162_lnkeccpoisonctl0_combo_PROC
      r162_lnkeccpoisonctl0 = {REG_WIDTH {1'b0}};
      r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN] = ff_regb_ddrc_ch0_linkecc_poison_inject_en;
      r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_TYPE+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_TYPE] = ff_regb_ddrc_ch0_linkecc_poison_type;
      r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_RW+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_RW] = ff_regb_ddrc_ch0_linkecc_poison_rw;
      r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL] = ff_regb_ddrc_ch0_linkecc_poison_dmi_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL) -1:0];
      r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL] = ff_regb_ddrc_ch0_linkecc_poison_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCINDEX
   //------------------------
   always_comb begin : r164_lnkeccindex_combo_PROC
      r164_lnkeccindex = {REG_WIDTH {1'b0}};
      r164_lnkeccindex[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL] = ff_regb_ddrc_ch0_rd_link_ecc_err_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL) -1:0];
      r164_lnkeccindex[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL] = ff_regb_ddrc_ch0_rd_link_ecc_err_rank_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL0
   //------------------------
   always_comb begin : r234_opctrl0_combo_PROC
      r234_opctrl0 = {REG_WIDTH {1'b0}};
      r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_WC+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_WC] = cfgs_ff_regb_ddrc_ch0_dis_wc;
      r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_RD_OPT+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_RD_OPT] = cfgs_ff_regb_ddrc_ch0_dis_max_rank_rd_opt;
      r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_WR_OPT+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_WR_OPT] = cfgs_ff_regb_ddrc_ch0_dis_max_rank_wr_opt;
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL1
   //------------------------
   always_comb begin : r235_opctrl1_combo_PROC
      r235_opctrl1 = {REG_WIDTH {1'b0}};
      r235_opctrl1[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_DQ+:`REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_DQ] = ff_regb_ddrc_ch0_dis_dq;
      r235_opctrl1[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_HIF+:`REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_HIF] = ff_regb_ddrc_ch0_dis_hif;
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCMD
   //------------------------
   always_comb begin : r237_opctrlcmd_combo_PROC
      r237_opctrlcmd = {REG_WIDTH {1'b0}};
      r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_ZQ_CALIB_SHORT] = ff_regb_ddrc_ch0_zq_calib_short;
      r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD] = ff_regb_ddrc_ch0_ctrlupd;
      r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD_BURST+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD_BURST] = ff_regb_ddrc_ch0_ctrlupd_burst;
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPREFCTRL0
   //------------------------
   always_comb begin : r240_oprefctrl0_combo_PROC
      r240_oprefctrl0 = {REG_WIDTH {1'b0}};
      r240_oprefctrl0[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH+:`REGB_DDRC_CH0_SIZE_OPREFCTRL0_RANK0_REFRESH] = ff_regb_ddrc_ch0_rank0_refresh;
      r240_oprefctrl0[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH+:`REGB_DDRC_CH0_SIZE_OPREFCTRL0_RANK1_REFRESH] = ff_regb_ddrc_ch0_rank1_refresh;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SWCTL
   //------------------------
   always_comb begin : r249_swctl_combo_PROC
      r249_swctl = {REG_WIDTH {1'b0}};
      r249_swctl[`REGB_DDRC_CH0_OFFSET_SWCTL_SW_DONE+:`REGB_DDRC_CH0_SIZE_SWCTL_SW_DONE] = cfgs_ff_regb_ddrc_ch0_sw_done;
   end
   //------------------------
   // Register REGB_DDRC_CH0.RANKCTL
   //------------------------
   always_comb begin : r253_rankctl_combo_PROC
      r253_rankctl = {REG_WIDTH {1'b0}};
      r253_rankctl[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_RD+:`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD] = cfgs_ff_regb_ddrc_ch0_max_rank_rd[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD) -1:0];
      r253_rankctl[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_WR+:`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR] = cfgs_ff_regb_ddrc_ch0_max_rank_wr[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DBICTL
   //------------------------
   always_comb begin : r254_dbictl_combo_PROC
      r254_dbictl = {REG_WIDTH {1'b0}};
      r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_DM_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_DM_EN] = ff_regb_ddrc_ch0_dm_en;
      r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_WR_DBI_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_WR_DBI_EN] = ff_regb_ddrc_ch0_wr_dbi_en;
      r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_RD_DBI_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_RD_DBI_EN] = ff_regb_ddrc_ch0_rd_dbi_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ODTMAP
   //------------------------
   always_comb begin : r256_odtmap_combo_PROC
      r256_odtmap = {REG_WIDTH {1'b0}};
      r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_WR_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT] = ff_regb_ddrc_ch0_rank0_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT) -1:0];
      r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_RD_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT] = ff_regb_ddrc_ch0_rank0_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT) -1:0];
      r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_WR_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT] = ff_regb_ddrc_ch0_rank1_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT) -1:0];
      r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_RD_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT] = ff_regb_ddrc_ch0_rank1_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DATACTL0
   //------------------------
   always_comb begin : r257_datactl0_combo_PROC
      r257_datactl0 = {REG_WIDTH {1'b0}};
      r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_RD_DATA_COPY_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_RD_DATA_COPY_EN] = ff_regb_ddrc_ch0_rd_data_copy_en;
      r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_COPY_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_COPY_EN] = ff_regb_ddrc_ch0_wr_data_copy_en;
      r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_X_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_X_EN] = ff_regb_ddrc_ch0_wr_data_x_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SWCTLSTATIC
   //------------------------
   always_comb begin : r258_swctlstatic_combo_PROC
      r258_swctlstatic = {REG_WIDTH {1'b0}};
      r258_swctlstatic[`REGB_DDRC_CH0_OFFSET_SWCTLSTATIC_SW_STATIC_UNLOCK+:`REGB_DDRC_CH0_SIZE_SWCTLSTATIC_SW_STATIC_UNLOCK] = cfgs_ff_regb_ddrc_ch0_sw_static_unlock;
   end
   //------------------------
   // Register REGB_DDRC_CH0.CGCTL
   //------------------------
   always_comb begin : r259_cgctl_combo_PROC
      r259_cgctl = {REG_WIDTH {1'b0}};
      r259_cgctl[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_TE_EN+:`REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_TE_EN] = ff_regb_ddrc_ch0_force_clk_te_en;
      r259_cgctl[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_ARB_EN+:`REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_ARB_EN] = ff_regb_ddrc_ch0_force_clk_arb_en;
   end
   //------------------------
   // Register REGB_DDRC_CH0.INITTMG0
   //------------------------
   always_comb begin : r260_inittmg0_combo_PROC
      r260_inittmg0 = {REG_WIDTH {1'b0}};
      r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_PRE_CKE_X1024+:`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024] = ff_regb_ddrc_ch0_pre_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024) -1:0];
      r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_POST_CKE_X1024+:`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024] = ff_regb_ddrc_ch0_post_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024) -1:0];
      r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_SKIP_DRAM_INIT+:`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT] = ff_regb_ddrc_ch0_skip_dram_init[(`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.PPT2CTRL0
   //------------------------
   always_comb begin : r285_ppt2ctrl0_combo_PROC
      r285_ppt2ctrl0 = {REG_WIDTH {1'b0}};
      r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST_NUM+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM] = ff_regb_ddrc_ch0_ppt2_burst_num[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM) -1:0];
      r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0] = ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi0[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0) -1:0];
      r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1] = ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi1[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1) -1:0];
      r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST] = ff_regb_ddrc_ch0_ppt2_burst;
      r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_WAIT_REF+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_WAIT_REF] = ff_regb_ddrc_ch0_ppt2_wait_ref;
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP1
   //------------------------
   always_comb begin : r495_addrmap1_map0_combo_PROC
      r495_addrmap1_map0 = {REG_WIDTH {1'b0}};
      r495_addrmap1_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP1_ADDRMAP_CS_BIT0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0] = cfgs_ff_regb_addr_map0_addrmap_cs_bit0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP3
   //------------------------
   always_comb begin : r497_addrmap3_map0_combo_PROC
      r497_addrmap3_map0 = {REG_WIDTH {1'b0}};
      r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0] = cfgs_ff_regb_addr_map0_addrmap_bank_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0) -1:0];
      r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1] = cfgs_ff_regb_addr_map0_addrmap_bank_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1) -1:0];
      r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B2+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2] = cfgs_ff_regb_addr_map0_addrmap_bank_b2[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP4
   //------------------------
   always_comb begin : r498_addrmap4_map0_combo_PROC
      r498_addrmap4_map0 = {REG_WIDTH {1'b0}};
      r498_addrmap4_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0] = cfgs_ff_regb_addr_map0_addrmap_bg_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0) -1:0];
      r498_addrmap4_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1] = cfgs_ff_regb_addr_map0_addrmap_bg_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP5
   //------------------------
   always_comb begin : r499_addrmap5_map0_combo_PROC
      r499_addrmap5_map0 = {REG_WIDTH {1'b0}};
      r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B7+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7] = cfgs_ff_regb_addr_map0_addrmap_col_b7[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7) -1:0];
      r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B8+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8] = cfgs_ff_regb_addr_map0_addrmap_col_b8[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8) -1:0];
      r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B9+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9] = cfgs_ff_regb_addr_map0_addrmap_col_b9[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9) -1:0];
      r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B10+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10] = cfgs_ff_regb_addr_map0_addrmap_col_b10[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP6
   //------------------------
   always_comb begin : r500_addrmap6_map0_combo_PROC
      r500_addrmap6_map0 = {REG_WIDTH {1'b0}};
      r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B3+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3] = cfgs_ff_regb_addr_map0_addrmap_col_b3[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3) -1:0];
      r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B4+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4] = cfgs_ff_regb_addr_map0_addrmap_col_b4[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4) -1:0];
      r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B5+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5] = cfgs_ff_regb_addr_map0_addrmap_col_b5[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5) -1:0];
      r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B6+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6] = cfgs_ff_regb_addr_map0_addrmap_col_b6[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP7
   //------------------------
   always_comb begin : r501_addrmap7_map0_combo_PROC
      r501_addrmap7_map0 = {REG_WIDTH {1'b0}};
      r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B14+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14] = cfgs_ff_regb_addr_map0_addrmap_row_b14[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14) -1:0];
      r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B15+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15] = cfgs_ff_regb_addr_map0_addrmap_row_b15[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15) -1:0];
      r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B16+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16] = cfgs_ff_regb_addr_map0_addrmap_row_b16[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16) -1:0];
      r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B17+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17] = cfgs_ff_regb_addr_map0_addrmap_row_b17[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP8
   //------------------------
   always_comb begin : r502_addrmap8_map0_combo_PROC
      r502_addrmap8_map0 = {REG_WIDTH {1'b0}};
      r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B10+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10] = cfgs_ff_regb_addr_map0_addrmap_row_b10[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10) -1:0];
      r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B11+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11] = cfgs_ff_regb_addr_map0_addrmap_row_b11[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11) -1:0];
      r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B12+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12] = cfgs_ff_regb_addr_map0_addrmap_row_b12[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12) -1:0];
      r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B13+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13] = cfgs_ff_regb_addr_map0_addrmap_row_b13[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP9
   //------------------------
   always_comb begin : r503_addrmap9_map0_combo_PROC
      r503_addrmap9_map0 = {REG_WIDTH {1'b0}};
      r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B6+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6] = cfgs_ff_regb_addr_map0_addrmap_row_b6[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6) -1:0];
      r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B7+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7] = cfgs_ff_regb_addr_map0_addrmap_row_b7[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7) -1:0];
      r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B8+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8] = cfgs_ff_regb_addr_map0_addrmap_row_b8[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8) -1:0];
      r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B9+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9] = cfgs_ff_regb_addr_map0_addrmap_row_b9[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP10
   //------------------------
   always_comb begin : r504_addrmap10_map0_combo_PROC
      r504_addrmap10_map0 = {REG_WIDTH {1'b0}};
      r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B2+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2] = cfgs_ff_regb_addr_map0_addrmap_row_b2[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2) -1:0];
      r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B3+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3] = cfgs_ff_regb_addr_map0_addrmap_row_b3[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3) -1:0];
      r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B4+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4] = cfgs_ff_regb_addr_map0_addrmap_row_b4[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4) -1:0];
      r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B5+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5] = cfgs_ff_regb_addr_map0_addrmap_row_b5[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP11
   //------------------------
   always_comb begin : r505_addrmap11_map0_combo_PROC
      r505_addrmap11_map0 = {REG_WIDTH {1'b0}};
      r505_addrmap11_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0] = cfgs_ff_regb_addr_map0_addrmap_row_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0) -1:0];
      r505_addrmap11_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1] = cfgs_ff_regb_addr_map0_addrmap_row_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP12
   //------------------------
   always_comb begin : r506_addrmap12_map0_combo_PROC
      r506_addrmap12_map0 = {REG_WIDTH {1'b0}};
      r506_addrmap12_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_NONBINARY_DEVICE_DENSITY+:`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY] = ff_regb_addr_map0_nonbinary_device_density[(`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY) -1:0];
      r506_addrmap12_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_BANK_HASH_EN+:`REGB_ADDR_MAP0_SIZE_ADDRMAP12_BANK_HASH_EN] = ff_regb_addr_map0_bank_hash_en;
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCCFG
   //------------------------
   always_comb begin : r521_pccfg_port0_combo_PROC
      r521_pccfg_port0 = {REG_WIDTH {1'b0}};
      r521_pccfg_port0[`REGB_ARB_PORT0_OFFSET_PCCFG_GO2CRITICAL_EN+:`REGB_ARB_PORT0_SIZE_PCCFG_GO2CRITICAL_EN] = cfgs_ff_regb_arb_port0_go2critical_en;
      r521_pccfg_port0[`REGB_ARB_PORT0_OFFSET_PCCFG_PAGEMATCH_LIMIT+:`REGB_ARB_PORT0_SIZE_PCCFG_PAGEMATCH_LIMIT] = cfgs_ff_regb_arb_port0_pagematch_limit;
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGR
   //------------------------
   always_comb begin : r522_pcfgr_port0_combo_PROC
      r522_pcfgr_port0 = {REG_WIDTH {1'b0}};
      r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PRIORITY+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY] = cfgs_ff_regb_arb_port0_rd_port_priority[(`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY) -1:0];
      r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_AGING_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_AGING_EN] = cfgs_ff_regb_arb_port0_rd_port_aging_en;
      r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_URGENT_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_URGENT_EN] = cfgs_ff_regb_arb_port0_rd_port_urgent_en;
      r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PAGEMATCH_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PAGEMATCH_EN] = cfgs_ff_regb_arb_port0_rd_port_pagematch_en;
      r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RRB_LOCK_THRESHOLD+:`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD] = cfgs_ff_regb_arb_port0_rrb_lock_threshold[(`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGW
   //------------------------
   always_comb begin : r523_pcfgw_port0_combo_PROC
      r523_pcfgw_port0 = {REG_WIDTH {1'b0}};
      r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PRIORITY+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY] = cfgs_ff_regb_arb_port0_wr_port_priority[(`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY) -1:0];
      r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_AGING_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_AGING_EN] = cfgs_ff_regb_arb_port0_wr_port_aging_en;
      r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_URGENT_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_URGENT_EN] = cfgs_ff_regb_arb_port0_wr_port_urgent_en;
      r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PAGEMATCH_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PAGEMATCH_EN] = cfgs_ff_regb_arb_port0_wr_port_pagematch_en;
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCTRL
   //------------------------
   always_comb begin : r556_pctrl_port0_combo_PROC
      r556_pctrl_port0 = {REG_WIDTH {1'b0}};
      r556_pctrl_port0[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN+:`REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN] = ff_regb_arb_port0_port_en;
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS0
   //------------------------
   always_comb begin : r557_pcfgqos0_port0_combo_PROC
      r557_pcfgqos0_port0 = {REG_WIDTH {1'b0}};
      r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL1+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1] = cfgs_ff_regb_arb_port0_rqos_map_level1[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1) -1:0];
      r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL2+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2] = cfgs_ff_regb_arb_port0_rqos_map_level2[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2) -1:0];
      r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION0+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0] = cfgs_ff_regb_arb_port0_rqos_map_region0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0) -1:0];
      r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION1+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1] = cfgs_ff_regb_arb_port0_rqos_map_region1[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1) -1:0];
      r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION2+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2] = cfgs_ff_regb_arb_port0_rqos_map_region2[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS1
   //------------------------
   always_comb begin : r558_pcfgqos1_port0_combo_PROC
      r558_pcfgqos1_port0 = {REG_WIDTH {1'b0}};
      r558_pcfgqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTB+:`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB] = cfgs_ff_regb_arb_port0_rqos_map_timeoutb[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB) -1:0];
      r558_pcfgqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTR+:`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR] = cfgs_ff_regb_arb_port0_rqos_map_timeoutr[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS0
   //------------------------
   always_comb begin : r559_pcfgwqos0_port0_combo_PROC
      r559_pcfgwqos0_port0 = {REG_WIDTH {1'b0}};
      r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1] = cfgs_ff_regb_arb_port0_wqos_map_level1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1) -1:0];
      r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2] = cfgs_ff_regb_arb_port0_wqos_map_level2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2) -1:0];
      r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION0+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0] = cfgs_ff_regb_arb_port0_wqos_map_region0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0) -1:0];
      r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1] = cfgs_ff_regb_arb_port0_wqos_map_region1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1) -1:0];
      r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2] = cfgs_ff_regb_arb_port0_wqos_map_region2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS1
   //------------------------
   always_comb begin : r560_pcfgwqos1_port0_combo_PROC
      r560_pcfgwqos1_port0 = {REG_WIDTH {1'b0}};
      r560_pcfgwqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1] = cfgs_ff_regb_arb_port0_wqos_map_timeout1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1) -1:0];
      r560_pcfgwqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2] = cfgs_ff_regb_arb_port0_wqos_map_timeout2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRCTL
   //------------------------
   always_comb begin : r569_sbrctl_port0_combo_PROC
      r569_sbrctl_port0 = {REG_WIDTH {1'b0}};
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_EN+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_EN] = ff_regb_arb_port0_scrub_en;
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_DURING_LOWPOWER+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_DURING_LOWPOWER] = ff_regb_arb_port0_scrub_during_lowpower;
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_NM+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM] = ff_regb_arb_port0_scrub_burst_length_nm[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM) -1:0];
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_INTERVAL+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL] = ff_regb_arb_port0_scrub_interval[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL) -1:0];
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_CMD_TYPE+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE] = ff_regb_arb_port0_scrub_cmd_type[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE) -1:0];
      r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_LP+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP] = ff_regb_arb_port0_scrub_burst_length_lp[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRWDATA0
   //------------------------
   always_comb begin : r571_sbrwdata0_port0_combo_PROC
      r571_sbrwdata0_port0 = {REG_WIDTH {1'b0}};
      r571_sbrwdata0_port0[`REGB_ARB_PORT0_OFFSET_SBRWDATA0_SCRUB_PATTERN0+:`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0] = ff_regb_arb_port0_scrub_pattern0[(`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART0
   //------------------------
   always_comb begin : r573_sbrstart0_port0_combo_PROC
      r573_sbrstart0_port0 = {REG_WIDTH {1'b0}};
      r573_sbrstart0_port0[`REGB_ARB_PORT0_OFFSET_SBRSTART0_SBR_ADDRESS_START_MASK_0+:`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0] = ff_regb_arb_port0_sbr_address_start_mask_0[(`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART1
   //------------------------
   always_comb begin : r574_sbrstart1_port0_combo_PROC
      r574_sbrstart1_port0 = {REG_WIDTH {1'b0}};
      r574_sbrstart1_port0[`REGB_ARB_PORT0_OFFSET_SBRSTART1_SBR_ADDRESS_START_MASK_1+:`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1] = ff_regb_arb_port0_sbr_address_start_mask_1[(`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE0
   //------------------------
   always_comb begin : r575_sbrrange0_port0_combo_PROC
      r575_sbrrange0_port0 = {REG_WIDTH {1'b0}};
      r575_sbrrange0_port0[`REGB_ARB_PORT0_OFFSET_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0+:`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0] = ff_regb_arb_port0_sbr_address_range_mask_0[(`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0) -1:0];
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE1
   //------------------------
   always_comb begin : r576_sbrrange1_port0_combo_PROC
      r576_sbrrange1_port0 = {REG_WIDTH {1'b0}};
      r576_sbrrange1_port0[`REGB_ARB_PORT0_OFFSET_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1+:`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1] = ff_regb_arb_port0_sbr_address_range_mask_1[(`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG0
   //------------------------
   always_comb begin : r1929_dramset1tmg0_freq0_combo_PROC
      r1929_dramset1tmg0_freq0 = {REG_WIDTH {1'b0}};
      r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] = cfgs_ff_regb_freq0_ch0_t_ras_min[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0];
      r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] = cfgs_ff_regb_freq0_ch0_t_ras_max[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0];
      r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW] = cfgs_ff_regb_freq0_ch0_t_faw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0];
      r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE] = cfgs_ff_regb_freq0_ch0_wr2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG1
   //------------------------
   always_comb begin : r1930_dramset1tmg1_freq0_combo_PROC
      r1930_dramset1tmg1_freq0 = {REG_WIDTH {1'b0}};
      r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC] = cfgs_ff_regb_freq0_ch0_t_rc[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0];
      r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE] = cfgs_ff_regb_freq0_ch0_rd2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0];
      r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP] = cfgs_ff_regb_freq0_ch0_t_xp[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0];
      r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] = cfgs_ff_regb_freq0_ch0_t_rcd_write[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG2
   //------------------------
   always_comb begin : r1931_dramset1tmg2_freq0_combo_PROC
      r1931_dramset1tmg2_freq0 = {REG_WIDTH {1'b0}};
      r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD] = cfgs_ff_regb_freq0_ch0_wr2rd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0];
      r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR] = cfgs_ff_regb_freq0_ch0_rd2wr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0];
      r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] = cfgs_ff_regb_freq0_ch0_read_latency[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0];
      r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] = cfgs_ff_regb_freq0_ch0_write_latency[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG3
   //------------------------
   always_comb begin : r1932_dramset1tmg3_freq0_combo_PROC
      r1932_dramset1tmg3_freq0 = {REG_WIDTH {1'b0}};
      r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR] = cfgs_ff_regb_freq0_ch0_wr2mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0];
      r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR] = cfgs_ff_regb_freq0_ch0_rd2mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0];
      r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR] = cfgs_ff_regb_freq0_ch0_t_mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG4
   //------------------------
   always_comb begin : r1933_dramset1tmg4_freq0_combo_PROC
      r1933_dramset1tmg4_freq0 = {REG_WIDTH {1'b0}};
      r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP] = cfgs_ff_regb_freq0_ch0_t_rp[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0];
      r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD] = cfgs_ff_regb_freq0_ch0_t_rrd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0];
      r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD] = cfgs_ff_regb_freq0_ch0_t_ccd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0];
      r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD] = cfgs_ff_regb_freq0_ch0_t_rcd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG5
   //------------------------
   always_comb begin : r1934_dramset1tmg5_freq0_combo_PROC
      r1934_dramset1tmg5_freq0 = {REG_WIDTH {1'b0}};
      r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE] = ff_regb_freq0_ch0_t_cke[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0];
      r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR] = ff_regb_freq0_ch0_t_ckesr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0];
      r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] = ff_regb_freq0_ch0_t_cksre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0];
      r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] = ff_regb_freq0_ch0_t_cksrx[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG6
   //------------------------
   always_comb begin : r1935_dramset1tmg6_freq0_combo_PROC
      r1935_dramset1tmg6_freq0 = {REG_WIDTH {1'b0}};
      r1935_dramset1tmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] = cfgs_ff_regb_freq0_ch0_t_ckcsx[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG7
   //------------------------
   always_comb begin : r1936_dramset1tmg7_freq0_combo_PROC
      r1936_dramset1tmg7_freq0 = {REG_WIDTH {1'b0}};
      r1936_dramset1tmg7_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH] = ff_regb_freq0_ch0_t_csh[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG9
   //------------------------
   always_comb begin : r1938_dramset1tmg9_freq0_combo_PROC
      r1938_dramset1tmg9_freq0 = {REG_WIDTH {1'b0}};
      r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] = cfgs_ff_regb_freq0_ch0_wr2rd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0];
      r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] = cfgs_ff_regb_freq0_ch0_t_rrd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0];
      r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] = cfgs_ff_regb_freq0_ch0_t_ccd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG12
   //------------------------
   always_comb begin : r1941_dramset1tmg12_freq0_combo_PROC
      r1941_dramset1tmg12_freq0 = {REG_WIDTH {1'b0}};
      r1941_dramset1tmg12_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] = cfgs_ff_regb_freq0_ch0_t_cmdcke[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG13
   //------------------------
   always_comb begin : r1942_dramset1tmg13_freq0_combo_PROC
      r1942_dramset1tmg13_freq0 = {REG_WIDTH {1'b0}};
      r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD] = cfgs_ff_regb_freq0_ch0_t_ppd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0];
      r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] = cfgs_ff_regb_freq0_ch0_t_ccd_mw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0];
      r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] = cfgs_ff_regb_freq0_ch0_odtloff[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG14
   //------------------------
   always_comb begin : r1943_dramset1tmg14_freq0_combo_PROC
      r1943_dramset1tmg14_freq0 = {REG_WIDTH {1'b0}};
      r1943_dramset1tmg14_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR] = cfgs_ff_regb_freq0_ch0_t_xsr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0];
      r1943_dramset1tmg14_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO] = cfgs_ff_regb_freq0_ch0_t_osco[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG17
   //------------------------
   always_comb begin : r1946_dramset1tmg17_freq0_combo_PROC
      r1946_dramset1tmg17_freq0 = {REG_WIDTH {1'b0}};
      r1946_dramset1tmg17_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] = cfgs_ff_regb_freq0_ch0_t_vrcg_disable[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0];
      r1946_dramset1tmg17_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] = cfgs_ff_regb_freq0_ch0_t_vrcg_enable[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG23
   //------------------------
   always_comb begin : r1951_dramset1tmg23_freq0_combo_PROC
      r1951_dramset1tmg23_freq0 = {REG_WIDTH {1'b0}};
      r1951_dramset1tmg23_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN] = ff_regb_freq0_ch0_t_pdn[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0];
      r1951_dramset1tmg23_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] = ff_regb_freq0_ch0_t_xsr_dsm_x1024[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG24
   //------------------------
   always_comb begin : r1952_dramset1tmg24_freq0_combo_PROC
      r1952_dramset1tmg24_freq0 = {REG_WIDTH {1'b0}};
      r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] = cfgs_ff_regb_freq0_ch0_max_wr_sync[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0];
      r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] = cfgs_ff_regb_freq0_ch0_max_rd_sync[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0];
      r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] = cfgs_ff_regb_freq0_ch0_rd2wr_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0];
      r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] = cfgs_ff_regb_freq0_ch0_bank_org[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG25
   //------------------------
   always_comb begin : r1953_dramset1tmg25_freq0_combo_PROC
      r1953_dramset1tmg25_freq0 = {REG_WIDTH {1'b0}};
      r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] = cfgs_ff_regb_freq0_ch0_rda2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0];
      r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] = cfgs_ff_regb_freq0_ch0_wra2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0];
      r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] = cfgs_ff_regb_freq0_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG30
   //------------------------
   always_comb begin : r1958_dramset1tmg30_freq0_combo_PROC
      r1958_dramset1tmg30_freq0 = {REG_WIDTH {1'b0}};
      r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD] = ff_regb_freq0_ch0_mrr2rd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0];
      r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR] = ff_regb_freq0_ch0_mrr2wr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0];
      r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] = ff_regb_freq0_ch0_mrr2mrw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG32
   //------------------------
   always_comb begin : r1960_dramset1tmg32_freq0_combo_PROC
      r1960_dramset1tmg32_freq0 = {REG_WIDTH {1'b0}};
      r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] = ff_regb_freq0_ch0_ws_fs2wck_sus[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0];
      r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] = ff_regb_freq0_ch0_t_wcksus[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0];
      r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] = ff_regb_freq0_ch0_ws_off2ws_fs[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR0
   //------------------------
   always_comb begin : r1991_initmr0_freq0_combo_PROC
      r1991_initmr0_freq0 = {REG_WIDTH {1'b0}};
      r1991_initmr0_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ0_CH0_SIZE_INITMR0_EMR] = cfgs_ff_regb_freq0_ch0_emr[(`REGB_FREQ0_CH0_SIZE_INITMR0_EMR) -1:0];
      r1991_initmr0_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ0_CH0_SIZE_INITMR0_MR] = cfgs_ff_regb_freq0_ch0_mr[(`REGB_FREQ0_CH0_SIZE_INITMR0_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR1
   //------------------------
   always_comb begin : r1992_initmr1_freq0_combo_PROC
      r1992_initmr1_freq0 = {REG_WIDTH {1'b0}};
      r1992_initmr1_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3] = ff_regb_freq0_ch0_emr3[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3) -1:0];
      r1992_initmr1_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2] = ff_regb_freq0_ch0_emr2[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR2
   //------------------------
   always_comb begin : r1993_initmr2_freq0_combo_PROC
      r1993_initmr2_freq0 = {REG_WIDTH {1'b0}};
      r1993_initmr2_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ0_CH0_SIZE_INITMR2_MR5] = cfgs_ff_regb_freq0_ch0_mr5[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR5) -1:0];
      r1993_initmr2_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ0_CH0_SIZE_INITMR2_MR4] = cfgs_ff_regb_freq0_ch0_mr4[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR4) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR3
   //------------------------
   always_comb begin : r1994_initmr3_freq0_combo_PROC
      r1994_initmr3_freq0 = {REG_WIDTH {1'b0}};
      r1994_initmr3_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ0_CH0_SIZE_INITMR3_MR6] = cfgs_ff_regb_freq0_ch0_mr6[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR6) -1:0];
      r1994_initmr3_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ0_CH0_SIZE_INITMR3_MR22] = cfgs_ff_regb_freq0_ch0_mr22[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR22) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG0
   //------------------------
   always_comb begin : r1995_dfitmg0_freq0_combo_PROC
      r1995_dfitmg0_freq0 = {REG_WIDTH {1'b0}};
      r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] = ff_regb_freq0_ch0_dfi_tphy_wrlat[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0];
      r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] = ff_regb_freq0_ch0_dfi_tphy_wrdata[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0];
      r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] = ff_regb_freq0_ch0_dfi_t_rddata_en[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0];
      r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] = ff_regb_freq0_ch0_dfi_t_ctrl_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG1
   //------------------------
   always_comb begin : r1996_dfitmg1_freq0_combo_PROC
      r1996_dfitmg1_freq0 = {REG_WIDTH {1'b0}};
      r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] = ff_regb_freq0_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0];
      r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] = ff_regb_freq0_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0];
      r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] = ff_regb_freq0_ch0_dfi_t_wrdata_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG2
   //------------------------
   always_comb begin : r1997_dfitmg2_freq0_combo_PROC
      r1997_dfitmg2_freq0 = {REG_WIDTH {1'b0}};
      r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] = cfgs_ff_regb_freq0_ch0_dfi_tphy_wrcslat[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0];
      r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] = cfgs_ff_regb_freq0_ch0_dfi_tphy_rdcslat[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0];
      r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] = cfgs_ff_regb_freq0_ch0_dfi_twck_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG4
   //------------------------
   always_comb begin : r1999_dfitmg4_freq0_combo_PROC
      r1999_dfitmg4_freq0 = {REG_WIDTH {1'b0}};
      r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] = cfgs_ff_regb_freq0_ch0_dfi_twck_dis[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0];
      r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] = cfgs_ff_regb_freq0_ch0_dfi_twck_en_fs[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0];
      r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] = cfgs_ff_regb_freq0_ch0_dfi_twck_en_wr[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0];
      r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] = cfgs_ff_regb_freq0_ch0_dfi_twck_en_rd[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG5
   //------------------------
   always_comb begin : r2000_dfitmg5_freq0_combo_PROC
      r2000_dfitmg5_freq0 = {REG_WIDTH {1'b0}};
      r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] = cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0];
      r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] = cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_cs[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0];
      r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] = cfgs_ff_regb_freq0_ch0_dfi_twck_toggle[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0];
      r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] = cfgs_ff_regb_freq0_ch0_dfi_twck_fast_toggle[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG6
   //------------------------
   always_comb begin : r2001_dfitmg6_freq0_combo_PROC
      r2001_dfitmg6_freq0 = {REG_WIDTH {1'b0}};
      r2001_dfitmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] = cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0];
      r2001_dfitmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] = cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd_en;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG0
   //------------------------
   always_comb begin : r2003_dfilptmg0_freq0_combo_PROC
      r2003_dfilptmg0_freq0 = {REG_WIDTH {1'b0}};
      r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_PD+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD] = ff_regb_freq0_ch0_dfi_lp_wakeup_pd[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD) -1:0];
      r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_SR+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR] = ff_regb_freq0_ch0_dfi_lp_wakeup_sr[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR) -1:0];
      r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_DSM+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM] = ff_regb_freq0_ch0_dfi_lp_wakeup_dsm[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG1
   //------------------------
   always_comb begin : r2004_dfilptmg1_freq0_combo_PROC
      r2004_dfilptmg1_freq0 = {REG_WIDTH {1'b0}};
      r2004_dfilptmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_LP_WAKEUP_DATA+:`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA] = ff_regb_freq0_ch0_dfi_lp_wakeup_data[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA) -1:0];
      r2004_dfilptmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_TLP_RESP+:`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP] = ff_regb_freq0_ch0_dfi_tlp_resp[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG0
   //------------------------
   always_comb begin : r2005_dfiupdtmg0_freq0_combo_PROC
      r2005_dfiupdtmg0_freq0 = {REG_WIDTH {1'b0}};
      r2005_dfiupdtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MIN+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN] = ff_regb_freq0_ch0_dfi_t_ctrlup_min[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN) -1:0];
      r2005_dfiupdtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MAX+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX] = ff_regb_freq0_ch0_dfi_t_ctrlup_max[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG1
   //------------------------
   always_comb begin : r2006_dfiupdtmg1_freq0_combo_PROC
      r2006_dfiupdtmg1_freq0 = {REG_WIDTH {1'b0}};
      r2006_dfiupdtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] = cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0];
      r2006_dfiupdtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] = cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG2
   //------------------------
   always_comb begin : r2008_dfiupdtmg2_freq0_combo_PROC
      r2008_dfiupdtmg2_freq0 = {REG_WIDTH {1'b0}};
      r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] = ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0];
      r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] = ff_regb_freq0_ch0_ctrlupd_after_dqsosc;
      r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] = ff_regb_freq0_ch0_ppt2_override;
      r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_EN] = ff_regb_freq0_ch0_ppt2_en;
      r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] = ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG3
   //------------------------
   always_comb begin : r2009_dfiupdtmg3_freq0_combo_PROC
      r2009_dfiupdtmg3_freq0 = {REG_WIDTH {1'b0}};
      r2009_dfiupdtmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] = cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG0
   //------------------------
   always_comb begin : r2010_rfshset1tmg0_freq0_combo_PROC
      r2010_rfshset1tmg0_freq0 = {REG_WIDTH {1'b0}};
      r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] = ff_regb_freq0_ch0_t_refi_x1_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0];
      r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] = ff_regb_freq0_ch0_refresh_to_x1_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0];
      r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] = ff_regb_freq0_ch0_refresh_margin[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0];
      r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] = ff_regb_freq0_ch0_refresh_to_x1_sel;
      r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] = ff_regb_freq0_ch0_t_refi_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG1
   //------------------------
   always_comb begin : r2011_rfshset1tmg1_freq0_combo_PROC
      r2011_rfshset1tmg1_freq0 = {REG_WIDTH {1'b0}};
      r2011_rfshset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] = ff_regb_freq0_ch0_t_rfc_min[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0];
      r2011_rfshset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] = ff_regb_freq0_ch0_t_rfc_min_ab[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG2
   //------------------------
   always_comb begin : r2012_rfshset1tmg2_freq0_combo_PROC
      r2012_rfshset1tmg2_freq0 = {REG_WIDTH {1'b0}};
      r2012_rfshset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] = ff_regb_freq0_ch0_t_pbr2pbr[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0];
      r2012_rfshset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] = ff_regb_freq0_ch0_t_pbr2act[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG3
   //------------------------
   always_comb begin : r2013_rfshset1tmg3_freq0_combo_PROC
      r2013_rfshset1tmg3_freq0 = {REG_WIDTH {1'b0}};
      r2013_rfshset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] = ff_regb_freq0_ch0_refresh_to_ab_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG4
   //------------------------
   always_comb begin : r2014_rfshset1tmg4_freq0_combo_PROC
      r2014_rfshset1tmg4_freq0 = {REG_WIDTH {1'b0}};
      r2014_rfshset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] = ff_regb_freq0_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0];
      r2014_rfshset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] = ff_regb_freq0_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RFMSET1TMG0
   //------------------------
   always_comb begin : r2024_rfmset1tmg0_freq0_combo_PROC
      r2024_rfmset1tmg0_freq0 = {REG_WIDTH {1'b0}};
      r2024_rfmset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB] = ff_regb_freq0_ch0_t_rfmpb[(`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG0
   //------------------------
   always_comb begin : r2035_zqset1tmg0_freq0_combo_PROC
      r2035_zqset1tmg0_freq0 = {REG_WIDTH {1'b0}};
      r2035_zqset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] = ff_regb_freq0_ch0_t_zq_long_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0];
      r2035_zqset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] = ff_regb_freq0_ch0_t_zq_short_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG1
   //------------------------
   always_comb begin : r2036_zqset1tmg1_freq0_combo_PROC
      r2036_zqset1tmg1_freq0 = {REG_WIDTH {1'b0}};
      r2036_zqset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] = cfgs_ff_regb_freq0_ch0_t_zq_short_interval_x1024[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0];
      r2036_zqset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] = cfgs_ff_regb_freq0_ch0_t_zq_reset_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG2
   //------------------------
   always_comb begin : r2037_zqset1tmg2_freq0_combo_PROC
      r2037_zqset1tmg2_freq0 = {REG_WIDTH {1'b0}};
      r2037_zqset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] = ff_regb_freq0_ch0_t_zq_stop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DQSOSCCTL0
   //------------------------
   always_comb begin : r2046_dqsoscctl0_freq0_combo_PROC
      r2046_dqsoscctl0_freq0 = {REG_WIDTH {1'b0}};
      r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] = ff_regb_freq0_ch0_dqsosc_enable;
      r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] = ff_regb_freq0_ch0_dqsosc_interval_unit;
      r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] = ff_regb_freq0_ch0_dqsosc_interval[(`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEINT
   //------------------------
   always_comb begin : r2047_derateint_freq0_combo_PROC
      r2047_derateint_freq0 = {REG_WIDTH {1'b0}};
      r2047_derateint_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] = cfgs_ff_regb_freq0_ch0_mr4_read_interval[(`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL0
   //------------------------
   always_comb begin : r2048_derateval0_freq0_combo_PROC
      r2048_derateval0_freq0 = {REG_WIDTH {1'b0}};
      r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] = ff_regb_freq0_ch0_derated_t_rrd[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0];
      r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP] = ff_regb_freq0_ch0_derated_t_rp[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0];
      r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] = ff_regb_freq0_ch0_derated_t_ras_min[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0];
      r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] = ff_regb_freq0_ch0_derated_t_rcd[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL1
   //------------------------
   always_comb begin : r2049_derateval1_freq0_combo_PROC
      r2049_derateval1_freq0 = {REG_WIDTH {1'b0}};
      r2049_derateval1_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC] = ff_regb_freq0_ch0_derated_t_rc[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0];
      r2049_derateval1_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] = ff_regb_freq0_ch0_derated_t_rcd_write[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.HWLPTMG0
   //------------------------
   always_comb begin : r2050_hwlptmg0_freq0_combo_PROC
      r2050_hwlptmg0_freq0 = {REG_WIDTH {1'b0}};
      r2050_hwlptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] = cfgs_ff_regb_freq0_ch0_hw_lp_idle_x32[(`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DVFSCTL0
   //------------------------
   always_comb begin : r2051_dvfsctl0_freq0_combo_PROC
      r2051_dvfsctl0_freq0 = {REG_WIDTH {1'b0}};
      r2051_dvfsctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ0_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] = cfgs_ff_regb_freq0_ch0_dvfsq_enable;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.SCHEDTMG0
   //------------------------
   always_comb begin : r2052_schedtmg0_freq0_combo_PROC
      r2052_schedtmg0_freq0 = {REG_WIDTH {1'b0}};
      r2052_schedtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] = cfgs_ff_regb_freq0_ch0_pageclose_timer[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0];
      r2052_schedtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] = cfgs_ff_regb_freq0_ch0_rdwr_idle_gap[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFHPR1
   //------------------------
   always_comb begin : r2053_perfhpr1_freq0_combo_PROC
      r2053_perfhpr1_freq0 = {REG_WIDTH {1'b0}};
      r2053_perfhpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] = cfgs_ff_regb_freq0_ch0_hpr_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0];
      r2053_perfhpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq0_ch0_hpr_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFLPR1
   //------------------------
   always_comb begin : r2054_perflpr1_freq0_combo_PROC
      r2054_perflpr1_freq0 = {REG_WIDTH {1'b0}};
      r2054_perflpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] = cfgs_ff_regb_freq0_ch0_lpr_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0];
      r2054_perflpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq0_ch0_lpr_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFWR1
   //------------------------
   always_comb begin : r2055_perfwr1_freq0_combo_PROC
      r2055_perfwr1_freq0 = {REG_WIDTH {1'b0}};
      r2055_perfwr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE] = cfgs_ff_regb_freq0_ch0_w_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0];
      r2055_perfwr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] = cfgs_ff_regb_freq0_ch0_w_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.TMGCFG
   //------------------------
   always_comb begin : r2056_tmgcfg_freq0_combo_PROC
      r2056_tmgcfg_freq0 = {REG_WIDTH {1'b0}};
      r2056_tmgcfg_freq0[`REGB_FREQ0_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ0_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] = ff_regb_freq0_ch0_frequency_ratio;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG0
   //------------------------
   always_comb begin : r2057_ranktmg0_freq0_combo_PROC
      r2057_ranktmg0_freq0 = {REG_WIDTH {1'b0}};
      r2057_ranktmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] = cfgs_ff_regb_freq0_ch0_diff_rank_rd_gap[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0];
      r2057_ranktmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] = cfgs_ff_regb_freq0_ch0_diff_rank_wr_gap[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG1
   //------------------------
   always_comb begin : r2058_ranktmg1_freq0_combo_PROC
      r2058_ranktmg1_freq0 = {REG_WIDTH {1'b0}};
      r2058_ranktmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR] = cfgs_ff_regb_freq0_ch0_wr2rd_dr[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0];
      r2058_ranktmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR] = cfgs_ff_regb_freq0_ch0_rd2wr_dr[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.PWRTMG
   //------------------------
   always_comb begin : r2059_pwrtmg_freq0_combo_PROC
      r2059_pwrtmg_freq0 = {REG_WIDTH {1'b0}};
      r2059_pwrtmg_freq0[`REGB_FREQ0_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] = cfgs_ff_regb_freq0_ch0_powerdown_to_x32[(`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0];
      r2059_pwrtmg_freq0[`REGB_FREQ0_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32] = cfgs_ff_regb_freq0_ch0_selfref_to_x32[(`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG0
   //------------------------
   always_comb begin : r2065_ddr4pprtmg0_freq0_combo_PROC
      r2065_ddr4pprtmg0_freq0 = {REG_WIDTH {1'b0}};
      r2065_ddr4pprtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] = cfgs_ff_regb_freq0_ch0_t_pgm_x1_x1024[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0];
      r2065_ddr4pprtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] = cfgs_ff_regb_freq0_ch0_t_pgm_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG1
   //------------------------
   always_comb begin : r2066_ddr4pprtmg1_freq0_combo_PROC
      r2066_ddr4pprtmg1_freq0 = {REG_WIDTH {1'b0}};
      r2066_ddr4pprtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] = cfgs_ff_regb_freq0_ch0_t_pgmpst_x32[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0];
      r2066_ddr4pprtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] = cfgs_ff_regb_freq0_ch0_t_pgm_exit[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ0_CH0.LNKECCCTL0
   //------------------------
   always_comb begin : r2067_lnkeccctl0_freq0_combo_PROC
      r2067_lnkeccctl0_freq0 = {REG_WIDTH {1'b0}};
      r2067_lnkeccctl0_freq0[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ0_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] = ff_regb_freq0_ch0_wr_link_ecc_enable;
      r2067_lnkeccctl0_freq0[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ0_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] = ff_regb_freq0_ch0_rd_link_ecc_enable;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG0
   //------------------------
   always_comb begin : r2201_dramset1tmg0_freq1_combo_PROC
      r2201_dramset1tmg0_freq1 = {REG_WIDTH {1'b0}};
      r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] = cfgs_ff_regb_freq1_ch0_t_ras_min[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0];
      r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] = cfgs_ff_regb_freq1_ch0_t_ras_max[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0];
      r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW] = cfgs_ff_regb_freq1_ch0_t_faw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0];
      r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE] = cfgs_ff_regb_freq1_ch0_wr2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG1
   //------------------------
   always_comb begin : r2202_dramset1tmg1_freq1_combo_PROC
      r2202_dramset1tmg1_freq1 = {REG_WIDTH {1'b0}};
      r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC] = cfgs_ff_regb_freq1_ch0_t_rc[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0];
      r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE] = cfgs_ff_regb_freq1_ch0_rd2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0];
      r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP] = cfgs_ff_regb_freq1_ch0_t_xp[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0];
      r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] = cfgs_ff_regb_freq1_ch0_t_rcd_write[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG2
   //------------------------
   always_comb begin : r2203_dramset1tmg2_freq1_combo_PROC
      r2203_dramset1tmg2_freq1 = {REG_WIDTH {1'b0}};
      r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD] = cfgs_ff_regb_freq1_ch0_wr2rd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0];
      r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR] = cfgs_ff_regb_freq1_ch0_rd2wr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0];
      r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] = cfgs_ff_regb_freq1_ch0_read_latency[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0];
      r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] = cfgs_ff_regb_freq1_ch0_write_latency[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG3
   //------------------------
   always_comb begin : r2204_dramset1tmg3_freq1_combo_PROC
      r2204_dramset1tmg3_freq1 = {REG_WIDTH {1'b0}};
      r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR] = cfgs_ff_regb_freq1_ch0_wr2mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0];
      r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR] = cfgs_ff_regb_freq1_ch0_rd2mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0];
      r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR] = cfgs_ff_regb_freq1_ch0_t_mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG4
   //------------------------
   always_comb begin : r2205_dramset1tmg4_freq1_combo_PROC
      r2205_dramset1tmg4_freq1 = {REG_WIDTH {1'b0}};
      r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP] = cfgs_ff_regb_freq1_ch0_t_rp[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0];
      r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD] = cfgs_ff_regb_freq1_ch0_t_rrd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0];
      r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD] = cfgs_ff_regb_freq1_ch0_t_ccd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0];
      r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD] = cfgs_ff_regb_freq1_ch0_t_rcd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG5
   //------------------------
   always_comb begin : r2206_dramset1tmg5_freq1_combo_PROC
      r2206_dramset1tmg5_freq1 = {REG_WIDTH {1'b0}};
      r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE] = ff_regb_freq1_ch0_t_cke[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0];
      r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR] = ff_regb_freq1_ch0_t_ckesr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0];
      r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] = ff_regb_freq1_ch0_t_cksre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0];
      r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] = ff_regb_freq1_ch0_t_cksrx[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG6
   //------------------------
   always_comb begin : r2207_dramset1tmg6_freq1_combo_PROC
      r2207_dramset1tmg6_freq1 = {REG_WIDTH {1'b0}};
      r2207_dramset1tmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] = cfgs_ff_regb_freq1_ch0_t_ckcsx[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG7
   //------------------------
   always_comb begin : r2208_dramset1tmg7_freq1_combo_PROC
      r2208_dramset1tmg7_freq1 = {REG_WIDTH {1'b0}};
      r2208_dramset1tmg7_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH] = ff_regb_freq1_ch0_t_csh[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG9
   //------------------------
   always_comb begin : r2210_dramset1tmg9_freq1_combo_PROC
      r2210_dramset1tmg9_freq1 = {REG_WIDTH {1'b0}};
      r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] = cfgs_ff_regb_freq1_ch0_wr2rd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0];
      r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] = cfgs_ff_regb_freq1_ch0_t_rrd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0];
      r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] = cfgs_ff_regb_freq1_ch0_t_ccd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG12
   //------------------------
   always_comb begin : r2213_dramset1tmg12_freq1_combo_PROC
      r2213_dramset1tmg12_freq1 = {REG_WIDTH {1'b0}};
      r2213_dramset1tmg12_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] = cfgs_ff_regb_freq1_ch0_t_cmdcke[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG13
   //------------------------
   always_comb begin : r2214_dramset1tmg13_freq1_combo_PROC
      r2214_dramset1tmg13_freq1 = {REG_WIDTH {1'b0}};
      r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD] = cfgs_ff_regb_freq1_ch0_t_ppd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0];
      r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] = cfgs_ff_regb_freq1_ch0_t_ccd_mw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0];
      r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] = cfgs_ff_regb_freq1_ch0_odtloff[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG14
   //------------------------
   always_comb begin : r2215_dramset1tmg14_freq1_combo_PROC
      r2215_dramset1tmg14_freq1 = {REG_WIDTH {1'b0}};
      r2215_dramset1tmg14_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR] = cfgs_ff_regb_freq1_ch0_t_xsr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0];
      r2215_dramset1tmg14_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO] = cfgs_ff_regb_freq1_ch0_t_osco[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG17
   //------------------------
   always_comb begin : r2218_dramset1tmg17_freq1_combo_PROC
      r2218_dramset1tmg17_freq1 = {REG_WIDTH {1'b0}};
      r2218_dramset1tmg17_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] = cfgs_ff_regb_freq1_ch0_t_vrcg_disable[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0];
      r2218_dramset1tmg17_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] = cfgs_ff_regb_freq1_ch0_t_vrcg_enable[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG23
   //------------------------
   always_comb begin : r2223_dramset1tmg23_freq1_combo_PROC
      r2223_dramset1tmg23_freq1 = {REG_WIDTH {1'b0}};
      r2223_dramset1tmg23_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN] = ff_regb_freq1_ch0_t_pdn[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0];
      r2223_dramset1tmg23_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] = ff_regb_freq1_ch0_t_xsr_dsm_x1024[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG24
   //------------------------
   always_comb begin : r2224_dramset1tmg24_freq1_combo_PROC
      r2224_dramset1tmg24_freq1 = {REG_WIDTH {1'b0}};
      r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] = cfgs_ff_regb_freq1_ch0_max_wr_sync[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0];
      r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] = cfgs_ff_regb_freq1_ch0_max_rd_sync[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0];
      r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] = cfgs_ff_regb_freq1_ch0_rd2wr_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0];
      r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] = cfgs_ff_regb_freq1_ch0_bank_org[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG25
   //------------------------
   always_comb begin : r2225_dramset1tmg25_freq1_combo_PROC
      r2225_dramset1tmg25_freq1 = {REG_WIDTH {1'b0}};
      r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] = cfgs_ff_regb_freq1_ch0_rda2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0];
      r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] = cfgs_ff_regb_freq1_ch0_wra2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0];
      r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] = cfgs_ff_regb_freq1_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG30
   //------------------------
   always_comb begin : r2230_dramset1tmg30_freq1_combo_PROC
      r2230_dramset1tmg30_freq1 = {REG_WIDTH {1'b0}};
      r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD] = ff_regb_freq1_ch0_mrr2rd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0];
      r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR] = ff_regb_freq1_ch0_mrr2wr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0];
      r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] = ff_regb_freq1_ch0_mrr2mrw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG32
   //------------------------
   always_comb begin : r2232_dramset1tmg32_freq1_combo_PROC
      r2232_dramset1tmg32_freq1 = {REG_WIDTH {1'b0}};
      r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] = ff_regb_freq1_ch0_ws_fs2wck_sus[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0];
      r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] = ff_regb_freq1_ch0_t_wcksus[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0];
      r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] = ff_regb_freq1_ch0_ws_off2ws_fs[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR0
   //------------------------
   always_comb begin : r2263_initmr0_freq1_combo_PROC
      r2263_initmr0_freq1 = {REG_WIDTH {1'b0}};
      r2263_initmr0_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ1_CH0_SIZE_INITMR0_EMR] = cfgs_ff_regb_freq1_ch0_emr[(`REGB_FREQ1_CH0_SIZE_INITMR0_EMR) -1:0];
      r2263_initmr0_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ1_CH0_SIZE_INITMR0_MR] = cfgs_ff_regb_freq1_ch0_mr[(`REGB_FREQ1_CH0_SIZE_INITMR0_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR1
   //------------------------
   always_comb begin : r2264_initmr1_freq1_combo_PROC
      r2264_initmr1_freq1 = {REG_WIDTH {1'b0}};
      r2264_initmr1_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3] = ff_regb_freq1_ch0_emr3[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3) -1:0];
      r2264_initmr1_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2] = ff_regb_freq1_ch0_emr2[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR2
   //------------------------
   always_comb begin : r2265_initmr2_freq1_combo_PROC
      r2265_initmr2_freq1 = {REG_WIDTH {1'b0}};
      r2265_initmr2_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ1_CH0_SIZE_INITMR2_MR5] = cfgs_ff_regb_freq1_ch0_mr5[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR5) -1:0];
      r2265_initmr2_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ1_CH0_SIZE_INITMR2_MR4] = cfgs_ff_regb_freq1_ch0_mr4[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR4) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR3
   //------------------------
   always_comb begin : r2266_initmr3_freq1_combo_PROC
      r2266_initmr3_freq1 = {REG_WIDTH {1'b0}};
      r2266_initmr3_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ1_CH0_SIZE_INITMR3_MR6] = cfgs_ff_regb_freq1_ch0_mr6[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR6) -1:0];
      r2266_initmr3_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ1_CH0_SIZE_INITMR3_MR22] = cfgs_ff_regb_freq1_ch0_mr22[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR22) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG0
   //------------------------
   always_comb begin : r2267_dfitmg0_freq1_combo_PROC
      r2267_dfitmg0_freq1 = {REG_WIDTH {1'b0}};
      r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] = ff_regb_freq1_ch0_dfi_tphy_wrlat[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0];
      r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] = ff_regb_freq1_ch0_dfi_tphy_wrdata[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0];
      r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] = ff_regb_freq1_ch0_dfi_t_rddata_en[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0];
      r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] = ff_regb_freq1_ch0_dfi_t_ctrl_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG1
   //------------------------
   always_comb begin : r2268_dfitmg1_freq1_combo_PROC
      r2268_dfitmg1_freq1 = {REG_WIDTH {1'b0}};
      r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] = ff_regb_freq1_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0];
      r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] = ff_regb_freq1_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0];
      r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] = ff_regb_freq1_ch0_dfi_t_wrdata_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG2
   //------------------------
   always_comb begin : r2269_dfitmg2_freq1_combo_PROC
      r2269_dfitmg2_freq1 = {REG_WIDTH {1'b0}};
      r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] = cfgs_ff_regb_freq1_ch0_dfi_tphy_wrcslat[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0];
      r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] = cfgs_ff_regb_freq1_ch0_dfi_tphy_rdcslat[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0];
      r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] = cfgs_ff_regb_freq1_ch0_dfi_twck_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG4
   //------------------------
   always_comb begin : r2271_dfitmg4_freq1_combo_PROC
      r2271_dfitmg4_freq1 = {REG_WIDTH {1'b0}};
      r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] = cfgs_ff_regb_freq1_ch0_dfi_twck_dis[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0];
      r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] = cfgs_ff_regb_freq1_ch0_dfi_twck_en_fs[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0];
      r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] = cfgs_ff_regb_freq1_ch0_dfi_twck_en_wr[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0];
      r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] = cfgs_ff_regb_freq1_ch0_dfi_twck_en_rd[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG5
   //------------------------
   always_comb begin : r2272_dfitmg5_freq1_combo_PROC
      r2272_dfitmg5_freq1 = {REG_WIDTH {1'b0}};
      r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] = cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0];
      r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] = cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_cs[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0];
      r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] = cfgs_ff_regb_freq1_ch0_dfi_twck_toggle[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0];
      r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] = cfgs_ff_regb_freq1_ch0_dfi_twck_fast_toggle[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG6
   //------------------------
   always_comb begin : r2273_dfitmg6_freq1_combo_PROC
      r2273_dfitmg6_freq1 = {REG_WIDTH {1'b0}};
      r2273_dfitmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] = cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0];
      r2273_dfitmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] = cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd_en;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG1
   //------------------------
   always_comb begin : r2275_dfiupdtmg1_freq1_combo_PROC
      r2275_dfiupdtmg1_freq1 = {REG_WIDTH {1'b0}};
      r2275_dfiupdtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] = cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0];
      r2275_dfiupdtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] = cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG2
   //------------------------
   always_comb begin : r2276_dfiupdtmg2_freq1_combo_PROC
      r2276_dfiupdtmg2_freq1 = {REG_WIDTH {1'b0}};
      r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] = ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0];
      r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] = ff_regb_freq1_ch0_ctrlupd_after_dqsosc;
      r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] = ff_regb_freq1_ch0_ppt2_override;
      r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_EN] = ff_regb_freq1_ch0_ppt2_en;
      r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] = ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG3
   //------------------------
   always_comb begin : r2277_dfiupdtmg3_freq1_combo_PROC
      r2277_dfiupdtmg3_freq1 = {REG_WIDTH {1'b0}};
      r2277_dfiupdtmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] = cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG0
   //------------------------
   always_comb begin : r2278_rfshset1tmg0_freq1_combo_PROC
      r2278_rfshset1tmg0_freq1 = {REG_WIDTH {1'b0}};
      r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] = ff_regb_freq1_ch0_t_refi_x1_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0];
      r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] = ff_regb_freq1_ch0_refresh_to_x1_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0];
      r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] = ff_regb_freq1_ch0_refresh_margin[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0];
      r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] = ff_regb_freq1_ch0_refresh_to_x1_sel;
      r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] = ff_regb_freq1_ch0_t_refi_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG1
   //------------------------
   always_comb begin : r2279_rfshset1tmg1_freq1_combo_PROC
      r2279_rfshset1tmg1_freq1 = {REG_WIDTH {1'b0}};
      r2279_rfshset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] = ff_regb_freq1_ch0_t_rfc_min[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0];
      r2279_rfshset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] = ff_regb_freq1_ch0_t_rfc_min_ab[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG2
   //------------------------
   always_comb begin : r2280_rfshset1tmg2_freq1_combo_PROC
      r2280_rfshset1tmg2_freq1 = {REG_WIDTH {1'b0}};
      r2280_rfshset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] = ff_regb_freq1_ch0_t_pbr2pbr[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0];
      r2280_rfshset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] = ff_regb_freq1_ch0_t_pbr2act[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG3
   //------------------------
   always_comb begin : r2281_rfshset1tmg3_freq1_combo_PROC
      r2281_rfshset1tmg3_freq1 = {REG_WIDTH {1'b0}};
      r2281_rfshset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] = ff_regb_freq1_ch0_refresh_to_ab_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG4
   //------------------------
   always_comb begin : r2282_rfshset1tmg4_freq1_combo_PROC
      r2282_rfshset1tmg4_freq1 = {REG_WIDTH {1'b0}};
      r2282_rfshset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] = ff_regb_freq1_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0];
      r2282_rfshset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] = ff_regb_freq1_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RFMSET1TMG0
   //------------------------
   always_comb begin : r2292_rfmset1tmg0_freq1_combo_PROC
      r2292_rfmset1tmg0_freq1 = {REG_WIDTH {1'b0}};
      r2292_rfmset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB] = ff_regb_freq1_ch0_t_rfmpb[(`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG0
   //------------------------
   always_comb begin : r2303_zqset1tmg0_freq1_combo_PROC
      r2303_zqset1tmg0_freq1 = {REG_WIDTH {1'b0}};
      r2303_zqset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] = ff_regb_freq1_ch0_t_zq_long_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0];
      r2303_zqset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] = ff_regb_freq1_ch0_t_zq_short_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG1
   //------------------------
   always_comb begin : r2304_zqset1tmg1_freq1_combo_PROC
      r2304_zqset1tmg1_freq1 = {REG_WIDTH {1'b0}};
      r2304_zqset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] = cfgs_ff_regb_freq1_ch0_t_zq_short_interval_x1024[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0];
      r2304_zqset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] = cfgs_ff_regb_freq1_ch0_t_zq_reset_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG2
   //------------------------
   always_comb begin : r2305_zqset1tmg2_freq1_combo_PROC
      r2305_zqset1tmg2_freq1 = {REG_WIDTH {1'b0}};
      r2305_zqset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] = ff_regb_freq1_ch0_t_zq_stop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DQSOSCCTL0
   //------------------------
   always_comb begin : r2314_dqsoscctl0_freq1_combo_PROC
      r2314_dqsoscctl0_freq1 = {REG_WIDTH {1'b0}};
      r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] = ff_regb_freq1_ch0_dqsosc_enable;
      r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] = ff_regb_freq1_ch0_dqsosc_interval_unit;
      r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] = ff_regb_freq1_ch0_dqsosc_interval[(`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEINT
   //------------------------
   always_comb begin : r2315_derateint_freq1_combo_PROC
      r2315_derateint_freq1 = {REG_WIDTH {1'b0}};
      r2315_derateint_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] = cfgs_ff_regb_freq1_ch0_mr4_read_interval[(`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL0
   //------------------------
   always_comb begin : r2316_derateval0_freq1_combo_PROC
      r2316_derateval0_freq1 = {REG_WIDTH {1'b0}};
      r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] = ff_regb_freq1_ch0_derated_t_rrd[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0];
      r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP] = ff_regb_freq1_ch0_derated_t_rp[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0];
      r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] = ff_regb_freq1_ch0_derated_t_ras_min[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0];
      r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] = ff_regb_freq1_ch0_derated_t_rcd[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL1
   //------------------------
   always_comb begin : r2317_derateval1_freq1_combo_PROC
      r2317_derateval1_freq1 = {REG_WIDTH {1'b0}};
      r2317_derateval1_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC] = ff_regb_freq1_ch0_derated_t_rc[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0];
      r2317_derateval1_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] = ff_regb_freq1_ch0_derated_t_rcd_write[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.HWLPTMG0
   //------------------------
   always_comb begin : r2318_hwlptmg0_freq1_combo_PROC
      r2318_hwlptmg0_freq1 = {REG_WIDTH {1'b0}};
      r2318_hwlptmg0_freq1[`REGB_FREQ1_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] = cfgs_ff_regb_freq1_ch0_hw_lp_idle_x32[(`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DVFSCTL0
   //------------------------
   always_comb begin : r2319_dvfsctl0_freq1_combo_PROC
      r2319_dvfsctl0_freq1 = {REG_WIDTH {1'b0}};
      r2319_dvfsctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ1_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] = cfgs_ff_regb_freq1_ch0_dvfsq_enable;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.SCHEDTMG0
   //------------------------
   always_comb begin : r2320_schedtmg0_freq1_combo_PROC
      r2320_schedtmg0_freq1 = {REG_WIDTH {1'b0}};
      r2320_schedtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] = cfgs_ff_regb_freq1_ch0_pageclose_timer[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0];
      r2320_schedtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] = cfgs_ff_regb_freq1_ch0_rdwr_idle_gap[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFHPR1
   //------------------------
   always_comb begin : r2321_perfhpr1_freq1_combo_PROC
      r2321_perfhpr1_freq1 = {REG_WIDTH {1'b0}};
      r2321_perfhpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] = cfgs_ff_regb_freq1_ch0_hpr_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0];
      r2321_perfhpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq1_ch0_hpr_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFLPR1
   //------------------------
   always_comb begin : r2322_perflpr1_freq1_combo_PROC
      r2322_perflpr1_freq1 = {REG_WIDTH {1'b0}};
      r2322_perflpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] = cfgs_ff_regb_freq1_ch0_lpr_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0];
      r2322_perflpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq1_ch0_lpr_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFWR1
   //------------------------
   always_comb begin : r2323_perfwr1_freq1_combo_PROC
      r2323_perfwr1_freq1 = {REG_WIDTH {1'b0}};
      r2323_perfwr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE] = cfgs_ff_regb_freq1_ch0_w_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0];
      r2323_perfwr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] = cfgs_ff_regb_freq1_ch0_w_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.TMGCFG
   //------------------------
   always_comb begin : r2324_tmgcfg_freq1_combo_PROC
      r2324_tmgcfg_freq1 = {REG_WIDTH {1'b0}};
      r2324_tmgcfg_freq1[`REGB_FREQ1_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ1_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] = ff_regb_freq1_ch0_frequency_ratio;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG0
   //------------------------
   always_comb begin : r2325_ranktmg0_freq1_combo_PROC
      r2325_ranktmg0_freq1 = {REG_WIDTH {1'b0}};
      r2325_ranktmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] = cfgs_ff_regb_freq1_ch0_diff_rank_rd_gap[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0];
      r2325_ranktmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] = cfgs_ff_regb_freq1_ch0_diff_rank_wr_gap[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG1
   //------------------------
   always_comb begin : r2326_ranktmg1_freq1_combo_PROC
      r2326_ranktmg1_freq1 = {REG_WIDTH {1'b0}};
      r2326_ranktmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR] = cfgs_ff_regb_freq1_ch0_wr2rd_dr[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0];
      r2326_ranktmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR] = cfgs_ff_regb_freq1_ch0_rd2wr_dr[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.PWRTMG
   //------------------------
   always_comb begin : r2327_pwrtmg_freq1_combo_PROC
      r2327_pwrtmg_freq1 = {REG_WIDTH {1'b0}};
      r2327_pwrtmg_freq1[`REGB_FREQ1_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] = cfgs_ff_regb_freq1_ch0_powerdown_to_x32[(`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0];
      r2327_pwrtmg_freq1[`REGB_FREQ1_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32] = cfgs_ff_regb_freq1_ch0_selfref_to_x32[(`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG0
   //------------------------
   always_comb begin : r2333_ddr4pprtmg0_freq1_combo_PROC
      r2333_ddr4pprtmg0_freq1 = {REG_WIDTH {1'b0}};
      r2333_ddr4pprtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] = cfgs_ff_regb_freq1_ch0_t_pgm_x1_x1024[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0];
      r2333_ddr4pprtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] = cfgs_ff_regb_freq1_ch0_t_pgm_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG1
   //------------------------
   always_comb begin : r2334_ddr4pprtmg1_freq1_combo_PROC
      r2334_ddr4pprtmg1_freq1 = {REG_WIDTH {1'b0}};
      r2334_ddr4pprtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] = cfgs_ff_regb_freq1_ch0_t_pgmpst_x32[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0];
      r2334_ddr4pprtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] = cfgs_ff_regb_freq1_ch0_t_pgm_exit[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ1_CH0.LNKECCCTL0
   //------------------------
   always_comb begin : r2335_lnkeccctl0_freq1_combo_PROC
      r2335_lnkeccctl0_freq1 = {REG_WIDTH {1'b0}};
      r2335_lnkeccctl0_freq1[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ1_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] = ff_regb_freq1_ch0_wr_link_ecc_enable;
      r2335_lnkeccctl0_freq1[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ1_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] = ff_regb_freq1_ch0_rd_link_ecc_enable;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG0
   //------------------------
   always_comb begin : r2469_dramset1tmg0_freq2_combo_PROC
      r2469_dramset1tmg0_freq2 = {REG_WIDTH {1'b0}};
      r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] = cfgs_ff_regb_freq2_ch0_t_ras_min[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0];
      r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] = cfgs_ff_regb_freq2_ch0_t_ras_max[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0];
      r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW] = cfgs_ff_regb_freq2_ch0_t_faw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0];
      r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE] = cfgs_ff_regb_freq2_ch0_wr2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG1
   //------------------------
   always_comb begin : r2470_dramset1tmg1_freq2_combo_PROC
      r2470_dramset1tmg1_freq2 = {REG_WIDTH {1'b0}};
      r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC] = cfgs_ff_regb_freq2_ch0_t_rc[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0];
      r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE] = cfgs_ff_regb_freq2_ch0_rd2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0];
      r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP] = cfgs_ff_regb_freq2_ch0_t_xp[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0];
      r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] = cfgs_ff_regb_freq2_ch0_t_rcd_write[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG2
   //------------------------
   always_comb begin : r2471_dramset1tmg2_freq2_combo_PROC
      r2471_dramset1tmg2_freq2 = {REG_WIDTH {1'b0}};
      r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD] = cfgs_ff_regb_freq2_ch0_wr2rd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0];
      r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR] = cfgs_ff_regb_freq2_ch0_rd2wr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0];
      r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] = cfgs_ff_regb_freq2_ch0_read_latency[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0];
      r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] = cfgs_ff_regb_freq2_ch0_write_latency[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG3
   //------------------------
   always_comb begin : r2472_dramset1tmg3_freq2_combo_PROC
      r2472_dramset1tmg3_freq2 = {REG_WIDTH {1'b0}};
      r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR] = cfgs_ff_regb_freq2_ch0_wr2mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0];
      r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR] = cfgs_ff_regb_freq2_ch0_rd2mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0];
      r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR] = cfgs_ff_regb_freq2_ch0_t_mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG4
   //------------------------
   always_comb begin : r2473_dramset1tmg4_freq2_combo_PROC
      r2473_dramset1tmg4_freq2 = {REG_WIDTH {1'b0}};
      r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP] = cfgs_ff_regb_freq2_ch0_t_rp[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0];
      r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD] = cfgs_ff_regb_freq2_ch0_t_rrd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0];
      r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD] = cfgs_ff_regb_freq2_ch0_t_ccd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0];
      r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD] = cfgs_ff_regb_freq2_ch0_t_rcd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG5
   //------------------------
   always_comb begin : r2474_dramset1tmg5_freq2_combo_PROC
      r2474_dramset1tmg5_freq2 = {REG_WIDTH {1'b0}};
      r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE] = ff_regb_freq2_ch0_t_cke[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0];
      r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR] = ff_regb_freq2_ch0_t_ckesr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0];
      r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] = ff_regb_freq2_ch0_t_cksre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0];
      r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] = ff_regb_freq2_ch0_t_cksrx[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG6
   //------------------------
   always_comb begin : r2475_dramset1tmg6_freq2_combo_PROC
      r2475_dramset1tmg6_freq2 = {REG_WIDTH {1'b0}};
      r2475_dramset1tmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] = cfgs_ff_regb_freq2_ch0_t_ckcsx[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG7
   //------------------------
   always_comb begin : r2476_dramset1tmg7_freq2_combo_PROC
      r2476_dramset1tmg7_freq2 = {REG_WIDTH {1'b0}};
      r2476_dramset1tmg7_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH] = ff_regb_freq2_ch0_t_csh[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG9
   //------------------------
   always_comb begin : r2478_dramset1tmg9_freq2_combo_PROC
      r2478_dramset1tmg9_freq2 = {REG_WIDTH {1'b0}};
      r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] = cfgs_ff_regb_freq2_ch0_wr2rd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0];
      r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] = cfgs_ff_regb_freq2_ch0_t_rrd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0];
      r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] = cfgs_ff_regb_freq2_ch0_t_ccd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG12
   //------------------------
   always_comb begin : r2481_dramset1tmg12_freq2_combo_PROC
      r2481_dramset1tmg12_freq2 = {REG_WIDTH {1'b0}};
      r2481_dramset1tmg12_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] = cfgs_ff_regb_freq2_ch0_t_cmdcke[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG13
   //------------------------
   always_comb begin : r2482_dramset1tmg13_freq2_combo_PROC
      r2482_dramset1tmg13_freq2 = {REG_WIDTH {1'b0}};
      r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD] = cfgs_ff_regb_freq2_ch0_t_ppd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0];
      r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] = cfgs_ff_regb_freq2_ch0_t_ccd_mw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0];
      r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] = cfgs_ff_regb_freq2_ch0_odtloff[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG14
   //------------------------
   always_comb begin : r2483_dramset1tmg14_freq2_combo_PROC
      r2483_dramset1tmg14_freq2 = {REG_WIDTH {1'b0}};
      r2483_dramset1tmg14_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR] = cfgs_ff_regb_freq2_ch0_t_xsr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0];
      r2483_dramset1tmg14_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO] = cfgs_ff_regb_freq2_ch0_t_osco[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG17
   //------------------------
   always_comb begin : r2486_dramset1tmg17_freq2_combo_PROC
      r2486_dramset1tmg17_freq2 = {REG_WIDTH {1'b0}};
      r2486_dramset1tmg17_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] = cfgs_ff_regb_freq2_ch0_t_vrcg_disable[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0];
      r2486_dramset1tmg17_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] = cfgs_ff_regb_freq2_ch0_t_vrcg_enable[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG23
   //------------------------
   always_comb begin : r2491_dramset1tmg23_freq2_combo_PROC
      r2491_dramset1tmg23_freq2 = {REG_WIDTH {1'b0}};
      r2491_dramset1tmg23_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN] = ff_regb_freq2_ch0_t_pdn[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0];
      r2491_dramset1tmg23_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] = ff_regb_freq2_ch0_t_xsr_dsm_x1024[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG24
   //------------------------
   always_comb begin : r2492_dramset1tmg24_freq2_combo_PROC
      r2492_dramset1tmg24_freq2 = {REG_WIDTH {1'b0}};
      r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] = cfgs_ff_regb_freq2_ch0_max_wr_sync[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0];
      r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] = cfgs_ff_regb_freq2_ch0_max_rd_sync[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0];
      r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] = cfgs_ff_regb_freq2_ch0_rd2wr_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0];
      r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] = cfgs_ff_regb_freq2_ch0_bank_org[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG25
   //------------------------
   always_comb begin : r2493_dramset1tmg25_freq2_combo_PROC
      r2493_dramset1tmg25_freq2 = {REG_WIDTH {1'b0}};
      r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] = cfgs_ff_regb_freq2_ch0_rda2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0];
      r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] = cfgs_ff_regb_freq2_ch0_wra2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0];
      r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] = cfgs_ff_regb_freq2_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG30
   //------------------------
   always_comb begin : r2498_dramset1tmg30_freq2_combo_PROC
      r2498_dramset1tmg30_freq2 = {REG_WIDTH {1'b0}};
      r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD] = ff_regb_freq2_ch0_mrr2rd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0];
      r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR] = ff_regb_freq2_ch0_mrr2wr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0];
      r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] = ff_regb_freq2_ch0_mrr2mrw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG32
   //------------------------
   always_comb begin : r2500_dramset1tmg32_freq2_combo_PROC
      r2500_dramset1tmg32_freq2 = {REG_WIDTH {1'b0}};
      r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] = ff_regb_freq2_ch0_ws_fs2wck_sus[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0];
      r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] = ff_regb_freq2_ch0_t_wcksus[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0];
      r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] = ff_regb_freq2_ch0_ws_off2ws_fs[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR0
   //------------------------
   always_comb begin : r2531_initmr0_freq2_combo_PROC
      r2531_initmr0_freq2 = {REG_WIDTH {1'b0}};
      r2531_initmr0_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ2_CH0_SIZE_INITMR0_EMR] = cfgs_ff_regb_freq2_ch0_emr[(`REGB_FREQ2_CH0_SIZE_INITMR0_EMR) -1:0];
      r2531_initmr0_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ2_CH0_SIZE_INITMR0_MR] = cfgs_ff_regb_freq2_ch0_mr[(`REGB_FREQ2_CH0_SIZE_INITMR0_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR1
   //------------------------
   always_comb begin : r2532_initmr1_freq2_combo_PROC
      r2532_initmr1_freq2 = {REG_WIDTH {1'b0}};
      r2532_initmr1_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3] = ff_regb_freq2_ch0_emr3[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3) -1:0];
      r2532_initmr1_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2] = ff_regb_freq2_ch0_emr2[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR2
   //------------------------
   always_comb begin : r2533_initmr2_freq2_combo_PROC
      r2533_initmr2_freq2 = {REG_WIDTH {1'b0}};
      r2533_initmr2_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ2_CH0_SIZE_INITMR2_MR5] = cfgs_ff_regb_freq2_ch0_mr5[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR5) -1:0];
      r2533_initmr2_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ2_CH0_SIZE_INITMR2_MR4] = cfgs_ff_regb_freq2_ch0_mr4[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR4) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR3
   //------------------------
   always_comb begin : r2534_initmr3_freq2_combo_PROC
      r2534_initmr3_freq2 = {REG_WIDTH {1'b0}};
      r2534_initmr3_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ2_CH0_SIZE_INITMR3_MR6] = cfgs_ff_regb_freq2_ch0_mr6[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR6) -1:0];
      r2534_initmr3_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ2_CH0_SIZE_INITMR3_MR22] = cfgs_ff_regb_freq2_ch0_mr22[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR22) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG0
   //------------------------
   always_comb begin : r2535_dfitmg0_freq2_combo_PROC
      r2535_dfitmg0_freq2 = {REG_WIDTH {1'b0}};
      r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] = ff_regb_freq2_ch0_dfi_tphy_wrlat[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0];
      r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] = ff_regb_freq2_ch0_dfi_tphy_wrdata[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0];
      r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] = ff_regb_freq2_ch0_dfi_t_rddata_en[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0];
      r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] = ff_regb_freq2_ch0_dfi_t_ctrl_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG1
   //------------------------
   always_comb begin : r2536_dfitmg1_freq2_combo_PROC
      r2536_dfitmg1_freq2 = {REG_WIDTH {1'b0}};
      r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] = ff_regb_freq2_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0];
      r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] = ff_regb_freq2_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0];
      r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] = ff_regb_freq2_ch0_dfi_t_wrdata_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG2
   //------------------------
   always_comb begin : r2537_dfitmg2_freq2_combo_PROC
      r2537_dfitmg2_freq2 = {REG_WIDTH {1'b0}};
      r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] = cfgs_ff_regb_freq2_ch0_dfi_tphy_wrcslat[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0];
      r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] = cfgs_ff_regb_freq2_ch0_dfi_tphy_rdcslat[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0];
      r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] = cfgs_ff_regb_freq2_ch0_dfi_twck_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG4
   //------------------------
   always_comb begin : r2539_dfitmg4_freq2_combo_PROC
      r2539_dfitmg4_freq2 = {REG_WIDTH {1'b0}};
      r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] = cfgs_ff_regb_freq2_ch0_dfi_twck_dis[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0];
      r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] = cfgs_ff_regb_freq2_ch0_dfi_twck_en_fs[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0];
      r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] = cfgs_ff_regb_freq2_ch0_dfi_twck_en_wr[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0];
      r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] = cfgs_ff_regb_freq2_ch0_dfi_twck_en_rd[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG5
   //------------------------
   always_comb begin : r2540_dfitmg5_freq2_combo_PROC
      r2540_dfitmg5_freq2 = {REG_WIDTH {1'b0}};
      r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] = cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0];
      r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] = cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_cs[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0];
      r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] = cfgs_ff_regb_freq2_ch0_dfi_twck_toggle[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0];
      r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] = cfgs_ff_regb_freq2_ch0_dfi_twck_fast_toggle[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG6
   //------------------------
   always_comb begin : r2541_dfitmg6_freq2_combo_PROC
      r2541_dfitmg6_freq2 = {REG_WIDTH {1'b0}};
      r2541_dfitmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] = cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0];
      r2541_dfitmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] = cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd_en;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG1
   //------------------------
   always_comb begin : r2543_dfiupdtmg1_freq2_combo_PROC
      r2543_dfiupdtmg1_freq2 = {REG_WIDTH {1'b0}};
      r2543_dfiupdtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] = cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0];
      r2543_dfiupdtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] = cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG2
   //------------------------
   always_comb begin : r2544_dfiupdtmg2_freq2_combo_PROC
      r2544_dfiupdtmg2_freq2 = {REG_WIDTH {1'b0}};
      r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] = ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0];
      r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] = ff_regb_freq2_ch0_ctrlupd_after_dqsosc;
      r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] = ff_regb_freq2_ch0_ppt2_override;
      r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_EN] = ff_regb_freq2_ch0_ppt2_en;
      r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] = ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG3
   //------------------------
   always_comb begin : r2545_dfiupdtmg3_freq2_combo_PROC
      r2545_dfiupdtmg3_freq2 = {REG_WIDTH {1'b0}};
      r2545_dfiupdtmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] = cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG0
   //------------------------
   always_comb begin : r2546_rfshset1tmg0_freq2_combo_PROC
      r2546_rfshset1tmg0_freq2 = {REG_WIDTH {1'b0}};
      r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] = ff_regb_freq2_ch0_t_refi_x1_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0];
      r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] = ff_regb_freq2_ch0_refresh_to_x1_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0];
      r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] = ff_regb_freq2_ch0_refresh_margin[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0];
      r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] = ff_regb_freq2_ch0_refresh_to_x1_sel;
      r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] = ff_regb_freq2_ch0_t_refi_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG1
   //------------------------
   always_comb begin : r2547_rfshset1tmg1_freq2_combo_PROC
      r2547_rfshset1tmg1_freq2 = {REG_WIDTH {1'b0}};
      r2547_rfshset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] = ff_regb_freq2_ch0_t_rfc_min[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0];
      r2547_rfshset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] = ff_regb_freq2_ch0_t_rfc_min_ab[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG2
   //------------------------
   always_comb begin : r2548_rfshset1tmg2_freq2_combo_PROC
      r2548_rfshset1tmg2_freq2 = {REG_WIDTH {1'b0}};
      r2548_rfshset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] = ff_regb_freq2_ch0_t_pbr2pbr[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0];
      r2548_rfshset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] = ff_regb_freq2_ch0_t_pbr2act[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG3
   //------------------------
   always_comb begin : r2549_rfshset1tmg3_freq2_combo_PROC
      r2549_rfshset1tmg3_freq2 = {REG_WIDTH {1'b0}};
      r2549_rfshset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] = ff_regb_freq2_ch0_refresh_to_ab_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG4
   //------------------------
   always_comb begin : r2550_rfshset1tmg4_freq2_combo_PROC
      r2550_rfshset1tmg4_freq2 = {REG_WIDTH {1'b0}};
      r2550_rfshset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] = ff_regb_freq2_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0];
      r2550_rfshset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] = ff_regb_freq2_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RFMSET1TMG0
   //------------------------
   always_comb begin : r2560_rfmset1tmg0_freq2_combo_PROC
      r2560_rfmset1tmg0_freq2 = {REG_WIDTH {1'b0}};
      r2560_rfmset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB] = ff_regb_freq2_ch0_t_rfmpb[(`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG0
   //------------------------
   always_comb begin : r2571_zqset1tmg0_freq2_combo_PROC
      r2571_zqset1tmg0_freq2 = {REG_WIDTH {1'b0}};
      r2571_zqset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] = ff_regb_freq2_ch0_t_zq_long_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0];
      r2571_zqset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] = ff_regb_freq2_ch0_t_zq_short_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG1
   //------------------------
   always_comb begin : r2572_zqset1tmg1_freq2_combo_PROC
      r2572_zqset1tmg1_freq2 = {REG_WIDTH {1'b0}};
      r2572_zqset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] = cfgs_ff_regb_freq2_ch0_t_zq_short_interval_x1024[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0];
      r2572_zqset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] = cfgs_ff_regb_freq2_ch0_t_zq_reset_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG2
   //------------------------
   always_comb begin : r2573_zqset1tmg2_freq2_combo_PROC
      r2573_zqset1tmg2_freq2 = {REG_WIDTH {1'b0}};
      r2573_zqset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] = ff_regb_freq2_ch0_t_zq_stop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DQSOSCCTL0
   //------------------------
   always_comb begin : r2582_dqsoscctl0_freq2_combo_PROC
      r2582_dqsoscctl0_freq2 = {REG_WIDTH {1'b0}};
      r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] = ff_regb_freq2_ch0_dqsosc_enable;
      r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] = ff_regb_freq2_ch0_dqsosc_interval_unit;
      r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] = ff_regb_freq2_ch0_dqsosc_interval[(`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEINT
   //------------------------
   always_comb begin : r2583_derateint_freq2_combo_PROC
      r2583_derateint_freq2 = {REG_WIDTH {1'b0}};
      r2583_derateint_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] = cfgs_ff_regb_freq2_ch0_mr4_read_interval[(`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL0
   //------------------------
   always_comb begin : r2584_derateval0_freq2_combo_PROC
      r2584_derateval0_freq2 = {REG_WIDTH {1'b0}};
      r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] = ff_regb_freq2_ch0_derated_t_rrd[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0];
      r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP] = ff_regb_freq2_ch0_derated_t_rp[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0];
      r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] = ff_regb_freq2_ch0_derated_t_ras_min[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0];
      r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] = ff_regb_freq2_ch0_derated_t_rcd[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL1
   //------------------------
   always_comb begin : r2585_derateval1_freq2_combo_PROC
      r2585_derateval1_freq2 = {REG_WIDTH {1'b0}};
      r2585_derateval1_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC] = ff_regb_freq2_ch0_derated_t_rc[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0];
      r2585_derateval1_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] = ff_regb_freq2_ch0_derated_t_rcd_write[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.HWLPTMG0
   //------------------------
   always_comb begin : r2586_hwlptmg0_freq2_combo_PROC
      r2586_hwlptmg0_freq2 = {REG_WIDTH {1'b0}};
      r2586_hwlptmg0_freq2[`REGB_FREQ2_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] = cfgs_ff_regb_freq2_ch0_hw_lp_idle_x32[(`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DVFSCTL0
   //------------------------
   always_comb begin : r2587_dvfsctl0_freq2_combo_PROC
      r2587_dvfsctl0_freq2 = {REG_WIDTH {1'b0}};
      r2587_dvfsctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ2_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] = cfgs_ff_regb_freq2_ch0_dvfsq_enable;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.SCHEDTMG0
   //------------------------
   always_comb begin : r2588_schedtmg0_freq2_combo_PROC
      r2588_schedtmg0_freq2 = {REG_WIDTH {1'b0}};
      r2588_schedtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] = cfgs_ff_regb_freq2_ch0_pageclose_timer[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0];
      r2588_schedtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] = cfgs_ff_regb_freq2_ch0_rdwr_idle_gap[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFHPR1
   //------------------------
   always_comb begin : r2589_perfhpr1_freq2_combo_PROC
      r2589_perfhpr1_freq2 = {REG_WIDTH {1'b0}};
      r2589_perfhpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] = cfgs_ff_regb_freq2_ch0_hpr_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0];
      r2589_perfhpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq2_ch0_hpr_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFLPR1
   //------------------------
   always_comb begin : r2590_perflpr1_freq2_combo_PROC
      r2590_perflpr1_freq2 = {REG_WIDTH {1'b0}};
      r2590_perflpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] = cfgs_ff_regb_freq2_ch0_lpr_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0];
      r2590_perflpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq2_ch0_lpr_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFWR1
   //------------------------
   always_comb begin : r2591_perfwr1_freq2_combo_PROC
      r2591_perfwr1_freq2 = {REG_WIDTH {1'b0}};
      r2591_perfwr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE] = cfgs_ff_regb_freq2_ch0_w_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0];
      r2591_perfwr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] = cfgs_ff_regb_freq2_ch0_w_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.TMGCFG
   //------------------------
   always_comb begin : r2592_tmgcfg_freq2_combo_PROC
      r2592_tmgcfg_freq2 = {REG_WIDTH {1'b0}};
      r2592_tmgcfg_freq2[`REGB_FREQ2_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ2_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] = ff_regb_freq2_ch0_frequency_ratio;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG0
   //------------------------
   always_comb begin : r2593_ranktmg0_freq2_combo_PROC
      r2593_ranktmg0_freq2 = {REG_WIDTH {1'b0}};
      r2593_ranktmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] = cfgs_ff_regb_freq2_ch0_diff_rank_rd_gap[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0];
      r2593_ranktmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] = cfgs_ff_regb_freq2_ch0_diff_rank_wr_gap[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG1
   //------------------------
   always_comb begin : r2594_ranktmg1_freq2_combo_PROC
      r2594_ranktmg1_freq2 = {REG_WIDTH {1'b0}};
      r2594_ranktmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR] = cfgs_ff_regb_freq2_ch0_wr2rd_dr[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0];
      r2594_ranktmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR] = cfgs_ff_regb_freq2_ch0_rd2wr_dr[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.PWRTMG
   //------------------------
   always_comb begin : r2595_pwrtmg_freq2_combo_PROC
      r2595_pwrtmg_freq2 = {REG_WIDTH {1'b0}};
      r2595_pwrtmg_freq2[`REGB_FREQ2_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] = cfgs_ff_regb_freq2_ch0_powerdown_to_x32[(`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0];
      r2595_pwrtmg_freq2[`REGB_FREQ2_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32] = cfgs_ff_regb_freq2_ch0_selfref_to_x32[(`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG0
   //------------------------
   always_comb begin : r2601_ddr4pprtmg0_freq2_combo_PROC
      r2601_ddr4pprtmg0_freq2 = {REG_WIDTH {1'b0}};
      r2601_ddr4pprtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] = cfgs_ff_regb_freq2_ch0_t_pgm_x1_x1024[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0];
      r2601_ddr4pprtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] = cfgs_ff_regb_freq2_ch0_t_pgm_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG1
   //------------------------
   always_comb begin : r2602_ddr4pprtmg1_freq2_combo_PROC
      r2602_ddr4pprtmg1_freq2 = {REG_WIDTH {1'b0}};
      r2602_ddr4pprtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] = cfgs_ff_regb_freq2_ch0_t_pgmpst_x32[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0];
      r2602_ddr4pprtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] = cfgs_ff_regb_freq2_ch0_t_pgm_exit[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ2_CH0.LNKECCCTL0
   //------------------------
   always_comb begin : r2603_lnkeccctl0_freq2_combo_PROC
      r2603_lnkeccctl0_freq2 = {REG_WIDTH {1'b0}};
      r2603_lnkeccctl0_freq2[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ2_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] = ff_regb_freq2_ch0_wr_link_ecc_enable;
      r2603_lnkeccctl0_freq2[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ2_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] = ff_regb_freq2_ch0_rd_link_ecc_enable;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG0
   //------------------------
   always_comb begin : r2737_dramset1tmg0_freq3_combo_PROC
      r2737_dramset1tmg0_freq3 = {REG_WIDTH {1'b0}};
      r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] = cfgs_ff_regb_freq3_ch0_t_ras_min[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0];
      r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] = cfgs_ff_regb_freq3_ch0_t_ras_max[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0];
      r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW] = cfgs_ff_regb_freq3_ch0_t_faw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0];
      r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE] = cfgs_ff_regb_freq3_ch0_wr2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG1
   //------------------------
   always_comb begin : r2738_dramset1tmg1_freq3_combo_PROC
      r2738_dramset1tmg1_freq3 = {REG_WIDTH {1'b0}};
      r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC] = cfgs_ff_regb_freq3_ch0_t_rc[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0];
      r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE] = cfgs_ff_regb_freq3_ch0_rd2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0];
      r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP] = cfgs_ff_regb_freq3_ch0_t_xp[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0];
      r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] = cfgs_ff_regb_freq3_ch0_t_rcd_write[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG2
   //------------------------
   always_comb begin : r2739_dramset1tmg2_freq3_combo_PROC
      r2739_dramset1tmg2_freq3 = {REG_WIDTH {1'b0}};
      r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD] = cfgs_ff_regb_freq3_ch0_wr2rd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0];
      r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR] = cfgs_ff_regb_freq3_ch0_rd2wr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0];
      r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] = cfgs_ff_regb_freq3_ch0_read_latency[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0];
      r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] = cfgs_ff_regb_freq3_ch0_write_latency[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG3
   //------------------------
   always_comb begin : r2740_dramset1tmg3_freq3_combo_PROC
      r2740_dramset1tmg3_freq3 = {REG_WIDTH {1'b0}};
      r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR] = cfgs_ff_regb_freq3_ch0_wr2mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0];
      r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR] = cfgs_ff_regb_freq3_ch0_rd2mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0];
      r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR] = cfgs_ff_regb_freq3_ch0_t_mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG4
   //------------------------
   always_comb begin : r2741_dramset1tmg4_freq3_combo_PROC
      r2741_dramset1tmg4_freq3 = {REG_WIDTH {1'b0}};
      r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP] = cfgs_ff_regb_freq3_ch0_t_rp[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0];
      r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD] = cfgs_ff_regb_freq3_ch0_t_rrd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0];
      r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD] = cfgs_ff_regb_freq3_ch0_t_ccd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0];
      r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD] = cfgs_ff_regb_freq3_ch0_t_rcd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG5
   //------------------------
   always_comb begin : r2742_dramset1tmg5_freq3_combo_PROC
      r2742_dramset1tmg5_freq3 = {REG_WIDTH {1'b0}};
      r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE] = ff_regb_freq3_ch0_t_cke[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0];
      r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR] = ff_regb_freq3_ch0_t_ckesr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0];
      r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] = ff_regb_freq3_ch0_t_cksre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0];
      r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] = ff_regb_freq3_ch0_t_cksrx[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG6
   //------------------------
   always_comb begin : r2743_dramset1tmg6_freq3_combo_PROC
      r2743_dramset1tmg6_freq3 = {REG_WIDTH {1'b0}};
      r2743_dramset1tmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] = cfgs_ff_regb_freq3_ch0_t_ckcsx[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG7
   //------------------------
   always_comb begin : r2744_dramset1tmg7_freq3_combo_PROC
      r2744_dramset1tmg7_freq3 = {REG_WIDTH {1'b0}};
      r2744_dramset1tmg7_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH] = ff_regb_freq3_ch0_t_csh[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG9
   //------------------------
   always_comb begin : r2746_dramset1tmg9_freq3_combo_PROC
      r2746_dramset1tmg9_freq3 = {REG_WIDTH {1'b0}};
      r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] = cfgs_ff_regb_freq3_ch0_wr2rd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0];
      r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] = cfgs_ff_regb_freq3_ch0_t_rrd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0];
      r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] = cfgs_ff_regb_freq3_ch0_t_ccd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG12
   //------------------------
   always_comb begin : r2749_dramset1tmg12_freq3_combo_PROC
      r2749_dramset1tmg12_freq3 = {REG_WIDTH {1'b0}};
      r2749_dramset1tmg12_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] = cfgs_ff_regb_freq3_ch0_t_cmdcke[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG13
   //------------------------
   always_comb begin : r2750_dramset1tmg13_freq3_combo_PROC
      r2750_dramset1tmg13_freq3 = {REG_WIDTH {1'b0}};
      r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD] = cfgs_ff_regb_freq3_ch0_t_ppd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0];
      r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] = cfgs_ff_regb_freq3_ch0_t_ccd_mw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0];
      r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] = cfgs_ff_regb_freq3_ch0_odtloff[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG14
   //------------------------
   always_comb begin : r2751_dramset1tmg14_freq3_combo_PROC
      r2751_dramset1tmg14_freq3 = {REG_WIDTH {1'b0}};
      r2751_dramset1tmg14_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR] = cfgs_ff_regb_freq3_ch0_t_xsr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0];
      r2751_dramset1tmg14_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO] = cfgs_ff_regb_freq3_ch0_t_osco[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG17
   //------------------------
   always_comb begin : r2754_dramset1tmg17_freq3_combo_PROC
      r2754_dramset1tmg17_freq3 = {REG_WIDTH {1'b0}};
      r2754_dramset1tmg17_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] = cfgs_ff_regb_freq3_ch0_t_vrcg_disable[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0];
      r2754_dramset1tmg17_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] = cfgs_ff_regb_freq3_ch0_t_vrcg_enable[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG23
   //------------------------
   always_comb begin : r2759_dramset1tmg23_freq3_combo_PROC
      r2759_dramset1tmg23_freq3 = {REG_WIDTH {1'b0}};
      r2759_dramset1tmg23_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN] = ff_regb_freq3_ch0_t_pdn[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0];
      r2759_dramset1tmg23_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] = ff_regb_freq3_ch0_t_xsr_dsm_x1024[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG24
   //------------------------
   always_comb begin : r2760_dramset1tmg24_freq3_combo_PROC
      r2760_dramset1tmg24_freq3 = {REG_WIDTH {1'b0}};
      r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] = cfgs_ff_regb_freq3_ch0_max_wr_sync[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0];
      r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] = cfgs_ff_regb_freq3_ch0_max_rd_sync[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0];
      r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] = cfgs_ff_regb_freq3_ch0_rd2wr_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0];
      r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] = cfgs_ff_regb_freq3_ch0_bank_org[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG25
   //------------------------
   always_comb begin : r2761_dramset1tmg25_freq3_combo_PROC
      r2761_dramset1tmg25_freq3 = {REG_WIDTH {1'b0}};
      r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] = cfgs_ff_regb_freq3_ch0_rda2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0];
      r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] = cfgs_ff_regb_freq3_ch0_wra2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0];
      r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] = cfgs_ff_regb_freq3_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG30
   //------------------------
   always_comb begin : r2766_dramset1tmg30_freq3_combo_PROC
      r2766_dramset1tmg30_freq3 = {REG_WIDTH {1'b0}};
      r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD] = ff_regb_freq3_ch0_mrr2rd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0];
      r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR] = ff_regb_freq3_ch0_mrr2wr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0];
      r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] = ff_regb_freq3_ch0_mrr2mrw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG32
   //------------------------
   always_comb begin : r2768_dramset1tmg32_freq3_combo_PROC
      r2768_dramset1tmg32_freq3 = {REG_WIDTH {1'b0}};
      r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] = ff_regb_freq3_ch0_ws_fs2wck_sus[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0];
      r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] = ff_regb_freq3_ch0_t_wcksus[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0];
      r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] = ff_regb_freq3_ch0_ws_off2ws_fs[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR0
   //------------------------
   always_comb begin : r2799_initmr0_freq3_combo_PROC
      r2799_initmr0_freq3 = {REG_WIDTH {1'b0}};
      r2799_initmr0_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ3_CH0_SIZE_INITMR0_EMR] = cfgs_ff_regb_freq3_ch0_emr[(`REGB_FREQ3_CH0_SIZE_INITMR0_EMR) -1:0];
      r2799_initmr0_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ3_CH0_SIZE_INITMR0_MR] = cfgs_ff_regb_freq3_ch0_mr[(`REGB_FREQ3_CH0_SIZE_INITMR0_MR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR1
   //------------------------
   always_comb begin : r2800_initmr1_freq3_combo_PROC
      r2800_initmr1_freq3 = {REG_WIDTH {1'b0}};
      r2800_initmr1_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3] = ff_regb_freq3_ch0_emr3[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3) -1:0];
      r2800_initmr1_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2] = ff_regb_freq3_ch0_emr2[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR2
   //------------------------
   always_comb begin : r2801_initmr2_freq3_combo_PROC
      r2801_initmr2_freq3 = {REG_WIDTH {1'b0}};
      r2801_initmr2_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ3_CH0_SIZE_INITMR2_MR5] = cfgs_ff_regb_freq3_ch0_mr5[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR5) -1:0];
      r2801_initmr2_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ3_CH0_SIZE_INITMR2_MR4] = cfgs_ff_regb_freq3_ch0_mr4[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR4) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR3
   //------------------------
   always_comb begin : r2802_initmr3_freq3_combo_PROC
      r2802_initmr3_freq3 = {REG_WIDTH {1'b0}};
      r2802_initmr3_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ3_CH0_SIZE_INITMR3_MR6] = cfgs_ff_regb_freq3_ch0_mr6[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR6) -1:0];
      r2802_initmr3_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ3_CH0_SIZE_INITMR3_MR22] = cfgs_ff_regb_freq3_ch0_mr22[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR22) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG0
   //------------------------
   always_comb begin : r2803_dfitmg0_freq3_combo_PROC
      r2803_dfitmg0_freq3 = {REG_WIDTH {1'b0}};
      r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] = ff_regb_freq3_ch0_dfi_tphy_wrlat[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0];
      r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] = ff_regb_freq3_ch0_dfi_tphy_wrdata[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0];
      r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] = ff_regb_freq3_ch0_dfi_t_rddata_en[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0];
      r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] = ff_regb_freq3_ch0_dfi_t_ctrl_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG1
   //------------------------
   always_comb begin : r2804_dfitmg1_freq3_combo_PROC
      r2804_dfitmg1_freq3 = {REG_WIDTH {1'b0}};
      r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] = ff_regb_freq3_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0];
      r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] = ff_regb_freq3_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0];
      r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] = ff_regb_freq3_ch0_dfi_t_wrdata_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG2
   //------------------------
   always_comb begin : r2805_dfitmg2_freq3_combo_PROC
      r2805_dfitmg2_freq3 = {REG_WIDTH {1'b0}};
      r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] = cfgs_ff_regb_freq3_ch0_dfi_tphy_wrcslat[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0];
      r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] = cfgs_ff_regb_freq3_ch0_dfi_tphy_rdcslat[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0];
      r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] = cfgs_ff_regb_freq3_ch0_dfi_twck_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG4
   //------------------------
   always_comb begin : r2807_dfitmg4_freq3_combo_PROC
      r2807_dfitmg4_freq3 = {REG_WIDTH {1'b0}};
      r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] = cfgs_ff_regb_freq3_ch0_dfi_twck_dis[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0];
      r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] = cfgs_ff_regb_freq3_ch0_dfi_twck_en_fs[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0];
      r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] = cfgs_ff_regb_freq3_ch0_dfi_twck_en_wr[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0];
      r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] = cfgs_ff_regb_freq3_ch0_dfi_twck_en_rd[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG5
   //------------------------
   always_comb begin : r2808_dfitmg5_freq3_combo_PROC
      r2808_dfitmg5_freq3 = {REG_WIDTH {1'b0}};
      r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] = cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0];
      r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] = cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_cs[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0];
      r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] = cfgs_ff_regb_freq3_ch0_dfi_twck_toggle[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0];
      r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] = cfgs_ff_regb_freq3_ch0_dfi_twck_fast_toggle[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG6
   //------------------------
   always_comb begin : r2809_dfitmg6_freq3_combo_PROC
      r2809_dfitmg6_freq3 = {REG_WIDTH {1'b0}};
      r2809_dfitmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] = cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0];
      r2809_dfitmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] = cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd_en;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG1
   //------------------------
   always_comb begin : r2811_dfiupdtmg1_freq3_combo_PROC
      r2811_dfiupdtmg1_freq3 = {REG_WIDTH {1'b0}};
      r2811_dfiupdtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] = cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0];
      r2811_dfiupdtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] = cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG2
   //------------------------
   always_comb begin : r2812_dfiupdtmg2_freq3_combo_PROC
      r2812_dfiupdtmg2_freq3 = {REG_WIDTH {1'b0}};
      r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] = ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0];
      r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] = ff_regb_freq3_ch0_ctrlupd_after_dqsosc;
      r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] = ff_regb_freq3_ch0_ppt2_override;
      r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_EN] = ff_regb_freq3_ch0_ppt2_en;
      r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] = ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG3
   //------------------------
   always_comb begin : r2813_dfiupdtmg3_freq3_combo_PROC
      r2813_dfiupdtmg3_freq3 = {REG_WIDTH {1'b0}};
      r2813_dfiupdtmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] = cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG0
   //------------------------
   always_comb begin : r2814_rfshset1tmg0_freq3_combo_PROC
      r2814_rfshset1tmg0_freq3 = {REG_WIDTH {1'b0}};
      r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] = ff_regb_freq3_ch0_t_refi_x1_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0];
      r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] = ff_regb_freq3_ch0_refresh_to_x1_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0];
      r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] = ff_regb_freq3_ch0_refresh_margin[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0];
      r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] = ff_regb_freq3_ch0_refresh_to_x1_sel;
      r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] = ff_regb_freq3_ch0_t_refi_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG1
   //------------------------
   always_comb begin : r2815_rfshset1tmg1_freq3_combo_PROC
      r2815_rfshset1tmg1_freq3 = {REG_WIDTH {1'b0}};
      r2815_rfshset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] = ff_regb_freq3_ch0_t_rfc_min[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0];
      r2815_rfshset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] = ff_regb_freq3_ch0_t_rfc_min_ab[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG2
   //------------------------
   always_comb begin : r2816_rfshset1tmg2_freq3_combo_PROC
      r2816_rfshset1tmg2_freq3 = {REG_WIDTH {1'b0}};
      r2816_rfshset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] = ff_regb_freq3_ch0_t_pbr2pbr[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0];
      r2816_rfshset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] = ff_regb_freq3_ch0_t_pbr2act[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG3
   //------------------------
   always_comb begin : r2817_rfshset1tmg3_freq3_combo_PROC
      r2817_rfshset1tmg3_freq3 = {REG_WIDTH {1'b0}};
      r2817_rfshset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] = ff_regb_freq3_ch0_refresh_to_ab_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG4
   //------------------------
   always_comb begin : r2818_rfshset1tmg4_freq3_combo_PROC
      r2818_rfshset1tmg4_freq3 = {REG_WIDTH {1'b0}};
      r2818_rfshset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] = ff_regb_freq3_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0];
      r2818_rfshset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] = ff_regb_freq3_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RFMSET1TMG0
   //------------------------
   always_comb begin : r2828_rfmset1tmg0_freq3_combo_PROC
      r2828_rfmset1tmg0_freq3 = {REG_WIDTH {1'b0}};
      r2828_rfmset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB] = ff_regb_freq3_ch0_t_rfmpb[(`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG0
   //------------------------
   always_comb begin : r2839_zqset1tmg0_freq3_combo_PROC
      r2839_zqset1tmg0_freq3 = {REG_WIDTH {1'b0}};
      r2839_zqset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] = ff_regb_freq3_ch0_t_zq_long_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0];
      r2839_zqset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] = ff_regb_freq3_ch0_t_zq_short_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG1
   //------------------------
   always_comb begin : r2840_zqset1tmg1_freq3_combo_PROC
      r2840_zqset1tmg1_freq3 = {REG_WIDTH {1'b0}};
      r2840_zqset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] = cfgs_ff_regb_freq3_ch0_t_zq_short_interval_x1024[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0];
      r2840_zqset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] = cfgs_ff_regb_freq3_ch0_t_zq_reset_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG2
   //------------------------
   always_comb begin : r2841_zqset1tmg2_freq3_combo_PROC
      r2841_zqset1tmg2_freq3 = {REG_WIDTH {1'b0}};
      r2841_zqset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] = ff_regb_freq3_ch0_t_zq_stop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DQSOSCCTL0
   //------------------------
   always_comb begin : r2850_dqsoscctl0_freq3_combo_PROC
      r2850_dqsoscctl0_freq3 = {REG_WIDTH {1'b0}};
      r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] = ff_regb_freq3_ch0_dqsosc_enable;
      r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] = ff_regb_freq3_ch0_dqsosc_interval_unit;
      r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] = ff_regb_freq3_ch0_dqsosc_interval[(`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEINT
   //------------------------
   always_comb begin : r2851_derateint_freq3_combo_PROC
      r2851_derateint_freq3 = {REG_WIDTH {1'b0}};
      r2851_derateint_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] = cfgs_ff_regb_freq3_ch0_mr4_read_interval[(`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL0
   //------------------------
   always_comb begin : r2852_derateval0_freq3_combo_PROC
      r2852_derateval0_freq3 = {REG_WIDTH {1'b0}};
      r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] = ff_regb_freq3_ch0_derated_t_rrd[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0];
      r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP] = ff_regb_freq3_ch0_derated_t_rp[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0];
      r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] = ff_regb_freq3_ch0_derated_t_ras_min[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0];
      r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] = ff_regb_freq3_ch0_derated_t_rcd[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL1
   //------------------------
   always_comb begin : r2853_derateval1_freq3_combo_PROC
      r2853_derateval1_freq3 = {REG_WIDTH {1'b0}};
      r2853_derateval1_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC] = ff_regb_freq3_ch0_derated_t_rc[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0];
      r2853_derateval1_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] = ff_regb_freq3_ch0_derated_t_rcd_write[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.HWLPTMG0
   //------------------------
   always_comb begin : r2854_hwlptmg0_freq3_combo_PROC
      r2854_hwlptmg0_freq3 = {REG_WIDTH {1'b0}};
      r2854_hwlptmg0_freq3[`REGB_FREQ3_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] = cfgs_ff_regb_freq3_ch0_hw_lp_idle_x32[(`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DVFSCTL0
   //------------------------
   always_comb begin : r2855_dvfsctl0_freq3_combo_PROC
      r2855_dvfsctl0_freq3 = {REG_WIDTH {1'b0}};
      r2855_dvfsctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ3_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] = cfgs_ff_regb_freq3_ch0_dvfsq_enable;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.SCHEDTMG0
   //------------------------
   always_comb begin : r2856_schedtmg0_freq3_combo_PROC
      r2856_schedtmg0_freq3 = {REG_WIDTH {1'b0}};
      r2856_schedtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] = cfgs_ff_regb_freq3_ch0_pageclose_timer[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0];
      r2856_schedtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] = cfgs_ff_regb_freq3_ch0_rdwr_idle_gap[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFHPR1
   //------------------------
   always_comb begin : r2857_perfhpr1_freq3_combo_PROC
      r2857_perfhpr1_freq3 = {REG_WIDTH {1'b0}};
      r2857_perfhpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] = cfgs_ff_regb_freq3_ch0_hpr_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0];
      r2857_perfhpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq3_ch0_hpr_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFLPR1
   //------------------------
   always_comb begin : r2858_perflpr1_freq3_combo_PROC
      r2858_perflpr1_freq3 = {REG_WIDTH {1'b0}};
      r2858_perflpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] = cfgs_ff_regb_freq3_ch0_lpr_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0];
      r2858_perflpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] = cfgs_ff_regb_freq3_ch0_lpr_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFWR1
   //------------------------
   always_comb begin : r2859_perfwr1_freq3_combo_PROC
      r2859_perfwr1_freq3 = {REG_WIDTH {1'b0}};
      r2859_perfwr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE] = cfgs_ff_regb_freq3_ch0_w_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0];
      r2859_perfwr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] = cfgs_ff_regb_freq3_ch0_w_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.TMGCFG
   //------------------------
   always_comb begin : r2860_tmgcfg_freq3_combo_PROC
      r2860_tmgcfg_freq3 = {REG_WIDTH {1'b0}};
      r2860_tmgcfg_freq3[`REGB_FREQ3_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ3_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] = ff_regb_freq3_ch0_frequency_ratio;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG0
   //------------------------
   always_comb begin : r2861_ranktmg0_freq3_combo_PROC
      r2861_ranktmg0_freq3 = {REG_WIDTH {1'b0}};
      r2861_ranktmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] = cfgs_ff_regb_freq3_ch0_diff_rank_rd_gap[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0];
      r2861_ranktmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] = cfgs_ff_regb_freq3_ch0_diff_rank_wr_gap[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG1
   //------------------------
   always_comb begin : r2862_ranktmg1_freq3_combo_PROC
      r2862_ranktmg1_freq3 = {REG_WIDTH {1'b0}};
      r2862_ranktmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR] = cfgs_ff_regb_freq3_ch0_wr2rd_dr[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0];
      r2862_ranktmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR] = cfgs_ff_regb_freq3_ch0_rd2wr_dr[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.PWRTMG
   //------------------------
   always_comb begin : r2863_pwrtmg_freq3_combo_PROC
      r2863_pwrtmg_freq3 = {REG_WIDTH {1'b0}};
      r2863_pwrtmg_freq3[`REGB_FREQ3_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] = cfgs_ff_regb_freq3_ch0_powerdown_to_x32[(`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0];
      r2863_pwrtmg_freq3[`REGB_FREQ3_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32] = cfgs_ff_regb_freq3_ch0_selfref_to_x32[(`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG0
   //------------------------
   always_comb begin : r2869_ddr4pprtmg0_freq3_combo_PROC
      r2869_ddr4pprtmg0_freq3 = {REG_WIDTH {1'b0}};
      r2869_ddr4pprtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] = cfgs_ff_regb_freq3_ch0_t_pgm_x1_x1024[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0];
      r2869_ddr4pprtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] = cfgs_ff_regb_freq3_ch0_t_pgm_x1_sel;
   end
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG1
   //------------------------
   always_comb begin : r2870_ddr4pprtmg1_freq3_combo_PROC
      r2870_ddr4pprtmg1_freq3 = {REG_WIDTH {1'b0}};
      r2870_ddr4pprtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] = cfgs_ff_regb_freq3_ch0_t_pgmpst_x32[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0];
      r2870_ddr4pprtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] = cfgs_ff_regb_freq3_ch0_t_pgm_exit[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0];
   end
   //------------------------
   // Register REGB_FREQ3_CH0.LNKECCCTL0
   //------------------------
   always_comb begin : r2871_lnkeccctl0_freq3_combo_PROC
      r2871_lnkeccctl0_freq3 = {REG_WIDTH {1'b0}};
      r2871_lnkeccctl0_freq3[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ3_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] = ff_regb_freq3_ch0_wr_link_ecc_enable;
      r2871_lnkeccctl0_freq3[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ3_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] = ff_regb_freq3_ch0_rd_link_ecc_enable;
   end



   always @ (posedge pclk or negedge presetn) begin : sample_pclk_wdata_PROC
      if (~presetn) begin
         apb_data_r  <= {APB_DW{1'b0}};
      end else begin
         apb_data_r  <= pwdata;
      end
   end

   always_comb begin : expand_data_PROC
      apb_data_expanded={REG_WIDTH{1'b0}};
      apb_data_expanded[REG_WIDTH-1:0]=apb_data_r[REG_WIDTH-1:0];
   end
   

   always @(posedge pclk or negedge presetn) begin : sample_pclk_regfields_PROC
      if (~presetn) begin
         ff_regb_ddrc_ch0_lpddr4 <= 'h0;
         ff_regb_ddrc_ch0_lpddr5 <= 'h0;
         ff_regb_ddrc_ch0_lpddr5x <= 'h0;
         ff_regb_ddrc_ch0_data_bus_width <= 'h0;
         ff_regb_ddrc_ch0_burst_rdwr <= 'h4;
         ff_regb_ddrc_ch0_active_ranks <= (`MEMC_NUM_RANKS==4) ? 'hF :((`MEMC_NUM_RANKS==2) ? 'h3 : 'h1);
         ff_regb_ddrc_ch0_target_frequency <= 'h0;
         ff_regb_ddrc_ch0_wck_on <= 'h0;
         ff_regb_ddrc_ch0_wck_suspend_en <= 'h0;
         ff_regb_ddrc_ch0_ws_off_en <= 'h1;
         ff_regb_ddrc_ch0_mr_type <= 'h0;
         ff_regb_ddrc_ch0_sw_init_int <= 'h0;
         ff_regb_ddrc_ch0_mr_rank <= (`MEMC_NUM_RANKS==4) ? 'hF :((`MEMC_NUM_RANKS==2) ? 'h3 : 'h1);
         ff_regb_ddrc_ch0_mr_addr <= 'h0;
         ff_regb_ddrc_ch0_mrr_done_clr <= 'h0;
         ff_regb_ddrc_ch0_dis_mrrw_trfc <= 'h0;
         ff_regb_ddrc_ch0_ppr_en <= 'h0;
         ff_regb_ddrc_ch0_ppr_pgmpst_en <= 'h0;
         ff_regb_ddrc_ch0_mr_wr_todo  <= 1'b0;
         ff_regb_ddrc_ch0_mr_wr_saved <= 1'b0;
         ff_regb_ddrc_ch0_mr_wr <= 'h0;
         ff_regb_ddrc_ch0_mr_data <= 'h0;
         ff_regb_ddrc_ch0_derate_enable <= 'h0;
         ff_regb_ddrc_ch0_lpddr4_refresh_mode <= 'h0;
         ff_regb_ddrc_ch0_derate_mr4_pause_fc <= 'h0;
         ff_regb_ddrc_ch0_dis_trefi_x6x8 <= 'h0;
         ff_regb_ddrc_ch0_dis_trefi_x0125 <= 'h0;
         ff_regb_ddrc_ch0_use_slow_rm_in_low_temp <= 'h1;
         ff_regb_ddrc_ch0_active_derate_byte_rank0 <= 'h0;
         ff_regb_ddrc_ch0_active_derate_byte_rank1 <= 'h0;
         cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_en <= 'h1;
         cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr <= 'h0;
         cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force <= 'h0;
         ff_regb_ddrc_ch0_derate_mr4_tuf_dis <= 'h0;
         ff_regb_ddrc_ch0_dbg_mr4_rank_sel <= 'h0;
         ff_regb_ddrc_ch0_selfref_en <= 'h0;
         ff_regb_ddrc_ch0_powerdown_en <= 'h0;
         ff_regb_ddrc_ch0_en_dfi_dram_clk_disable <= 'h0;
         ff_regb_ddrc_ch0_selfref_sw <= 'h0;
         ff_regb_ddrc_ch0_stay_in_selfref <= 'h0;
         ff_regb_ddrc_ch0_dis_cam_drain_selfref <= 'h0;
         ff_regb_ddrc_ch0_lpddr4_sr_allowed <= 'h0;
         ff_regb_ddrc_ch0_dsm_en <= 'h0;
         ff_regb_ddrc_ch0_hw_lp_en <= 'h1;
         ff_regb_ddrc_ch0_hw_lp_exit_idle_en <= 'h1;
         ff_regb_ddrc_ch0_bsm_clk_on <= 'h3f;
         ff_regb_ddrc_ch0_refresh_burst <= 'h0;
         ff_regb_ddrc_ch0_auto_refab_en <= 'h0;
         ff_regb_ddrc_ch0_per_bank_refresh <= 'h0;
         ff_regb_ddrc_ch0_per_bank_refresh_opt_en <= 'h0;
         ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en <= 'h0;
         ff_regb_ddrc_ch0_dis_auto_refresh <= 'h0;
         ff_regb_ddrc_ch0_refresh_update_level <= 'h0;
         ff_regb_ddrc_ch0_rfm_en <= 'h0;
         ff_regb_ddrc_ch0_rfmsbc <= 'h0;
         ff_regb_ddrc_ch0_raaimt <= 'h1;
         ff_regb_ddrc_ch0_raamult <= 'h0;
         ff_regb_ddrc_ch0_raadec <= 'h0;
         ff_regb_ddrc_ch0_rfmth_rm_thr <= 'ha;
         ff_regb_ddrc_ch0_init_raa_cnt <= 'h0;
         ff_regb_ddrc_ch0_dbg_raa_rank <= 'h0;
         ff_regb_ddrc_ch0_dbg_raa_bg_bank <= 'h0;
         ff_regb_ddrc_ch0_zq_resistor_shared <= 'h0;
         ff_regb_ddrc_ch0_dis_auto_zq <= 'h0;
         ff_regb_ddrc_ch0_zq_reset_todo  <= 1'b0;
         ff_regb_ddrc_ch0_zq_reset_saved <= 1'b0;
         ff_regb_ddrc_ch0_zq_reset <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl_hwffc <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dqsosc_runtime <= 'h40;
         cfgs_ff_regb_ddrc_ch0_wck2dqo_runtime <= 'h40;
         cfgs_ff_regb_ddrc_ch0_dis_dqsosc_srx <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_opt_wrecc_collision_flush <= 'h0;
         cfgs_ff_regb_ddrc_ch0_prefer_write <= 'h0;
         cfgs_ff_regb_ddrc_ch0_pageclose <= 'h1;
         cfgs_ff_regb_ddrc_ch0_opt_wrcam_fill_level <= 'h1;
         cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_act <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_pre <= 'h0;
         cfgs_ff_regb_ddrc_ch0_autopre_rmw <= 'h0;
         cfgs_ff_regb_ddrc_ch0_lpr_num_entries <= $unsigned(`MEMC_NO_OF_ENTRY/2);
         cfgs_ff_regb_ddrc_ch0_lpddr4_opt_act_timing <= 'h0;
         cfgs_ff_regb_ddrc_ch0_lpddr5_opt_act_timing <= 'h1;
         cfgs_ff_regb_ddrc_ch0_w_starve_free_running <= 'h0;
         cfgs_ff_regb_ddrc_ch0_opt_act_lat <= 'h0;
         cfgs_ff_regb_ddrc_ch0_prefer_read <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_speculative_act <= 'h0;
         cfgs_ff_regb_ddrc_ch0_opt_vprw_sch <= 'h1;
         cfgs_ff_regb_ddrc_ch0_delay_switch_write <= 'h2;
         cfgs_ff_regb_ddrc_ch0_visible_window_limit_wr <= 'h0;
         cfgs_ff_regb_ddrc_ch0_visible_window_limit_rd <= 'h0;
         cfgs_ff_regb_ddrc_ch0_page_hit_limit_wr <= 'h0;
         cfgs_ff_regb_ddrc_ch0_page_hit_limit_rd <= 'h0;
         cfgs_ff_regb_ddrc_ch0_opt_hit_gt_hpr <= 'h0;
         cfgs_ff_regb_ddrc_ch0_wrcam_lowthresh <= 'h8;
         cfgs_ff_regb_ddrc_ch0_wrcam_highthresh <= 'h2;
         cfgs_ff_regb_ddrc_ch0_wr_pghit_num_thresh <= 'h4;
         cfgs_ff_regb_ddrc_ch0_rd_pghit_num_thresh <= 'h4;
         cfgs_ff_regb_ddrc_ch0_rd_act_idle_gap <= 'h10;
         cfgs_ff_regb_ddrc_ch0_wr_act_idle_gap <= 'h8;
         cfgs_ff_regb_ddrc_ch0_rd_page_exp_cycles <= 'h40;
         cfgs_ff_regb_ddrc_ch0_wr_page_exp_cycles <= 'h8;
         cfgs_ff_regb_ddrc_ch0_wrecc_cam_lowthresh <= 'h4;
         cfgs_ff_regb_ddrc_ch0_wrecc_cam_highthresh <= 'h2;
         cfgs_ff_regb_ddrc_ch0_dis_opt_loaded_wrecc_cam_fill_level <= 'h1;
         cfgs_ff_regb_ddrc_ch0_dis_opt_valid_wrecc_cam_fill_level <= 'h0;
         ff_regb_ddrc_ch0_hwffc_en <= 'h0;
         ff_regb_ddrc_ch0_init_fsp <= 'h1;
         ff_regb_ddrc_ch0_init_vrcg <= 'h0;
         ff_regb_ddrc_ch0_target_vrcg <= 'h0;
         ff_regb_ddrc_ch0_skip_mrw_odtvref <= 'h0;
         ff_regb_ddrc_ch0_skip_zq_stop_start <= 'h0;
         ff_regb_ddrc_ch0_zq_interval <= 'h1;
         ff_regb_ddrc_ch0_hwffc_mode <= 'h0;
         ff_regb_ddrc_ch0_dfi_lp_en_pd <= 'h0;
         ff_regb_ddrc_ch0_dfi_lp_en_sr <= 'h0;
         ff_regb_ddrc_ch0_dfi_lp_en_dsm <= 'h0;
         ff_regb_ddrc_ch0_dfi_lp_en_data <= 'h0;
         ff_regb_ddrc_ch0_dfi_lp_data_req_en <= 'h1;
         ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data <= 'h0;
         ff_regb_ddrc_ch0_dfi_phyupd_en <= 'h1;
         ff_regb_ddrc_ch0_ctrlupd_pre_srx <= 'h0;
         ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx <= 'h0;
         ff_regb_ddrc_ch0_dis_auto_ctrlupd <= 'h0;
         ff_regb_ddrc_ch0_dfi_init_complete_en <= 'h1;
         ff_regb_ddrc_ch0_phy_dbi_mode <= 'h0;
         ff_regb_ddrc_ch0_dfi_data_cs_polarity <= 'h0;
         ff_regb_ddrc_ch0_dfi_reset_n <= 'h0;
         ff_regb_ddrc_ch0_dfi_init_start <= 'h0;
         ff_regb_ddrc_ch0_lp_optimized_write <= 'h0;
         ff_regb_ddrc_ch0_dfi_frequency <= 'h0;
         ff_regb_ddrc_ch0_dfi_freq_fsp <= 'h0;
         ff_regb_ddrc_ch0_dfi_channel_mode <= 'h0;
         ff_regb_ddrc_ch0_dfi_phymstr_en <= 'h1;
         ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32 <= 'h80;
         ff_regb_ddrc_ch0_wr_poison_slverr_en <= 'h1;
         ff_regb_ddrc_ch0_wr_poison_intr_en <= 'h1;
         ff_regb_ddrc_ch0_wr_poison_intr_clr <= 'h0;
         ff_regb_ddrc_ch0_rd_poison_slverr_en <= 'h1;
         ff_regb_ddrc_ch0_rd_poison_intr_en <= 'h1;
         ff_regb_ddrc_ch0_rd_poison_intr_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_mode <= 'h0;
         ff_regb_ddrc_ch0_ecc_ap_en <= 'h1;
         ff_regb_ddrc_ch0_ecc_region_remap_en <= 'h0;
         ff_regb_ddrc_ch0_ecc_region_map <= 'h7f;
         ff_regb_ddrc_ch0_blk_channel_idle_time_x32 <= 'h3f;
         ff_regb_ddrc_ch0_ecc_ap_err_threshold <= `MEMC_MAX_INLINE_ECC_PER_BURST/2-1;
         ff_regb_ddrc_ch0_ecc_region_map_other <= 'h0;
         ff_regb_ddrc_ch0_ecc_region_map_granu <= 'h0;
         cfgs_ff_regb_ddrc_ch0_data_poison_en <= 'h0;
         cfgs_ff_regb_ddrc_ch0_data_poison_bit <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_region_parity_lock <= 'h1;
         cfgs_ff_regb_ddrc_ch0_ecc_region_waste_lock <= 'h1;
         cfgs_ff_regb_ddrc_ch0_med_ecc_en <= 'h0;
         cfgs_ff_regb_ddrc_ch0_blk_channel_active_term <= 'h1;
         cfgs_ff_regb_ddrc_ch0_active_blk_channel <= `MEMC_NO_OF_BLK_CHANNEL-1;
         ff_regb_ddrc_ch0_ecc_corrected_err_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_uncorrected_err_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_ap_err_intr_clr <= 'h0;
         ff_regb_ddrc_ch0_ecc_corrected_err_intr_en <= 'h1;
         ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_en <= 'h1;
         ff_regb_ddrc_ch0_ecc_ap_err_intr_en <= 'h1;
         ff_regb_ddrc_ch0_ecc_corrected_err_intr_force <= 'h0;
         ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force <= 'h0;
         ff_regb_ddrc_ch0_ecc_ap_err_intr_force <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_col <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_rank <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_row <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_bank <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_bg <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_data_31_0 <= 'h0;
         cfgs_ff_regb_ddrc_ch0_ecc_poison_data_71_64 <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_en <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_en <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force <= 'h0;
         ff_regb_ddrc_ch0_linkecc_poison_inject_en <= 'h0;
         ff_regb_ddrc_ch0_linkecc_poison_type <= 'h0;
         ff_regb_ddrc_ch0_linkecc_poison_rw <= 'h0;
         ff_regb_ddrc_ch0_linkecc_poison_dmi_sel <= 'h0;
         ff_regb_ddrc_ch0_linkecc_poison_byte_sel <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_err_byte_sel <= 'h0;
         ff_regb_ddrc_ch0_rd_link_ecc_err_rank_sel <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_wc <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_max_rank_rd_opt <= 'h0;
         cfgs_ff_regb_ddrc_ch0_dis_max_rank_wr_opt <= 'h0;
         ff_regb_ddrc_ch0_dis_dq <= 'h0;
         ff_regb_ddrc_ch0_dis_hif <= 'h0;
         ff_regb_ddrc_ch0_zq_calib_short_todo  <= 1'b0;
         ff_regb_ddrc_ch0_zq_calib_short_saved <= 1'b0;
         ff_regb_ddrc_ch0_zq_calib_short <= 'h0;
         ff_regb_ddrc_ch0_ctrlupd_todo  <= 1'b0;
         ff_regb_ddrc_ch0_ctrlupd_saved <= 1'b0;
         ff_regb_ddrc_ch0_ctrlupd <= 'h0;
         ff_regb_ddrc_ch0_ctrlupd_burst <= 'h0;
         ff_regb_ddrc_ch0_rank0_refresh_todo  <= 1'b0;
         ff_regb_ddrc_ch0_rank0_refresh_saved <= 1'b0;
         ff_regb_ddrc_ch0_rank0_refresh <= 'h0;
         ff_regb_ddrc_ch0_rank1_refresh_todo  <= 1'b0;
         ff_regb_ddrc_ch0_rank1_refresh_saved <= 1'b0;
         ff_regb_ddrc_ch0_rank1_refresh <= 'h0;
         cfgs_ff_regb_ddrc_ch0_sw_done <= 'h1;
         cfgs_ff_regb_ddrc_ch0_max_rank_rd <= 'hf;
         cfgs_ff_regb_ddrc_ch0_max_rank_wr <= 'h0;
         ff_regb_ddrc_ch0_dm_en <= 'h1;
         ff_regb_ddrc_ch0_wr_dbi_en <= 'h0;
         ff_regb_ddrc_ch0_rd_dbi_en <= 'h0;
         ff_regb_ddrc_ch0_rank0_wr_odt <= 'h1;
         ff_regb_ddrc_ch0_rank0_rd_odt <= 'h1;
         ff_regb_ddrc_ch0_rank1_wr_odt <= (`MEMC_NUM_RANKS>1) ? 'h2 : 'h0;
         ff_regb_ddrc_ch0_rank1_rd_odt <= (`MEMC_NUM_RANKS>1) ? 'h2 : 'h0;
         ff_regb_ddrc_ch0_rd_data_copy_en <= 'h0;
         ff_regb_ddrc_ch0_wr_data_copy_en <= 'h0;
         ff_regb_ddrc_ch0_wr_data_x_en <= 'h0;
         cfgs_ff_regb_ddrc_ch0_sw_static_unlock <= 'h0;
         ff_regb_ddrc_ch0_force_clk_te_en <= 'h0;
         ff_regb_ddrc_ch0_force_clk_arb_en <= 'h0;
         ff_regb_ddrc_ch0_pre_cke_x1024 <= 'h4e;
         ff_regb_ddrc_ch0_post_cke_x1024 <= 'h2;
         ff_regb_ddrc_ch0_skip_dram_init <= 'h0;
         ff_regb_ddrc_ch0_ppt2_burst_num <= 'h200;
         ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi0 <= 'h8;
         ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi1 <= 'h0;
         ff_regb_ddrc_ch0_ppt2_burst_todo  <= 1'b0;
         ff_regb_ddrc_ch0_ppt2_burst_saved <= 1'b0;
         ff_regb_ddrc_ch0_ppt2_burst <= 'h0;
         ff_regb_ddrc_ch0_ppt2_wait_ref <= 'h1;
         cfgs_ff_regb_addr_map0_addrmap_cs_bit0 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_bank_b0 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_bank_b1 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_bank_b2 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_bg_b0 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_bg_b1 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b7 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b8 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b9 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b10 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b3 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b4 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b5 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_col_b6 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b14 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b15 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b16 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b17 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b10 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b11 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b12 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b13 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b6 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b7 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b8 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b9 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b2 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b3 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b4 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b5 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b0 <= 'h0;
         cfgs_ff_regb_addr_map0_addrmap_row_b1 <= 'h0;
         ff_regb_addr_map0_nonbinary_device_density <= 'h0;
         ff_regb_addr_map0_bank_hash_en <= 'h0;
         cfgs_ff_regb_arb_port0_go2critical_en <= 'h0;
         cfgs_ff_regb_arb_port0_pagematch_limit <= 'h0;
         cfgs_ff_regb_arb_port0_rd_port_priority <= 'h1f;
         cfgs_ff_regb_arb_port0_rd_port_aging_en <= 'h1;
         cfgs_ff_regb_arb_port0_rd_port_urgent_en <= 'h0;
         cfgs_ff_regb_arb_port0_rd_port_pagematch_en <= (`MEMC_DDR4_EN==1) ? 'h0 : 'h1;
         cfgs_ff_regb_arb_port0_rrb_lock_threshold <= 'h0;
         cfgs_ff_regb_arb_port0_wr_port_priority <= 'h1f;
         cfgs_ff_regb_arb_port0_wr_port_aging_en <= 'h1;
         cfgs_ff_regb_arb_port0_wr_port_urgent_en <= 'h0;
         cfgs_ff_regb_arb_port0_wr_port_pagematch_en <= 'h1;
         ff_regb_arb_port0_port_en <= $unsigned(`UMCTL2_PORT_EN_RESET_VALUE);
         cfgs_ff_regb_arb_port0_rqos_map_level1 <= 'h0;
         cfgs_ff_regb_arb_port0_rqos_map_level2 <= 'he;
         cfgs_ff_regb_arb_port0_rqos_map_region0 <= 'h0;
         cfgs_ff_regb_arb_port0_rqos_map_region1 <= 'h0;
         cfgs_ff_regb_arb_port0_rqos_map_region2 <= 'h2;
         cfgs_ff_regb_arb_port0_rqos_map_timeoutb <= 'h0;
         cfgs_ff_regb_arb_port0_rqos_map_timeoutr <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_level1 <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_level2 <= 'he;
         cfgs_ff_regb_arb_port0_wqos_map_region0 <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_region1 <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_region2 <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_timeout1 <= 'h0;
         cfgs_ff_regb_arb_port0_wqos_map_timeout2 <= 'h0;
         ff_regb_arb_port0_scrub_en <= 'h0;
         ff_regb_arb_port0_scrub_during_lowpower <= 'h0;
         ff_regb_arb_port0_scrub_burst_length_nm <= 'h1;
         ff_regb_arb_port0_scrub_interval <= 'hff;
         ff_regb_arb_port0_scrub_cmd_type <= 'h0;
         ff_regb_arb_port0_scrub_burst_length_lp <= 'h1;
         ff_regb_arb_port0_scrub_pattern0 <= 'h0;
         ff_regb_arb_port0_sbr_address_start_mask_0 <= 'h0;
         ff_regb_arb_port0_sbr_address_start_mask_1 <= 'h0;
         ff_regb_arb_port0_sbr_address_range_mask_0 <= 'h0;
         ff_regb_arb_port0_sbr_address_range_mask_1 <= 'h0;
         cfgs_ff_regb_freq0_ch0_t_ras_min <= 'hf;
         cfgs_ff_regb_freq0_ch0_t_ras_max <= 'h1b;
         cfgs_ff_regb_freq0_ch0_t_faw <= 'h10;
         cfgs_ff_regb_freq0_ch0_wr2pre <= 'hf;
         cfgs_ff_regb_freq0_ch0_t_rc <= 'h14;
         cfgs_ff_regb_freq0_ch0_rd2pre <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_xp <= 'h8;
         cfgs_ff_regb_freq0_ch0_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq0_ch0_wr2rd <= 'hd;
         cfgs_ff_regb_freq0_ch0_rd2wr <= 'h6;
         cfgs_ff_regb_freq0_ch0_read_latency <= 'h5;
         cfgs_ff_regb_freq0_ch0_write_latency <= 'h3;
         cfgs_ff_regb_freq0_ch0_wr2mr <= 'h4;
         cfgs_ff_regb_freq0_ch0_rd2mr <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_mr <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_rp <= 'h5;
         cfgs_ff_regb_freq0_ch0_t_rrd <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_ccd <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_rcd <= 'h5;
         ff_regb_freq0_ch0_t_cke <= 'h3;
         ff_regb_freq0_ch0_t_ckesr <= 'h4;
         ff_regb_freq0_ch0_t_cksre <= 'h5;
         ff_regb_freq0_ch0_t_cksrx <= 'h5;
         cfgs_ff_regb_freq0_ch0_t_ckcsx <= 'h5;
         ff_regb_freq0_ch0_t_csh <= 'h0;
         cfgs_ff_regb_freq0_ch0_wr2rd_s <= 'hd;
         cfgs_ff_regb_freq0_ch0_t_rrd_s <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_ccd_s <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_cmdcke <= 'h2;
         cfgs_ff_regb_freq0_ch0_t_ppd <= 'h4;
         cfgs_ff_regb_freq0_ch0_t_ccd_mw <= 'h20;
         cfgs_ff_regb_freq0_ch0_odtloff <= 'h1c;
         cfgs_ff_regb_freq0_ch0_t_xsr <= 'ha0;
         cfgs_ff_regb_freq0_ch0_t_osco <= 'h8;
         cfgs_ff_regb_freq0_ch0_t_vrcg_disable <= 'h0;
         cfgs_ff_regb_freq0_ch0_t_vrcg_enable <= 'h0;
         ff_regb_freq0_ch0_t_pdn <= 'h0;
         ff_regb_freq0_ch0_t_xsr_dsm_x1024 <= 'h0;
         cfgs_ff_regb_freq0_ch0_max_wr_sync <= 'hf;
         cfgs_ff_regb_freq0_ch0_max_rd_sync <= 'hf;
         cfgs_ff_regb_freq0_ch0_rd2wr_s <= 'hf;
         cfgs_ff_regb_freq0_ch0_bank_org <= 'h0;
         cfgs_ff_regb_freq0_ch0_rda2pre <= 'h0;
         cfgs_ff_regb_freq0_ch0_wra2pre <= 'h0;
         cfgs_ff_regb_freq0_ch0_lpddr4_diff_bank_rwa2pre <= 'h0;
         ff_regb_freq0_ch0_mrr2rd <= 'h0;
         ff_regb_freq0_ch0_mrr2wr <= 'h0;
         ff_regb_freq0_ch0_mrr2mrw <= 'h0;
         ff_regb_freq0_ch0_ws_fs2wck_sus <= 'h8;
         ff_regb_freq0_ch0_t_wcksus <= 'h4;
         ff_regb_freq0_ch0_ws_off2ws_fs <= 'h3;
         cfgs_ff_regb_freq0_ch0_emr <= 'h510;
         cfgs_ff_regb_freq0_ch0_mr <= 'h0;
         ff_regb_freq0_ch0_emr3 <= 'h0;
         ff_regb_freq0_ch0_emr2 <= 'h0;
         cfgs_ff_regb_freq0_ch0_mr5 <= 'h0;
         cfgs_ff_regb_freq0_ch0_mr4 <= 'h0;
         cfgs_ff_regb_freq0_ch0_mr6 <= 'h0;
         cfgs_ff_regb_freq0_ch0_mr22 <= 'h0;
         ff_regb_freq0_ch0_dfi_tphy_wrlat <= 'h2;
         ff_regb_freq0_ch0_dfi_tphy_wrdata <= 'h0;
         ff_regb_freq0_ch0_dfi_t_rddata_en <= 'h2;
         ff_regb_freq0_ch0_dfi_t_ctrl_delay <= 'h7;
         ff_regb_freq0_ch0_dfi_t_dram_clk_enable <= 'h4;
         ff_regb_freq0_ch0_dfi_t_dram_clk_disable <= 'h4;
         ff_regb_freq0_ch0_dfi_t_wrdata_delay <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_tphy_wrcslat <= 'h2;
         cfgs_ff_regb_freq0_ch0_dfi_tphy_rdcslat <= 'h2;
         cfgs_ff_regb_freq0_ch0_dfi_twck_delay <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_dis <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_en_fs <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_en_wr <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_en_rd <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_cs <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_toggle <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_fast_toggle <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd <= 'h0;
         cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd_en <= 'h0;
         ff_regb_freq0_ch0_dfi_lp_wakeup_pd <= 'h0;
         ff_regb_freq0_ch0_dfi_lp_wakeup_sr <= 'h0;
         ff_regb_freq0_ch0_dfi_lp_wakeup_dsm <= 'h0;
         ff_regb_freq0_ch0_dfi_lp_wakeup_data <= 'h0;
         ff_regb_freq0_ch0_dfi_tlp_resp <= 'h7;
         ff_regb_freq0_ch0_dfi_t_ctrlup_min <= 'h3;
         ff_regb_freq0_ch0_dfi_t_ctrlup_max <= 'h40;
         cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_max_x1024 <= 'h1;
         cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_min_x1024 <= 'h1;
         ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1 <= 'h12c;
         ff_regb_freq0_ch0_ctrlupd_after_dqsosc <= 'h0;
         ff_regb_freq0_ch0_ppt2_override <= 'h0;
         ff_regb_freq0_ch0_ppt2_en <= 'h0;
         ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1_unit <= 'h3;
         cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_burst_interval_x8 <= 'h1;
         ff_regb_freq0_ch0_t_refi_x1_x32 <= 'h62;
         ff_regb_freq0_ch0_refresh_to_x1_x32 <= 'h10;
         ff_regb_freq0_ch0_refresh_margin <= 'h2;
         ff_regb_freq0_ch0_refresh_to_x1_sel <= 'h0;
         ff_regb_freq0_ch0_t_refi_x1_sel <= 'h0;
         ff_regb_freq0_ch0_t_rfc_min <= 'h8c;
         ff_regb_freq0_ch0_t_rfc_min_ab <= 'h0;
         ff_regb_freq0_ch0_t_pbr2pbr <= 'h8c;
         ff_regb_freq0_ch0_t_pbr2act <= 'h8c;
         ff_regb_freq0_ch0_refresh_to_ab_x32 <= 'h10;
         ff_regb_freq0_ch0_refresh_timer0_start_value_x32 <= 'h0;
         ff_regb_freq0_ch0_refresh_timer1_start_value_x32 <= 'h0;
         ff_regb_freq0_ch0_t_rfmpb <= 'h8c;
         ff_regb_freq0_ch0_t_zq_long_nop <= 'h200;
         ff_regb_freq0_ch0_t_zq_short_nop <= 'h40;
         cfgs_ff_regb_freq0_ch0_t_zq_short_interval_x1024 <= 'h100;
         cfgs_ff_regb_freq0_ch0_t_zq_reset_nop <= 'h20;
         ff_regb_freq0_ch0_t_zq_stop <= 'h18;
         ff_regb_freq0_ch0_dqsosc_enable <= 'h0;
         ff_regb_freq0_ch0_dqsosc_interval_unit <= 'h0;
         ff_regb_freq0_ch0_dqsosc_interval <= 'h7;
         cfgs_ff_regb_freq0_ch0_mr4_read_interval <= 'h800000;
         ff_regb_freq0_ch0_derated_t_rrd <= 'h4;
         ff_regb_freq0_ch0_derated_t_rp <= 'h5;
         ff_regb_freq0_ch0_derated_t_ras_min <= 'hf;
         ff_regb_freq0_ch0_derated_t_rcd <= 'h5;
         ff_regb_freq0_ch0_derated_t_rc <= 'h14;
         ff_regb_freq0_ch0_derated_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq0_ch0_hw_lp_idle_x32 <= 'h0;
         cfgs_ff_regb_freq0_ch0_dvfsq_enable <= 'h0;
         cfgs_ff_regb_freq0_ch0_pageclose_timer <= 'h0;
         cfgs_ff_regb_freq0_ch0_rdwr_idle_gap <= 'h0;
         cfgs_ff_regb_freq0_ch0_hpr_max_starve <= 'h1;
         cfgs_ff_regb_freq0_ch0_hpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq0_ch0_lpr_max_starve <= 'h7f;
         cfgs_ff_regb_freq0_ch0_lpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq0_ch0_w_max_starve <= 'h7f;
         cfgs_ff_regb_freq0_ch0_w_xact_run_length <= 'hf;
         ff_regb_freq0_ch0_frequency_ratio <= 'h0;
         cfgs_ff_regb_freq0_ch0_diff_rank_rd_gap <= 'h6;
         cfgs_ff_regb_freq0_ch0_diff_rank_wr_gap <= 'h6;
         cfgs_ff_regb_freq0_ch0_wr2rd_dr <= 'hf;
         cfgs_ff_regb_freq0_ch0_rd2wr_dr <= 'hf;
         cfgs_ff_regb_freq0_ch0_powerdown_to_x32 <= 'h10;
         cfgs_ff_regb_freq0_ch0_selfref_to_x32 <= 'h40;
         cfgs_ff_regb_freq0_ch0_t_pgm_x1_x1024 <= 'h2faf09;
         cfgs_ff_regb_freq0_ch0_t_pgm_x1_sel <= 'h0;
         cfgs_ff_regb_freq0_ch0_t_pgmpst_x32 <= 'h9c5;
         cfgs_ff_regb_freq0_ch0_t_pgm_exit <= 'h18;
         ff_regb_freq0_ch0_wr_link_ecc_enable <= 'h0;
         ff_regb_freq0_ch0_rd_link_ecc_enable <= 'h0;
         cfgs_ff_regb_freq1_ch0_t_ras_min <= 'hf;
         cfgs_ff_regb_freq1_ch0_t_ras_max <= 'h1b;
         cfgs_ff_regb_freq1_ch0_t_faw <= 'h10;
         cfgs_ff_regb_freq1_ch0_wr2pre <= 'hf;
         cfgs_ff_regb_freq1_ch0_t_rc <= 'h14;
         cfgs_ff_regb_freq1_ch0_rd2pre <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_xp <= 'h8;
         cfgs_ff_regb_freq1_ch0_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq1_ch0_wr2rd <= 'hd;
         cfgs_ff_regb_freq1_ch0_rd2wr <= 'h6;
         cfgs_ff_regb_freq1_ch0_read_latency <= 'h5;
         cfgs_ff_regb_freq1_ch0_write_latency <= 'h3;
         cfgs_ff_regb_freq1_ch0_wr2mr <= 'h4;
         cfgs_ff_regb_freq1_ch0_rd2mr <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_mr <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_rp <= 'h5;
         cfgs_ff_regb_freq1_ch0_t_rrd <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_ccd <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_rcd <= 'h5;
         ff_regb_freq1_ch0_t_cke <= 'h3;
         ff_regb_freq1_ch0_t_ckesr <= 'h4;
         ff_regb_freq1_ch0_t_cksre <= 'h5;
         ff_regb_freq1_ch0_t_cksrx <= 'h5;
         cfgs_ff_regb_freq1_ch0_t_ckcsx <= 'h5;
         ff_regb_freq1_ch0_t_csh <= 'h0;
         cfgs_ff_regb_freq1_ch0_wr2rd_s <= 'hd;
         cfgs_ff_regb_freq1_ch0_t_rrd_s <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_ccd_s <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_cmdcke <= 'h2;
         cfgs_ff_regb_freq1_ch0_t_ppd <= 'h4;
         cfgs_ff_regb_freq1_ch0_t_ccd_mw <= 'h20;
         cfgs_ff_regb_freq1_ch0_odtloff <= 'h1c;
         cfgs_ff_regb_freq1_ch0_t_xsr <= 'ha0;
         cfgs_ff_regb_freq1_ch0_t_osco <= 'h8;
         cfgs_ff_regb_freq1_ch0_t_vrcg_disable <= 'h0;
         cfgs_ff_regb_freq1_ch0_t_vrcg_enable <= 'h0;
         ff_regb_freq1_ch0_t_pdn <= 'h0;
         ff_regb_freq1_ch0_t_xsr_dsm_x1024 <= 'h0;
         cfgs_ff_regb_freq1_ch0_max_wr_sync <= 'hf;
         cfgs_ff_regb_freq1_ch0_max_rd_sync <= 'hf;
         cfgs_ff_regb_freq1_ch0_rd2wr_s <= 'hf;
         cfgs_ff_regb_freq1_ch0_bank_org <= 'h0;
         cfgs_ff_regb_freq1_ch0_rda2pre <= 'h0;
         cfgs_ff_regb_freq1_ch0_wra2pre <= 'h0;
         cfgs_ff_regb_freq1_ch0_lpddr4_diff_bank_rwa2pre <= 'h0;
         ff_regb_freq1_ch0_mrr2rd <= 'h0;
         ff_regb_freq1_ch0_mrr2wr <= 'h0;
         ff_regb_freq1_ch0_mrr2mrw <= 'h0;
         ff_regb_freq1_ch0_ws_fs2wck_sus <= 'h8;
         ff_regb_freq1_ch0_t_wcksus <= 'h4;
         ff_regb_freq1_ch0_ws_off2ws_fs <= 'h3;
         cfgs_ff_regb_freq1_ch0_emr <= 'h510;
         cfgs_ff_regb_freq1_ch0_mr <= 'h0;
         ff_regb_freq1_ch0_emr3 <= 'h0;
         ff_regb_freq1_ch0_emr2 <= 'h0;
         cfgs_ff_regb_freq1_ch0_mr5 <= 'h0;
         cfgs_ff_regb_freq1_ch0_mr4 <= 'h0;
         cfgs_ff_regb_freq1_ch0_mr6 <= 'h0;
         cfgs_ff_regb_freq1_ch0_mr22 <= 'h0;
         ff_regb_freq1_ch0_dfi_tphy_wrlat <= 'h2;
         ff_regb_freq1_ch0_dfi_tphy_wrdata <= 'h0;
         ff_regb_freq1_ch0_dfi_t_rddata_en <= 'h2;
         ff_regb_freq1_ch0_dfi_t_ctrl_delay <= 'h7;
         ff_regb_freq1_ch0_dfi_t_dram_clk_enable <= 'h4;
         ff_regb_freq1_ch0_dfi_t_dram_clk_disable <= 'h4;
         ff_regb_freq1_ch0_dfi_t_wrdata_delay <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_tphy_wrcslat <= 'h2;
         cfgs_ff_regb_freq1_ch0_dfi_tphy_rdcslat <= 'h2;
         cfgs_ff_regb_freq1_ch0_dfi_twck_delay <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_dis <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_en_fs <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_en_wr <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_en_rd <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_cs <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_toggle <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_fast_toggle <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd_en <= 'h0;
         cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_max_x1024 <= 'h1;
         cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_min_x1024 <= 'h1;
         ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1 <= 'h12c;
         ff_regb_freq1_ch0_ctrlupd_after_dqsosc <= 'h0;
         ff_regb_freq1_ch0_ppt2_override <= 'h0;
         ff_regb_freq1_ch0_ppt2_en <= 'h0;
         ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1_unit <= 'h3;
         cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_burst_interval_x8 <= 'h1;
         ff_regb_freq1_ch0_t_refi_x1_x32 <= 'h62;
         ff_regb_freq1_ch0_refresh_to_x1_x32 <= 'h10;
         ff_regb_freq1_ch0_refresh_margin <= 'h2;
         ff_regb_freq1_ch0_refresh_to_x1_sel <= 'h0;
         ff_regb_freq1_ch0_t_refi_x1_sel <= 'h0;
         ff_regb_freq1_ch0_t_rfc_min <= 'h8c;
         ff_regb_freq1_ch0_t_rfc_min_ab <= 'h0;
         ff_regb_freq1_ch0_t_pbr2pbr <= 'h8c;
         ff_regb_freq1_ch0_t_pbr2act <= 'h8c;
         ff_regb_freq1_ch0_refresh_to_ab_x32 <= 'h10;
         ff_regb_freq1_ch0_refresh_timer0_start_value_x32 <= 'h0;
         ff_regb_freq1_ch0_refresh_timer1_start_value_x32 <= 'h0;
         ff_regb_freq1_ch0_t_rfmpb <= 'h8c;
         ff_regb_freq1_ch0_t_zq_long_nop <= 'h200;
         ff_regb_freq1_ch0_t_zq_short_nop <= 'h40;
         cfgs_ff_regb_freq1_ch0_t_zq_short_interval_x1024 <= 'h100;
         cfgs_ff_regb_freq1_ch0_t_zq_reset_nop <= 'h20;
         ff_regb_freq1_ch0_t_zq_stop <= 'h18;
         ff_regb_freq1_ch0_dqsosc_enable <= 'h0;
         ff_regb_freq1_ch0_dqsosc_interval_unit <= 'h0;
         ff_regb_freq1_ch0_dqsosc_interval <= 'h7;
         cfgs_ff_regb_freq1_ch0_mr4_read_interval <= 'h800000;
         ff_regb_freq1_ch0_derated_t_rrd <= 'h4;
         ff_regb_freq1_ch0_derated_t_rp <= 'h5;
         ff_regb_freq1_ch0_derated_t_ras_min <= 'hf;
         ff_regb_freq1_ch0_derated_t_rcd <= 'h5;
         ff_regb_freq1_ch0_derated_t_rc <= 'h14;
         ff_regb_freq1_ch0_derated_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq1_ch0_hw_lp_idle_x32 <= 'h0;
         cfgs_ff_regb_freq1_ch0_dvfsq_enable <= 'h0;
         cfgs_ff_regb_freq1_ch0_pageclose_timer <= 'h0;
         cfgs_ff_regb_freq1_ch0_rdwr_idle_gap <= 'h0;
         cfgs_ff_regb_freq1_ch0_hpr_max_starve <= 'h1;
         cfgs_ff_regb_freq1_ch0_hpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq1_ch0_lpr_max_starve <= 'h7f;
         cfgs_ff_regb_freq1_ch0_lpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq1_ch0_w_max_starve <= 'h7f;
         cfgs_ff_regb_freq1_ch0_w_xact_run_length <= 'hf;
         ff_regb_freq1_ch0_frequency_ratio <= 'h0;
         cfgs_ff_regb_freq1_ch0_diff_rank_rd_gap <= 'h6;
         cfgs_ff_regb_freq1_ch0_diff_rank_wr_gap <= 'h6;
         cfgs_ff_regb_freq1_ch0_wr2rd_dr <= 'hf;
         cfgs_ff_regb_freq1_ch0_rd2wr_dr <= 'hf;
         cfgs_ff_regb_freq1_ch0_powerdown_to_x32 <= 'h10;
         cfgs_ff_regb_freq1_ch0_selfref_to_x32 <= 'h40;
         cfgs_ff_regb_freq1_ch0_t_pgm_x1_x1024 <= 'h2faf09;
         cfgs_ff_regb_freq1_ch0_t_pgm_x1_sel <= 'h0;
         cfgs_ff_regb_freq1_ch0_t_pgmpst_x32 <= 'h9c5;
         cfgs_ff_regb_freq1_ch0_t_pgm_exit <= 'h18;
         ff_regb_freq1_ch0_wr_link_ecc_enable <= 'h0;
         ff_regb_freq1_ch0_rd_link_ecc_enable <= 'h0;
         cfgs_ff_regb_freq2_ch0_t_ras_min <= 'hf;
         cfgs_ff_regb_freq2_ch0_t_ras_max <= 'h1b;
         cfgs_ff_regb_freq2_ch0_t_faw <= 'h10;
         cfgs_ff_regb_freq2_ch0_wr2pre <= 'hf;
         cfgs_ff_regb_freq2_ch0_t_rc <= 'h14;
         cfgs_ff_regb_freq2_ch0_rd2pre <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_xp <= 'h8;
         cfgs_ff_regb_freq2_ch0_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq2_ch0_wr2rd <= 'hd;
         cfgs_ff_regb_freq2_ch0_rd2wr <= 'h6;
         cfgs_ff_regb_freq2_ch0_read_latency <= 'h5;
         cfgs_ff_regb_freq2_ch0_write_latency <= 'h3;
         cfgs_ff_regb_freq2_ch0_wr2mr <= 'h4;
         cfgs_ff_regb_freq2_ch0_rd2mr <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_mr <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_rp <= 'h5;
         cfgs_ff_regb_freq2_ch0_t_rrd <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_ccd <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_rcd <= 'h5;
         ff_regb_freq2_ch0_t_cke <= 'h3;
         ff_regb_freq2_ch0_t_ckesr <= 'h4;
         ff_regb_freq2_ch0_t_cksre <= 'h5;
         ff_regb_freq2_ch0_t_cksrx <= 'h5;
         cfgs_ff_regb_freq2_ch0_t_ckcsx <= 'h5;
         ff_regb_freq2_ch0_t_csh <= 'h0;
         cfgs_ff_regb_freq2_ch0_wr2rd_s <= 'hd;
         cfgs_ff_regb_freq2_ch0_t_rrd_s <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_ccd_s <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_cmdcke <= 'h2;
         cfgs_ff_regb_freq2_ch0_t_ppd <= 'h4;
         cfgs_ff_regb_freq2_ch0_t_ccd_mw <= 'h20;
         cfgs_ff_regb_freq2_ch0_odtloff <= 'h1c;
         cfgs_ff_regb_freq2_ch0_t_xsr <= 'ha0;
         cfgs_ff_regb_freq2_ch0_t_osco <= 'h8;
         cfgs_ff_regb_freq2_ch0_t_vrcg_disable <= 'h0;
         cfgs_ff_regb_freq2_ch0_t_vrcg_enable <= 'h0;
         ff_regb_freq2_ch0_t_pdn <= 'h0;
         ff_regb_freq2_ch0_t_xsr_dsm_x1024 <= 'h0;
         cfgs_ff_regb_freq2_ch0_max_wr_sync <= 'hf;
         cfgs_ff_regb_freq2_ch0_max_rd_sync <= 'hf;
         cfgs_ff_regb_freq2_ch0_rd2wr_s <= 'hf;
         cfgs_ff_regb_freq2_ch0_bank_org <= 'h0;
         cfgs_ff_regb_freq2_ch0_rda2pre <= 'h0;
         cfgs_ff_regb_freq2_ch0_wra2pre <= 'h0;
         cfgs_ff_regb_freq2_ch0_lpddr4_diff_bank_rwa2pre <= 'h0;
         ff_regb_freq2_ch0_mrr2rd <= 'h0;
         ff_regb_freq2_ch0_mrr2wr <= 'h0;
         ff_regb_freq2_ch0_mrr2mrw <= 'h0;
         ff_regb_freq2_ch0_ws_fs2wck_sus <= 'h8;
         ff_regb_freq2_ch0_t_wcksus <= 'h4;
         ff_regb_freq2_ch0_ws_off2ws_fs <= 'h3;
         cfgs_ff_regb_freq2_ch0_emr <= 'h510;
         cfgs_ff_regb_freq2_ch0_mr <= 'h0;
         ff_regb_freq2_ch0_emr3 <= 'h0;
         ff_regb_freq2_ch0_emr2 <= 'h0;
         cfgs_ff_regb_freq2_ch0_mr5 <= 'h0;
         cfgs_ff_regb_freq2_ch0_mr4 <= 'h0;
         cfgs_ff_regb_freq2_ch0_mr6 <= 'h0;
         cfgs_ff_regb_freq2_ch0_mr22 <= 'h0;
         ff_regb_freq2_ch0_dfi_tphy_wrlat <= 'h2;
         ff_regb_freq2_ch0_dfi_tphy_wrdata <= 'h0;
         ff_regb_freq2_ch0_dfi_t_rddata_en <= 'h2;
         ff_regb_freq2_ch0_dfi_t_ctrl_delay <= 'h7;
         ff_regb_freq2_ch0_dfi_t_dram_clk_enable <= 'h4;
         ff_regb_freq2_ch0_dfi_t_dram_clk_disable <= 'h4;
         ff_regb_freq2_ch0_dfi_t_wrdata_delay <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_tphy_wrcslat <= 'h2;
         cfgs_ff_regb_freq2_ch0_dfi_tphy_rdcslat <= 'h2;
         cfgs_ff_regb_freq2_ch0_dfi_twck_delay <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_dis <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_en_fs <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_en_wr <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_en_rd <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_cs <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_toggle <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_fast_toggle <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd_en <= 'h0;
         cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_max_x1024 <= 'h1;
         cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_min_x1024 <= 'h1;
         ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1 <= 'h12c;
         ff_regb_freq2_ch0_ctrlupd_after_dqsosc <= 'h0;
         ff_regb_freq2_ch0_ppt2_override <= 'h0;
         ff_regb_freq2_ch0_ppt2_en <= 'h0;
         ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1_unit <= 'h3;
         cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_burst_interval_x8 <= 'h1;
         ff_regb_freq2_ch0_t_refi_x1_x32 <= 'h62;
         ff_regb_freq2_ch0_refresh_to_x1_x32 <= 'h10;
         ff_regb_freq2_ch0_refresh_margin <= 'h2;
         ff_regb_freq2_ch0_refresh_to_x1_sel <= 'h0;
         ff_regb_freq2_ch0_t_refi_x1_sel <= 'h0;
         ff_regb_freq2_ch0_t_rfc_min <= 'h8c;
         ff_regb_freq2_ch0_t_rfc_min_ab <= 'h0;
         ff_regb_freq2_ch0_t_pbr2pbr <= 'h8c;
         ff_regb_freq2_ch0_t_pbr2act <= 'h8c;
         ff_regb_freq2_ch0_refresh_to_ab_x32 <= 'h10;
         ff_regb_freq2_ch0_refresh_timer0_start_value_x32 <= 'h0;
         ff_regb_freq2_ch0_refresh_timer1_start_value_x32 <= 'h0;
         ff_regb_freq2_ch0_t_rfmpb <= 'h8c;
         ff_regb_freq2_ch0_t_zq_long_nop <= 'h200;
         ff_regb_freq2_ch0_t_zq_short_nop <= 'h40;
         cfgs_ff_regb_freq2_ch0_t_zq_short_interval_x1024 <= 'h100;
         cfgs_ff_regb_freq2_ch0_t_zq_reset_nop <= 'h20;
         ff_regb_freq2_ch0_t_zq_stop <= 'h18;
         ff_regb_freq2_ch0_dqsosc_enable <= 'h0;
         ff_regb_freq2_ch0_dqsosc_interval_unit <= 'h0;
         ff_regb_freq2_ch0_dqsosc_interval <= 'h7;
         cfgs_ff_regb_freq2_ch0_mr4_read_interval <= 'h800000;
         ff_regb_freq2_ch0_derated_t_rrd <= 'h4;
         ff_regb_freq2_ch0_derated_t_rp <= 'h5;
         ff_regb_freq2_ch0_derated_t_ras_min <= 'hf;
         ff_regb_freq2_ch0_derated_t_rcd <= 'h5;
         ff_regb_freq2_ch0_derated_t_rc <= 'h14;
         ff_regb_freq2_ch0_derated_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq2_ch0_hw_lp_idle_x32 <= 'h0;
         cfgs_ff_regb_freq2_ch0_dvfsq_enable <= 'h0;
         cfgs_ff_regb_freq2_ch0_pageclose_timer <= 'h0;
         cfgs_ff_regb_freq2_ch0_rdwr_idle_gap <= 'h0;
         cfgs_ff_regb_freq2_ch0_hpr_max_starve <= 'h1;
         cfgs_ff_regb_freq2_ch0_hpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq2_ch0_lpr_max_starve <= 'h7f;
         cfgs_ff_regb_freq2_ch0_lpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq2_ch0_w_max_starve <= 'h7f;
         cfgs_ff_regb_freq2_ch0_w_xact_run_length <= 'hf;
         ff_regb_freq2_ch0_frequency_ratio <= 'h0;
         cfgs_ff_regb_freq2_ch0_diff_rank_rd_gap <= 'h6;
         cfgs_ff_regb_freq2_ch0_diff_rank_wr_gap <= 'h6;
         cfgs_ff_regb_freq2_ch0_wr2rd_dr <= 'hf;
         cfgs_ff_regb_freq2_ch0_rd2wr_dr <= 'hf;
         cfgs_ff_regb_freq2_ch0_powerdown_to_x32 <= 'h10;
         cfgs_ff_regb_freq2_ch0_selfref_to_x32 <= 'h40;
         cfgs_ff_regb_freq2_ch0_t_pgm_x1_x1024 <= 'h2faf09;
         cfgs_ff_regb_freq2_ch0_t_pgm_x1_sel <= 'h0;
         cfgs_ff_regb_freq2_ch0_t_pgmpst_x32 <= 'h9c5;
         cfgs_ff_regb_freq2_ch0_t_pgm_exit <= 'h18;
         ff_regb_freq2_ch0_wr_link_ecc_enable <= 'h0;
         ff_regb_freq2_ch0_rd_link_ecc_enable <= 'h0;
         cfgs_ff_regb_freq3_ch0_t_ras_min <= 'hf;
         cfgs_ff_regb_freq3_ch0_t_ras_max <= 'h1b;
         cfgs_ff_regb_freq3_ch0_t_faw <= 'h10;
         cfgs_ff_regb_freq3_ch0_wr2pre <= 'hf;
         cfgs_ff_regb_freq3_ch0_t_rc <= 'h14;
         cfgs_ff_regb_freq3_ch0_rd2pre <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_xp <= 'h8;
         cfgs_ff_regb_freq3_ch0_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq3_ch0_wr2rd <= 'hd;
         cfgs_ff_regb_freq3_ch0_rd2wr <= 'h6;
         cfgs_ff_regb_freq3_ch0_read_latency <= 'h5;
         cfgs_ff_regb_freq3_ch0_write_latency <= 'h3;
         cfgs_ff_regb_freq3_ch0_wr2mr <= 'h4;
         cfgs_ff_regb_freq3_ch0_rd2mr <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_mr <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_rp <= 'h5;
         cfgs_ff_regb_freq3_ch0_t_rrd <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_ccd <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_rcd <= 'h5;
         ff_regb_freq3_ch0_t_cke <= 'h3;
         ff_regb_freq3_ch0_t_ckesr <= 'h4;
         ff_regb_freq3_ch0_t_cksre <= 'h5;
         ff_regb_freq3_ch0_t_cksrx <= 'h5;
         cfgs_ff_regb_freq3_ch0_t_ckcsx <= 'h5;
         ff_regb_freq3_ch0_t_csh <= 'h0;
         cfgs_ff_regb_freq3_ch0_wr2rd_s <= 'hd;
         cfgs_ff_regb_freq3_ch0_t_rrd_s <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_ccd_s <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_cmdcke <= 'h2;
         cfgs_ff_regb_freq3_ch0_t_ppd <= 'h4;
         cfgs_ff_regb_freq3_ch0_t_ccd_mw <= 'h20;
         cfgs_ff_regb_freq3_ch0_odtloff <= 'h1c;
         cfgs_ff_regb_freq3_ch0_t_xsr <= 'ha0;
         cfgs_ff_regb_freq3_ch0_t_osco <= 'h8;
         cfgs_ff_regb_freq3_ch0_t_vrcg_disable <= 'h0;
         cfgs_ff_regb_freq3_ch0_t_vrcg_enable <= 'h0;
         ff_regb_freq3_ch0_t_pdn <= 'h0;
         ff_regb_freq3_ch0_t_xsr_dsm_x1024 <= 'h0;
         cfgs_ff_regb_freq3_ch0_max_wr_sync <= 'hf;
         cfgs_ff_regb_freq3_ch0_max_rd_sync <= 'hf;
         cfgs_ff_regb_freq3_ch0_rd2wr_s <= 'hf;
         cfgs_ff_regb_freq3_ch0_bank_org <= 'h0;
         cfgs_ff_regb_freq3_ch0_rda2pre <= 'h0;
         cfgs_ff_regb_freq3_ch0_wra2pre <= 'h0;
         cfgs_ff_regb_freq3_ch0_lpddr4_diff_bank_rwa2pre <= 'h0;
         ff_regb_freq3_ch0_mrr2rd <= 'h0;
         ff_regb_freq3_ch0_mrr2wr <= 'h0;
         ff_regb_freq3_ch0_mrr2mrw <= 'h0;
         ff_regb_freq3_ch0_ws_fs2wck_sus <= 'h8;
         ff_regb_freq3_ch0_t_wcksus <= 'h4;
         ff_regb_freq3_ch0_ws_off2ws_fs <= 'h3;
         cfgs_ff_regb_freq3_ch0_emr <= 'h510;
         cfgs_ff_regb_freq3_ch0_mr <= 'h0;
         ff_regb_freq3_ch0_emr3 <= 'h0;
         ff_regb_freq3_ch0_emr2 <= 'h0;
         cfgs_ff_regb_freq3_ch0_mr5 <= 'h0;
         cfgs_ff_regb_freq3_ch0_mr4 <= 'h0;
         cfgs_ff_regb_freq3_ch0_mr6 <= 'h0;
         cfgs_ff_regb_freq3_ch0_mr22 <= 'h0;
         ff_regb_freq3_ch0_dfi_tphy_wrlat <= 'h2;
         ff_regb_freq3_ch0_dfi_tphy_wrdata <= 'h0;
         ff_regb_freq3_ch0_dfi_t_rddata_en <= 'h2;
         ff_regb_freq3_ch0_dfi_t_ctrl_delay <= 'h7;
         ff_regb_freq3_ch0_dfi_t_dram_clk_enable <= 'h4;
         ff_regb_freq3_ch0_dfi_t_dram_clk_disable <= 'h4;
         ff_regb_freq3_ch0_dfi_t_wrdata_delay <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_tphy_wrcslat <= 'h2;
         cfgs_ff_regb_freq3_ch0_dfi_tphy_rdcslat <= 'h2;
         cfgs_ff_regb_freq3_ch0_dfi_twck_delay <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_dis <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_en_fs <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_en_wr <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_en_rd <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_cs <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_toggle <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_fast_toggle <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd_en <= 'h0;
         cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_max_x1024 <= 'h1;
         cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_min_x1024 <= 'h1;
         ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1 <= 'h12c;
         ff_regb_freq3_ch0_ctrlupd_after_dqsosc <= 'h0;
         ff_regb_freq3_ch0_ppt2_override <= 'h0;
         ff_regb_freq3_ch0_ppt2_en <= 'h0;
         ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1_unit <= 'h3;
         cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_burst_interval_x8 <= 'h1;
         ff_regb_freq3_ch0_t_refi_x1_x32 <= 'h62;
         ff_regb_freq3_ch0_refresh_to_x1_x32 <= 'h10;
         ff_regb_freq3_ch0_refresh_margin <= 'h2;
         ff_regb_freq3_ch0_refresh_to_x1_sel <= 'h0;
         ff_regb_freq3_ch0_t_refi_x1_sel <= 'h0;
         ff_regb_freq3_ch0_t_rfc_min <= 'h8c;
         ff_regb_freq3_ch0_t_rfc_min_ab <= 'h0;
         ff_regb_freq3_ch0_t_pbr2pbr <= 'h8c;
         ff_regb_freq3_ch0_t_pbr2act <= 'h8c;
         ff_regb_freq3_ch0_refresh_to_ab_x32 <= 'h10;
         ff_regb_freq3_ch0_refresh_timer0_start_value_x32 <= 'h0;
         ff_regb_freq3_ch0_refresh_timer1_start_value_x32 <= 'h0;
         ff_regb_freq3_ch0_t_rfmpb <= 'h8c;
         ff_regb_freq3_ch0_t_zq_long_nop <= 'h200;
         ff_regb_freq3_ch0_t_zq_short_nop <= 'h40;
         cfgs_ff_regb_freq3_ch0_t_zq_short_interval_x1024 <= 'h100;
         cfgs_ff_regb_freq3_ch0_t_zq_reset_nop <= 'h20;
         ff_regb_freq3_ch0_t_zq_stop <= 'h18;
         ff_regb_freq3_ch0_dqsosc_enable <= 'h0;
         ff_regb_freq3_ch0_dqsosc_interval_unit <= 'h0;
         ff_regb_freq3_ch0_dqsosc_interval <= 'h7;
         cfgs_ff_regb_freq3_ch0_mr4_read_interval <= 'h800000;
         ff_regb_freq3_ch0_derated_t_rrd <= 'h4;
         ff_regb_freq3_ch0_derated_t_rp <= 'h5;
         ff_regb_freq3_ch0_derated_t_ras_min <= 'hf;
         ff_regb_freq3_ch0_derated_t_rcd <= 'h5;
         ff_regb_freq3_ch0_derated_t_rc <= 'h14;
         ff_regb_freq3_ch0_derated_t_rcd_write <= 'h5;
         cfgs_ff_regb_freq3_ch0_hw_lp_idle_x32 <= 'h0;
         cfgs_ff_regb_freq3_ch0_dvfsq_enable <= 'h0;
         cfgs_ff_regb_freq3_ch0_pageclose_timer <= 'h0;
         cfgs_ff_regb_freq3_ch0_rdwr_idle_gap <= 'h0;
         cfgs_ff_regb_freq3_ch0_hpr_max_starve <= 'h1;
         cfgs_ff_regb_freq3_ch0_hpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq3_ch0_lpr_max_starve <= 'h7f;
         cfgs_ff_regb_freq3_ch0_lpr_xact_run_length <= 'hf;
         cfgs_ff_regb_freq3_ch0_w_max_starve <= 'h7f;
         cfgs_ff_regb_freq3_ch0_w_xact_run_length <= 'hf;
         ff_regb_freq3_ch0_frequency_ratio <= 'h0;
         cfgs_ff_regb_freq3_ch0_diff_rank_rd_gap <= 'h6;
         cfgs_ff_regb_freq3_ch0_diff_rank_wr_gap <= 'h6;
         cfgs_ff_regb_freq3_ch0_wr2rd_dr <= 'hf;
         cfgs_ff_regb_freq3_ch0_rd2wr_dr <= 'hf;
         cfgs_ff_regb_freq3_ch0_powerdown_to_x32 <= 'h10;
         cfgs_ff_regb_freq3_ch0_selfref_to_x32 <= 'h40;
         cfgs_ff_regb_freq3_ch0_t_pgm_x1_x1024 <= 'h2faf09;
         cfgs_ff_regb_freq3_ch0_t_pgm_x1_sel <= 'h0;
         cfgs_ff_regb_freq3_ch0_t_pgmpst_x32 <= 'h9c5;
         cfgs_ff_regb_freq3_ch0_t_pgm_exit <= 'h18;
         ff_regb_freq3_ch0_wr_link_ecc_enable <= 'h0;
         ff_regb_freq3_ch0_rd_link_ecc_enable <= 'h0;

      end else begin
   //------------------------
   // Register REGB_DDRC_CH0.MSTR0
   //------------------------
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_lpddr4 <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4 +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4] & regb_ddrc_ch0_mstr0_lpddr4_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4 +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4];
         end
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_lpddr5 <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5 +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5] & regb_ddrc_ch0_mstr0_lpddr5_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5 +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5];
         end
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_lpddr5x <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X] & regb_ddrc_ch0_mstr0_lpddr5x_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X +: `REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X];
         end
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_data_bus_width[(`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH +: `REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH] & regb_ddrc_ch0_mstr0_data_bus_width_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH +: `REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH];
         end
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_burst_rdwr[(`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR +: `REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR] & regb_ddrc_ch0_mstr0_burst_rdwr_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR +: `REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR];
         end
         if (rwselect[0] && write_en) begin
            ff_regb_ddrc_ch0_active_ranks[(`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS +: `REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS] & regb_ddrc_ch0_mstr0_active_ranks_mask[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS +: `REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS];
         end
   //------------------------
   // Register REGB_DDRC_CH0.MSTR2
   //------------------------
         if (rwselect[2] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_target_frequency[(`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR2_TARGET_FREQUENCY +: `REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY] & regb_ddrc_ch0_mstr2_target_frequency_mask[`REGB_DDRC_CH0_OFFSET_MSTR2_TARGET_FREQUENCY +: `REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.MSTR4
   //------------------------
         if (rwselect[4] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_wck_on <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_ON +: `REGB_DDRC_CH0_SIZE_MSTR4_WCK_ON] & regb_ddrc_ch0_mstr4_wck_on_mask[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_ON +: `REGB_DDRC_CH0_SIZE_MSTR4_WCK_ON];
            end
         end
         if (rwselect[4] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_wck_suspend_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_SUSPEND_EN +: `REGB_DDRC_CH0_SIZE_MSTR4_WCK_SUSPEND_EN] & regb_ddrc_ch0_mstr4_wck_suspend_en_mask[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_SUSPEND_EN +: `REGB_DDRC_CH0_SIZE_MSTR4_WCK_SUSPEND_EN];
            end
         end
         if (rwselect[4] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_ws_off_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MSTR4_WS_OFF_EN +: `REGB_DDRC_CH0_SIZE_MSTR4_WS_OFF_EN] & regb_ddrc_ch0_mstr4_ws_off_en_mask[`REGB_DDRC_CH0_OFFSET_MSTR4_WS_OFF_EN +: `REGB_DDRC_CH0_SIZE_MSTR4_WS_OFF_EN];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL0
   //------------------------
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_mr_type <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_TYPE +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_TYPE] & regb_ddrc_ch0_mrctrl0_mr_type_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_TYPE +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_TYPE];
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_sw_init_int <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_SW_INIT_INT +: `REGB_DDRC_CH0_SIZE_MRCTRL0_SW_INIT_INT] & regb_ddrc_ch0_mrctrl0_sw_init_int_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_SW_INIT_INT +: `REGB_DDRC_CH0_SIZE_MRCTRL0_SW_INIT_INT];
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_mr_rank[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_RANK +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK] & regb_ddrc_ch0_mrctrl0_mr_rank_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_RANK +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK];
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_mr_addr[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_ADDR +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR] & regb_ddrc_ch0_mrctrl0_mr_addr_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_ADDR +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR];
         end
         if (reg_ddrc_mrr_done_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_mrr_done_clr <= 1'b0;
         end else begin
            if (rwselect[5] && write_en) begin
               ff_regb_ddrc_ch0_mrr_done_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MRR_DONE_CLR +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MRR_DONE_CLR] & regb_ddrc_ch0_mrctrl0_mrr_done_clr_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MRR_DONE_CLR +: `REGB_DDRC_CH0_SIZE_MRCTRL0_MRR_DONE_CLR];
            end
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_dis_mrrw_trfc <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_DIS_MRRW_TRFC +: `REGB_DDRC_CH0_SIZE_MRCTRL0_DIS_MRRW_TRFC] & regb_ddrc_ch0_mrctrl0_dis_mrrw_trfc_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_DIS_MRRW_TRFC +: `REGB_DDRC_CH0_SIZE_MRCTRL0_DIS_MRRW_TRFC];
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_ppr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_EN +: `REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_EN] & regb_ddrc_ch0_mrctrl0_ppr_en_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_EN +: `REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_EN];
         end
         if (rwselect[5] && write_en) begin
            ff_regb_ddrc_ch0_ppr_pgmpst_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_PGMPST_EN +: `REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_PGMPST_EN] & regb_ddrc_ch0_mrctrl0_ppr_pgmpst_en_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_PGMPST_EN +: `REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_PGMPST_EN];
         end
         if (reg_ddrc_mr_wr_ack_pclk) begin
            ff_regb_ddrc_ch0_mr_wr <= 1'b0;
            ff_regb_ddrc_ch0_mr_wr_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_mr_wr_todo & (!ddrc_reg_mr_wr_busy_int)) begin
// ccx_line_begin: ; These lines can be hit if there is a back-to-back request while the operation for the first request is ongoing. However, for mr_wr, this is not the recommended used case and driver should monitor for busy to go low before generating the next second request.
               ff_regb_ddrc_ch0_mr_wr_todo <= 1'b0;
               ff_regb_ddrc_ch0_mr_wr <= ff_regb_ddrc_ch0_mr_wr_saved;
// ccx_line_end
            end else if (rwselect[5] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR] & regb_ddrc_ch0_mrctrl0_mr_wr_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR]) ) begin
               if (ddrc_reg_mr_wr_busy_int) begin
                  ff_regb_ddrc_ch0_mr_wr_todo <= 1'b1;
                  ff_regb_ddrc_ch0_mr_wr_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_mr_wr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR] & regb_ddrc_ch0_mrctrl0_mr_wr_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR];
               end
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL1
   //------------------------
         if (rwselect[6] && write_en) begin
            ff_regb_ddrc_ch0_mr_data[(`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_MRCTRL1_MR_DATA +: `REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA] & regb_ddrc_ch0_mrctrl1_mr_data_mask[`REGB_DDRC_CH0_OFFSET_MRCTRL1_MR_DATA +: `REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL0
   //------------------------
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_derate_enable <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_ENABLE +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_ENABLE] & regb_ddrc_ch0_deratectl0_derate_enable_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_ENABLE +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_ENABLE];
         end
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_lpddr4_refresh_mode <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_LPDDR4_REFRESH_MODE +: `REGB_DDRC_CH0_SIZE_DERATECTL0_LPDDR4_REFRESH_MODE] & regb_ddrc_ch0_deratectl0_lpddr4_refresh_mode_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_LPDDR4_REFRESH_MODE +: `REGB_DDRC_CH0_SIZE_DERATECTL0_LPDDR4_REFRESH_MODE];
         end
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_derate_mr4_pause_fc <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_MR4_PAUSE_FC +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_MR4_PAUSE_FC] & regb_ddrc_ch0_deratectl0_derate_mr4_pause_fc_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_MR4_PAUSE_FC +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_MR4_PAUSE_FC];
         end
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_dis_trefi_x6x8 <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X6X8 +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X6X8] & regb_ddrc_ch0_deratectl0_dis_trefi_x6x8_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X6X8 +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X6X8];
         end
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_dis_trefi_x0125 <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X0125 +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X0125] & regb_ddrc_ch0_deratectl0_dis_trefi_x0125_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X0125 +: `REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X0125];
         end
         if (rwselect[8] && write_en) begin
            ff_regb_ddrc_ch0_use_slow_rm_in_low_temp <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP +: `REGB_DDRC_CH0_SIZE_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP] & regb_ddrc_ch0_deratectl0_use_slow_rm_in_low_temp_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP +: `REGB_DDRC_CH0_SIZE_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL1
   //------------------------
         if (rwselect[9] && write_en) begin
            ff_regb_ddrc_ch0_active_derate_byte_rank0[(`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0 +: `REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0] & regb_ddrc_ch0_deratectl1_active_derate_byte_rank0_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0 +: `REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL2
   //------------------------
         if (rwselect[10] && write_en) begin
            ff_regb_ddrc_ch0_active_derate_byte_rank1[(`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1 +: `REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1] & regb_ddrc_ch0_deratectl2_active_derate_byte_rank1_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1 +: `REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL5
   //------------------------
         if (rwselect[13] && write_en) begin
            cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN] & regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_en_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN];
         end
         if (reg_ddrc_derate_temp_limit_intr_clr_ack_pclk) begin
            cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr <= 1'b0;
         end else begin
            if (rwselect[13] && write_en) begin
               cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR] & regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR];
            end
         end
         if (reg_ddrc_derate_temp_limit_intr_force_ack_pclk) begin
            cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force <= 1'b0;
         end else begin
            if (rwselect[13] && write_en) begin
               cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE] & regb_ddrc_ch0_deratectl5_derate_temp_limit_intr_force_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL6
   //------------------------
         if (rwselect[14] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_derate_mr4_tuf_dis <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATECTL6_DERATE_MR4_TUF_DIS +: `REGB_DDRC_CH0_SIZE_DERATECTL6_DERATE_MR4_TUF_DIS] & regb_ddrc_ch0_deratectl6_derate_mr4_tuf_dis_mask[`REGB_DDRC_CH0_OFFSET_DERATECTL6_DERATE_MR4_TUF_DIS +: `REGB_DDRC_CH0_SIZE_DERATECTL6_DERATE_MR4_TUF_DIS];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGCTL
   //------------------------
         if (rwselect[16] && write_en) begin
            ff_regb_ddrc_ch0_dbg_mr4_rank_sel[(`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DERATEDBGCTL_DBG_MR4_RANK_SEL +: `REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL] & regb_ddrc_ch0_deratedbgctl_dbg_mr4_rank_sel_mask[`REGB_DDRC_CH0_OFFSET_DERATEDBGCTL_DBG_MR4_RANK_SEL +: `REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL];
         end
   //------------------------
   // Register REGB_DDRC_CH0.PWRCTL
   //------------------------
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_selfref_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN] & regb_ddrc_ch0_pwrctl_selfref_en_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_powerdown_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_POWERDOWN_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN] & regb_ddrc_ch0_pwrctl_powerdown_en_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_POWERDOWN_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_en_dfi_dram_clk_disable <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_EN_DFI_DRAM_CLK_DISABLE +: `REGB_DDRC_CH0_SIZE_PWRCTL_EN_DFI_DRAM_CLK_DISABLE] & regb_ddrc_ch0_pwrctl_en_dfi_dram_clk_disable_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_EN_DFI_DRAM_CLK_DISABLE +: `REGB_DDRC_CH0_SIZE_PWRCTL_EN_DFI_DRAM_CLK_DISABLE];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_selfref_sw <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_SW +: `REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_SW] & regb_ddrc_ch0_pwrctl_selfref_sw_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_SW +: `REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_SW];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_stay_in_selfref <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_STAY_IN_SELFREF +: `REGB_DDRC_CH0_SIZE_PWRCTL_STAY_IN_SELFREF] & regb_ddrc_ch0_pwrctl_stay_in_selfref_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_STAY_IN_SELFREF +: `REGB_DDRC_CH0_SIZE_PWRCTL_STAY_IN_SELFREF];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_dis_cam_drain_selfref <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_DIS_CAM_DRAIN_SELFREF +: `REGB_DDRC_CH0_SIZE_PWRCTL_DIS_CAM_DRAIN_SELFREF] & regb_ddrc_ch0_pwrctl_dis_cam_drain_selfref_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_DIS_CAM_DRAIN_SELFREF +: `REGB_DDRC_CH0_SIZE_PWRCTL_DIS_CAM_DRAIN_SELFREF];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_lpddr4_sr_allowed <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_LPDDR4_SR_ALLOWED +: `REGB_DDRC_CH0_SIZE_PWRCTL_LPDDR4_SR_ALLOWED] & regb_ddrc_ch0_pwrctl_lpddr4_sr_allowed_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_LPDDR4_SR_ALLOWED +: `REGB_DDRC_CH0_SIZE_PWRCTL_LPDDR4_SR_ALLOWED];
         end
         if (rwselect[17] && write_en) begin
            ff_regb_ddrc_ch0_dsm_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PWRCTL_DSM_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_DSM_EN] & regb_ddrc_ch0_pwrctl_dsm_en_mask[`REGB_DDRC_CH0_OFFSET_PWRCTL_DSM_EN +: `REGB_DDRC_CH0_SIZE_PWRCTL_DSM_EN];
         end
   //------------------------
   // Register REGB_DDRC_CH0.HWLPCTL
   //------------------------
         if (rwselect[18] && write_en) begin
            ff_regb_ddrc_ch0_hw_lp_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EN +: `REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EN] & regb_ddrc_ch0_hwlpctl_hw_lp_en_mask[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EN +: `REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EN];
         end
         if (rwselect[18] && write_en) begin
            ff_regb_ddrc_ch0_hw_lp_exit_idle_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EXIT_IDLE_EN +: `REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EXIT_IDLE_EN] & regb_ddrc_ch0_hwlpctl_hw_lp_exit_idle_en_mask[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EXIT_IDLE_EN +: `REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EXIT_IDLE_EN];
         end
   //------------------------
   // Register REGB_DDRC_CH0.CLKGATECTL
   //------------------------
         if (rwselect[20] && write_en) begin
            ff_regb_ddrc_ch0_bsm_clk_on[(`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_CLKGATECTL_BSM_CLK_ON +: `REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON] & regb_ddrc_ch0_clkgatectl_bsm_clk_on_mask[`REGB_DDRC_CH0_OFFSET_CLKGATECTL_BSM_CLK_ON +: `REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON];
         end
   //------------------------
   // Register REGB_DDRC_CH0.RFSHMOD0
   //------------------------
         if (rwselect[21] && write_en) begin
            ff_regb_ddrc_ch0_refresh_burst[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_REFRESH_BURST +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST] & regb_ddrc_ch0_rfshmod0_refresh_burst_mask[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_REFRESH_BURST +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST];
         end
         if (rwselect[21] && write_en) begin
            ff_regb_ddrc_ch0_auto_refab_en[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_AUTO_REFAB_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN] & regb_ddrc_ch0_rfshmod0_auto_refab_en_mask[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_AUTO_REFAB_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN];
         end
         if (rwselect[21] && write_en) begin
            ff_regb_ddrc_ch0_per_bank_refresh <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH] & regb_ddrc_ch0_rfshmod0_per_bank_refresh_mask[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH];
         end
         if (rwselect[21] && write_en) begin
            ff_regb_ddrc_ch0_per_bank_refresh_opt_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH_OPT_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH_OPT_EN] & regb_ddrc_ch0_rfshmod0_per_bank_refresh_opt_en_mask[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH_OPT_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH_OPT_EN];
         end
         if (rwselect[21] && write_en) begin
            ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN] & regb_ddrc_ch0_rfshmod0_fixed_crit_refpb_bank_en_mask[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN +: `REGB_DDRC_CH0_SIZE_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN];
         end
   //------------------------
   // Register REGB_DDRC_CH0.RFSHCTL0
   //------------------------
         if (rwselect[23] && write_en) begin
            ff_regb_ddrc_ch0_dis_auto_refresh <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_DIS_AUTO_REFRESH +: `REGB_DDRC_CH0_SIZE_RFSHCTL0_DIS_AUTO_REFRESH] & regb_ddrc_ch0_rfshctl0_dis_auto_refresh_mask[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_DIS_AUTO_REFRESH +: `REGB_DDRC_CH0_SIZE_RFSHCTL0_DIS_AUTO_REFRESH];
         end
         if (rwselect[23] && write_en) begin
            ff_regb_ddrc_ch0_refresh_update_level <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_REFRESH_UPDATE_LEVEL +: `REGB_DDRC_CH0_SIZE_RFSHCTL0_REFRESH_UPDATE_LEVEL] & regb_ddrc_ch0_rfshctl0_refresh_update_level_mask[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_REFRESH_UPDATE_LEVEL +: `REGB_DDRC_CH0_SIZE_RFSHCTL0_REFRESH_UPDATE_LEVEL];
         end
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD0
   //------------------------
         if (rwselect[24] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rfm_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFM_EN +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFM_EN] & regb_ddrc_ch0_rfmmod0_rfm_en_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFM_EN +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFM_EN];
            end
         end
         if (rwselect[24] && write_en) begin
            ff_regb_ddrc_ch0_rfmsbc <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMSBC +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFMSBC] & regb_ddrc_ch0_rfmmod0_rfmsbc_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMSBC +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFMSBC];
         end
         if (rwselect[24] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_raaimt[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAIMT +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT] & regb_ddrc_ch0_rfmmod0_raaimt_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAIMT +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT];
            end
         end
         if (rwselect[24] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_raamult[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAMULT +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT] & regb_ddrc_ch0_rfmmod0_raamult_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAMULT +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT];
            end
         end
         if (rwselect[24] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_raadec[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAADEC +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC] & regb_ddrc_ch0_rfmmod0_raadec_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAADEC +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC];
            end
         end
         if (rwselect[24] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rfmth_rm_thr[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMTH_RM_THR +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR] & regb_ddrc_ch0_rfmmod0_rfmth_rm_thr_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMTH_RM_THR +: `REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD1
   //------------------------
         if (rwselect[25] && write_en) begin
            ff_regb_ddrc_ch0_init_raa_cnt[(`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMMOD1_INIT_RAA_CNT +: `REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT] & regb_ddrc_ch0_rfmmod1_init_raa_cnt_mask[`REGB_DDRC_CH0_OFFSET_RFMMOD1_INIT_RAA_CNT +: `REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT];
         end
   //------------------------
   // Register REGB_DDRC_CH0.RFMCTL
   //------------------------
         if (rwselect[26] && write_en) begin
            ff_regb_ddrc_ch0_dbg_raa_rank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_RANK +: `REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK] & regb_ddrc_ch0_rfmctl_dbg_raa_rank_mask[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_RANK +: `REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK];
         end
         if (rwselect[26] && write_en) begin
            ff_regb_ddrc_ch0_dbg_raa_bg_bank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_BG_BANK +: `REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK] & regb_ddrc_ch0_rfmctl_dbg_raa_bg_bank_mask[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_BG_BANK +: `REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK];
         end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL0
   //------------------------
         if (rwselect[27] && write_en) begin
            ff_regb_ddrc_ch0_zq_resistor_shared <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL0_ZQ_RESISTOR_SHARED +: `REGB_DDRC_CH0_SIZE_ZQCTL0_ZQ_RESISTOR_SHARED] & regb_ddrc_ch0_zqctl0_zq_resistor_shared_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL0_ZQ_RESISTOR_SHARED +: `REGB_DDRC_CH0_SIZE_ZQCTL0_ZQ_RESISTOR_SHARED];
         end
         if (rwselect[27] && write_en) begin
            ff_regb_ddrc_ch0_dis_auto_zq <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL0_DIS_AUTO_ZQ +: `REGB_DDRC_CH0_SIZE_ZQCTL0_DIS_AUTO_ZQ] & regb_ddrc_ch0_zqctl0_dis_auto_zq_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL0_DIS_AUTO_ZQ +: `REGB_DDRC_CH0_SIZE_ZQCTL0_DIS_AUTO_ZQ];
         end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL1
   //------------------------
         if (reg_ddrc_zq_reset_ack_pclk) begin
            ff_regb_ddrc_ch0_zq_reset <= 1'b0;
            ff_regb_ddrc_ch0_zq_reset_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_zq_reset_todo & (!ddrc_reg_zq_reset_busy_int)) begin
               ff_regb_ddrc_ch0_zq_reset_todo <= 1'b0;
               ff_regb_ddrc_ch0_zq_reset <= ff_regb_ddrc_ch0_zq_reset_saved;
            end else if (rwselect[28] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET] & regb_ddrc_ch0_zqctl1_zq_reset_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET]) ) begin
               if (ddrc_reg_zq_reset_busy_int) begin
                  ff_regb_ddrc_ch0_zq_reset_todo <= 1'b1;
                  ff_regb_ddrc_ch0_zq_reset_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_zq_reset <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET] & regb_ddrc_ch0_zqctl1_zq_reset_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET];
               end
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL2
   //------------------------
         if (rwselect[29] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL +: `REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL] & regb_ddrc_ch0_zqctl2_dis_srx_zqcl_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL +: `REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL];
            end
         end
         if (rwselect[29] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl_hwffc <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL_HWFFC +: `REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL_HWFFC] & regb_ddrc_ch0_zqctl2_dis_srx_zqcl_hwffc_mask[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL_HWFFC +: `REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL_HWFFC];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCRUNTIME
   //------------------------
         if (rwselect[30] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dqsosc_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_DQSOSC_RUNTIME +: `REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME] & regb_ddrc_ch0_dqsoscruntime_dqsosc_runtime_mask[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_DQSOSC_RUNTIME +: `REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME];
            end
         end
         if (rwselect[30] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wck2dqo_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_WCK2DQO_RUNTIME +: `REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME] & regb_ddrc_ch0_dqsoscruntime_wck2dqo_runtime_mask[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_WCK2DQO_RUNTIME +: `REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCCFG0
   //------------------------
         if (rwselect[31] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_dqsosc_srx <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DQSOSCCFG0_DIS_DQSOSC_SRX +: `REGB_DDRC_CH0_SIZE_DQSOSCCFG0_DIS_DQSOSC_SRX] & regb_ddrc_ch0_dqsosccfg0_dis_dqsosc_srx_mask[`REGB_DDRC_CH0_OFFSET_DQSOSCCFG0_DIS_DQSOSC_SRX +: `REGB_DDRC_CH0_SIZE_DQSOSCCFG0_DIS_DQSOSC_SRX];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED0
   //------------------------
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_opt_wrecc_collision_flush <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH] & regb_ddrc_ch0_sched0_dis_opt_wrecc_collision_flush_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH];
            end
         end
         if (rwselect[33] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_prefer_write <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_WRITE +: `REGB_DDRC_CH0_SIZE_SCHED0_PREFER_WRITE] & regb_ddrc_ch0_sched0_prefer_write_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_WRITE +: `REGB_DDRC_CH0_SIZE_SCHED0_PREFER_WRITE];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_pageclose <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_PAGECLOSE +: `REGB_DDRC_CH0_SIZE_SCHED0_PAGECLOSE] & regb_ddrc_ch0_sched0_pageclose_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_PAGECLOSE +: `REGB_DDRC_CH0_SIZE_SCHED0_PAGECLOSE];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_opt_wrcam_fill_level <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_WRCAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_WRCAM_FILL_LEVEL] & regb_ddrc_ch0_sched0_opt_wrcam_fill_level_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_WRCAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_WRCAM_FILL_LEVEL];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_act <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_ACT +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_ACT] & regb_ddrc_ch0_sched0_dis_opt_ntt_by_act_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_ACT +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_ACT];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_pre <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_PRE +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_PRE] & regb_ddrc_ch0_sched0_dis_opt_ntt_by_pre_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_PRE +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_PRE];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_autopre_rmw <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_AUTOPRE_RMW +: `REGB_DDRC_CH0_SIZE_SCHED0_AUTOPRE_RMW] & regb_ddrc_ch0_sched0_autopre_rmw_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_AUTOPRE_RMW +: `REGB_DDRC_CH0_SIZE_SCHED0_AUTOPRE_RMW];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_lpr_num_entries[(`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_LPR_NUM_ENTRIES +: `REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES] & regb_ddrc_ch0_sched0_lpr_num_entries_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_LPR_NUM_ENTRIES +: `REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES];
            end
         end
         if (rwselect[33] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_lpddr4_opt_act_timing <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR4_OPT_ACT_TIMING +: `REGB_DDRC_CH0_SIZE_SCHED0_LPDDR4_OPT_ACT_TIMING] & regb_ddrc_ch0_sched0_lpddr4_opt_act_timing_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR4_OPT_ACT_TIMING +: `REGB_DDRC_CH0_SIZE_SCHED0_LPDDR4_OPT_ACT_TIMING];
            end
         end
         if (rwselect[33] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_lpddr5_opt_act_timing <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR5_OPT_ACT_TIMING +: `REGB_DDRC_CH0_SIZE_SCHED0_LPDDR5_OPT_ACT_TIMING] & regb_ddrc_ch0_sched0_lpddr5_opt_act_timing_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR5_OPT_ACT_TIMING +: `REGB_DDRC_CH0_SIZE_SCHED0_LPDDR5_OPT_ACT_TIMING];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_w_starve_free_running <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_W_STARVE_FREE_RUNNING +: `REGB_DDRC_CH0_SIZE_SCHED0_W_STARVE_FREE_RUNNING] & regb_ddrc_ch0_sched0_w_starve_free_running_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_W_STARVE_FREE_RUNNING +: `REGB_DDRC_CH0_SIZE_SCHED0_W_STARVE_FREE_RUNNING];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_opt_act_lat <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_ACT_LAT +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_ACT_LAT] & regb_ddrc_ch0_sched0_opt_act_lat_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_ACT_LAT +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_ACT_LAT];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_prefer_read <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_READ +: `REGB_DDRC_CH0_SIZE_SCHED0_PREFER_READ] & regb_ddrc_ch0_sched0_prefer_read_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_READ +: `REGB_DDRC_CH0_SIZE_SCHED0_PREFER_READ];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_speculative_act <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_SPECULATIVE_ACT +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_SPECULATIVE_ACT] & regb_ddrc_ch0_sched0_dis_speculative_act_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_SPECULATIVE_ACT +: `REGB_DDRC_CH0_SIZE_SCHED0_DIS_SPECULATIVE_ACT];
            end
         end
         if (rwselect[33] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_opt_vprw_sch <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_VPRW_SCH +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_VPRW_SCH] & regb_ddrc_ch0_sched0_opt_vprw_sch_mask[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_VPRW_SCH +: `REGB_DDRC_CH0_SIZE_SCHED0_OPT_VPRW_SCH];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED1
   //------------------------
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_delay_switch_write[(`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_DELAY_SWITCH_WRITE +: `REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE] & regb_ddrc_ch0_sched1_delay_switch_write_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_DELAY_SWITCH_WRITE +: `REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE];
            end
         end
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_visible_window_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_WR +: `REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR] & regb_ddrc_ch0_sched1_visible_window_limit_wr_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_WR +: `REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR];
            end
         end
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_visible_window_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_RD +: `REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD] & regb_ddrc_ch0_sched1_visible_window_limit_rd_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_RD +: `REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD];
            end
         end
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_page_hit_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_WR +: `REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR] & regb_ddrc_ch0_sched1_page_hit_limit_wr_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_WR +: `REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR];
            end
         end
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_page_hit_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_RD +: `REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD] & regb_ddrc_ch0_sched1_page_hit_limit_rd_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_RD +: `REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD];
            end
         end
         if (rwselect[34] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_opt_hit_gt_hpr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED1_OPT_HIT_GT_HPR +: `REGB_DDRC_CH0_SIZE_SCHED1_OPT_HIT_GT_HPR] & regb_ddrc_ch0_sched1_opt_hit_gt_hpr_mask[`REGB_DDRC_CH0_OFFSET_SCHED1_OPT_HIT_GT_HPR +: `REGB_DDRC_CH0_SIZE_SCHED1_OPT_HIT_GT_HPR];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED3
   //------------------------
         if (rwselect[36] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wrcam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_LOWTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH] & regb_ddrc_ch0_sched3_wrcam_lowthresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_LOWTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH];
            end
         end
         if (rwselect[36] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wrcam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_HIGHTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH] & regb_ddrc_ch0_sched3_wrcam_highthresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_HIGHTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH];
            end
         end
         if (rwselect[36] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wr_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED3_WR_PGHIT_NUM_THRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH] & regb_ddrc_ch0_sched3_wr_pghit_num_thresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED3_WR_PGHIT_NUM_THRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH];
            end
         end
         if (rwselect[36] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_rd_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED3_RD_PGHIT_NUM_THRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH] & regb_ddrc_ch0_sched3_rd_pghit_num_thresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED3_RD_PGHIT_NUM_THRESH +: `REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED4
   //------------------------
         if (rwselect[37] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_rd_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_ACT_IDLE_GAP +: `REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP] & regb_ddrc_ch0_sched4_rd_act_idle_gap_mask[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_ACT_IDLE_GAP +: `REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP];
            end
         end
         if (rwselect[37] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wr_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_ACT_IDLE_GAP +: `REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP] & regb_ddrc_ch0_sched4_wr_act_idle_gap_mask[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_ACT_IDLE_GAP +: `REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP];
            end
         end
         if (rwselect[37] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_rd_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_PAGE_EXP_CYCLES +: `REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES] & regb_ddrc_ch0_sched4_rd_page_exp_cycles_mask[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_PAGE_EXP_CYCLES +: `REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES];
            end
         end
         if (rwselect[37] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wr_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_PAGE_EXP_CYCLES +: `REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES] & regb_ddrc_ch0_sched4_wr_page_exp_cycles_mask[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_PAGE_EXP_CYCLES +: `REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SCHED5
   //------------------------
         if (rwselect[38] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wrecc_cam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_LOWTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH] & regb_ddrc_ch0_sched5_wrecc_cam_lowthresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_LOWTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH];
            end
         end
         if (rwselect[38] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_wrecc_cam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_HIGHTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH] & regb_ddrc_ch0_sched5_wrecc_cam_highthresh_mask[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_HIGHTHRESH +: `REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH];
            end
         end
         if (rwselect[38] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_opt_loaded_wrecc_cam_fill_level <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL] & regb_ddrc_ch0_sched5_dis_opt_loaded_wrecc_cam_fill_level_mask[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL];
            end
         end
         if (rwselect[38] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_opt_valid_wrecc_cam_fill_level <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL] & regb_ddrc_ch0_sched5_dis_opt_valid_wrecc_cam_fill_level_mask[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL +: `REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCCTL
   //------------------------
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_hwffc_en[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_EN +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN] & regb_ddrc_ch0_hwffcctl_hwffc_en_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_EN +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_init_fsp <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_FSP +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_FSP] & regb_ddrc_ch0_hwffcctl_init_fsp_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_FSP +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_FSP];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_init_vrcg <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_VRCG +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_VRCG] & regb_ddrc_ch0_hwffcctl_init_vrcg_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_VRCG +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_VRCG];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_target_vrcg <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_TARGET_VRCG +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_TARGET_VRCG] & regb_ddrc_ch0_hwffcctl_target_vrcg_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_TARGET_VRCG +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_TARGET_VRCG];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_skip_mrw_odtvref <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_MRW_ODTVREF +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_MRW_ODTVREF] & regb_ddrc_ch0_hwffcctl_skip_mrw_odtvref_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_MRW_ODTVREF +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_MRW_ODTVREF];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_skip_zq_stop_start <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_ZQ_STOP_START +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_ZQ_STOP_START] & regb_ddrc_ch0_hwffcctl_skip_zq_stop_start_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_ZQ_STOP_START +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_ZQ_STOP_START];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_zq_interval[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_ZQ_INTERVAL +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL] & regb_ddrc_ch0_hwffcctl_zq_interval_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_ZQ_INTERVAL +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL];
         end
         if (rwselect[39] && write_en) begin
            ff_regb_ddrc_ch0_hwffc_mode <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_MODE +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_MODE] & regb_ddrc_ch0_hwffcctl_hwffc_mode_mask[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_MODE +: `REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_MODE];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DFILPCFG0
   //------------------------
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_dfi_lp_en_pd <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_PD +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_PD] & regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_pd_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_PD +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_PD];
         end
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_dfi_lp_en_sr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_SR +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_SR] & regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_sr_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_SR +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_SR];
         end
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_dfi_lp_en_dsm <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DSM +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DSM] & regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_dsm_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DSM +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DSM];
         end
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_dfi_lp_en_data <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DATA +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DATA] & regb_ddrc_ch0_dfilpcfg0_dfi_lp_en_data_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DATA +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DATA];
         end
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_dfi_lp_data_req_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_DATA_REQ_EN +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_DATA_REQ_EN] & regb_ddrc_ch0_dfilpcfg0_dfi_lp_data_req_en_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_DATA_REQ_EN +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_DATA_REQ_EN];
         end
         if (rwselect[48] && write_en) begin
            ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data[(`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA] & regb_ddrc_ch0_dfilpcfg0_extra_gap_for_dfi_lp_data_mask[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA +: `REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DFIUPD0
   //------------------------
         if (rwselect[49] && write_en) begin
            ff_regb_ddrc_ch0_dfi_phyupd_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DFI_PHYUPD_EN +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DFI_PHYUPD_EN] & regb_ddrc_ch0_dfiupd0_dfi_phyupd_en_mask[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DFI_PHYUPD_EN +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DFI_PHYUPD_EN];
         end
         if (rwselect[49] && write_en) begin
            ff_regb_ddrc_ch0_ctrlupd_pre_srx <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIUPD0_CTRLUPD_PRE_SRX +: `REGB_DDRC_CH0_SIZE_DFIUPD0_CTRLUPD_PRE_SRX] & regb_ddrc_ch0_dfiupd0_ctrlupd_pre_srx_mask[`REGB_DDRC_CH0_OFFSET_DFIUPD0_CTRLUPD_PRE_SRX +: `REGB_DDRC_CH0_SIZE_DFIUPD0_CTRLUPD_PRE_SRX];
         end
         if (rwselect[49] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD_SRX +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD_SRX] & regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_srx_mask[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD_SRX +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD_SRX];
            end
         end
         if (rwselect[49] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dis_auto_ctrlupd <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD] & regb_ddrc_ch0_dfiupd0_dis_auto_ctrlupd_mask[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD +: `REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DFIMISC
   //------------------------
         if (rwselect[51] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dfi_init_complete_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_COMPLETE_EN +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_COMPLETE_EN] & regb_ddrc_ch0_dfimisc_dfi_init_complete_en_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_COMPLETE_EN +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_COMPLETE_EN];
            end
         end
         if (rwselect[51] && write_en) begin
            ff_regb_ddrc_ch0_phy_dbi_mode <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_PHY_DBI_MODE +: `REGB_DDRC_CH0_SIZE_DFIMISC_PHY_DBI_MODE] & regb_ddrc_ch0_dfimisc_phy_dbi_mode_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_PHY_DBI_MODE +: `REGB_DDRC_CH0_SIZE_DFIMISC_PHY_DBI_MODE];
         end
         if (rwselect[51] && write_en) begin
            ff_regb_ddrc_ch0_dfi_data_cs_polarity <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_DATA_CS_POLARITY +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_DATA_CS_POLARITY] & regb_ddrc_ch0_dfimisc_dfi_data_cs_polarity_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_DATA_CS_POLARITY +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_DATA_CS_POLARITY];
         end
         if (rwselect[51] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dfi_reset_n <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_RESET_N +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_RESET_N] & regb_ddrc_ch0_dfimisc_dfi_reset_n_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_RESET_N +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_RESET_N];
            end
         end
         if (rwselect[51] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dfi_init_start <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_START +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_START] & regb_ddrc_ch0_dfimisc_dfi_init_start_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_START +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_START];
            end
         end
         if (rwselect[51] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_lp_optimized_write <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_LP_OPTIMIZED_WRITE +: `REGB_DDRC_CH0_SIZE_DFIMISC_LP_OPTIMIZED_WRITE] & regb_ddrc_ch0_dfimisc_lp_optimized_write_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_LP_OPTIMIZED_WRITE +: `REGB_DDRC_CH0_SIZE_DFIMISC_LP_OPTIMIZED_WRITE];
            end
         end
         if (rwselect[51] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dfi_frequency[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQUENCY +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY] & regb_ddrc_ch0_dfimisc_dfi_frequency_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQUENCY +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY];
            end
         end
         if (rwselect[51] && write_en) begin
            ff_regb_ddrc_ch0_dfi_freq_fsp[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQ_FSP +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP] & regb_ddrc_ch0_dfimisc_dfi_freq_fsp_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQ_FSP +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP];
         end
         if (rwselect[51] && write_en) begin
            ff_regb_ddrc_ch0_dfi_channel_mode[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_CHANNEL_MODE +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE] & regb_ddrc_ch0_dfimisc_dfi_channel_mode_mask[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_CHANNEL_MODE +: `REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DFIPHYMSTR
   //------------------------
         if (rwselect[52] && write_en) begin
            ff_regb_ddrc_ch0_dfi_phymstr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_EN +: `REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_EN] & regb_ddrc_ch0_dfiphymstr_dfi_phymstr_en_mask[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_EN +: `REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_EN];
         end
         if (rwselect[52] && write_en) begin
            ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32[(`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32 +: `REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32] & regb_ddrc_ch0_dfiphymstr_dfi_phymstr_blk_ref_x32_mask[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32 +: `REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32];
         end
   //------------------------
   // Register REGB_DDRC_CH0.POISONCFG
   //------------------------
         if (rwselect[57] && write_en) begin
            ff_regb_ddrc_ch0_wr_poison_slverr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_SLVERR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_SLVERR_EN] & regb_ddrc_ch0_poisoncfg_wr_poison_slverr_en_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_SLVERR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_SLVERR_EN];
         end
         if (rwselect[57] && write_en) begin
            ff_regb_ddrc_ch0_wr_poison_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_EN] & regb_ddrc_ch0_poisoncfg_wr_poison_intr_en_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_EN];
         end
         if (reg_ddrc_wr_poison_intr_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_wr_poison_intr_clr <= 1'b0;
         end else begin
            if (rwselect[57] && write_en) begin
               ff_regb_ddrc_ch0_wr_poison_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_CLR +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_CLR] & regb_ddrc_ch0_poisoncfg_wr_poison_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_CLR +: `REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_CLR];
            end
         end
         if (rwselect[57] && write_en) begin
            ff_regb_ddrc_ch0_rd_poison_slverr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_SLVERR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_SLVERR_EN] & regb_ddrc_ch0_poisoncfg_rd_poison_slverr_en_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_SLVERR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_SLVERR_EN];
         end
         if (rwselect[57] && write_en) begin
            ff_regb_ddrc_ch0_rd_poison_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_EN] & regb_ddrc_ch0_poisoncfg_rd_poison_intr_en_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_EN +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_EN];
         end
         if (reg_ddrc_rd_poison_intr_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_poison_intr_clr <= 1'b0;
         end else begin
            if (rwselect[57] && write_en) begin
               ff_regb_ddrc_ch0_rd_poison_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_CLR +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_CLR] & regb_ddrc_ch0_poisoncfg_rd_poison_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_CLR +: `REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_CLR];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG0
   //------------------------
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_mode[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_MODE +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE] & regb_ddrc_ch0_ecccfg0_ecc_mode_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_MODE +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE];
         end
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_ap_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_EN] & regb_ddrc_ch0_ecccfg0_ecc_ap_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_EN];
         end
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_region_remap_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_REMAP_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_REMAP_EN] & regb_ddrc_ch0_ecccfg0_ecc_region_remap_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_REMAP_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_REMAP_EN];
         end
         if (rwselect[58] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_ecc_region_map[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP] & regb_ddrc_ch0_ecccfg0_ecc_region_map_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP];
            end
         end
         if (rwselect[58] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_blk_channel_idle_time_x32[(`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32 +: `REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32] & regb_ddrc_ch0_ecccfg0_blk_channel_idle_time_x32_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32 +: `REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32];
            end
         end
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_ap_err_threshold[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_ERR_THRESHOLD +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD] & regb_ddrc_ch0_ecccfg0_ecc_ap_err_threshold_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_ERR_THRESHOLD +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD];
         end
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_region_map_other <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_OTHER +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_OTHER] & regb_ddrc_ch0_ecccfg0_ecc_region_map_other_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_OTHER +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_OTHER];
         end
         if (rwselect[58] && write_en) begin
            ff_regb_ddrc_ch0_ecc_region_map_granu[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_GRANU +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU] & regb_ddrc_ch0_ecccfg0_ecc_region_map_granu_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_GRANU +: `REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU];
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG1
   //------------------------
         if (rwselect[59] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_data_poison_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_EN] & regb_ddrc_ch0_ecccfg1_data_poison_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_EN];
            end
         end
         if (rwselect[59] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_data_poison_bit <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_BIT +: `REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_BIT] & regb_ddrc_ch0_ecccfg1_data_poison_bit_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_BIT +: `REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_BIT];
            end
         end
         if (rwselect[59] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_region_parity_lock <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_PARITY_LOCK +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_PARITY_LOCK] & regb_ddrc_ch0_ecccfg1_ecc_region_parity_lock_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_PARITY_LOCK +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_PARITY_LOCK];
            end
         end
         if (rwselect[59] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_region_waste_lock <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_WASTE_LOCK +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_WASTE_LOCK] & regb_ddrc_ch0_ecccfg1_ecc_region_waste_lock_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_WASTE_LOCK +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_WASTE_LOCK];
            end
         end
         if (rwselect[59] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_med_ecc_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_MED_ECC_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG1_MED_ECC_EN] & regb_ddrc_ch0_ecccfg1_med_ecc_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_MED_ECC_EN +: `REGB_DDRC_CH0_SIZE_ECCCFG1_MED_ECC_EN];
            end
         end
         if (rwselect[59] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_blk_channel_active_term <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM +: `REGB_DDRC_CH0_SIZE_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM] & regb_ddrc_ch0_ecccfg1_blk_channel_active_term_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM +: `REGB_DDRC_CH0_SIZE_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM];
            end
         end
         if (rwselect[59] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_active_blk_channel[(`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ACTIVE_BLK_CHANNEL +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL] & regb_ddrc_ch0_ecccfg1_active_blk_channel_mask[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ACTIVE_BLK_CHANNEL +: `REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCTL
   //------------------------
         if (reg_ddrc_ecc_corrected_err_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_corrected_err_clr <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_corrected_err_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_CLR] & regb_ddrc_ch0_eccctl_ecc_corrected_err_clr_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_CLR];
            end
         end
         if (reg_ddrc_ecc_uncorrected_err_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_uncorrected_err_clr <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_uncorrected_err_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_CLR] & regb_ddrc_ch0_eccctl_ecc_uncorrected_err_clr_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_CLR];
            end
         end
         if (reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORR_ERR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORR_ERR_CNT_CLR] & regb_ddrc_ch0_eccctl_ecc_corr_err_cnt_clr_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORR_ERR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORR_ERR_CNT_CLR];
            end
         end
         if (reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORR_ERR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORR_ERR_CNT_CLR] & regb_ddrc_ch0_eccctl_ecc_uncorr_err_cnt_clr_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORR_ERR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORR_ERR_CNT_CLR];
            end
         end
         if (reg_ddrc_ecc_ap_err_intr_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_ap_err_intr_clr <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_ap_err_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_CLR] & regb_ddrc_ch0_eccctl_ecc_ap_err_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_CLR];
            end
         end
         if (rwselect[60] && write_en) begin
            ff_regb_ddrc_ch0_ecc_corrected_err_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_EN] & regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_EN];
         end
         if (rwselect[60] && write_en) begin
            ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN] & regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN];
         end
         if (rwselect[60] && write_en) begin
            ff_regb_ddrc_ch0_ecc_ap_err_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_EN] & regb_ddrc_ch0_eccctl_ecc_ap_err_intr_en_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_EN +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_EN];
         end
         if (reg_ddrc_ecc_corrected_err_intr_force_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_corrected_err_intr_force <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_corrected_err_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE] & regb_ddrc_ch0_eccctl_ecc_corrected_err_intr_force_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE];
            end
         end
         if (reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE] & regb_ddrc_ch0_eccctl_ecc_uncorrected_err_intr_force_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE];
            end
         end
         if (reg_ddrc_ecc_ap_err_intr_force_ack_pclk) begin
            ff_regb_ddrc_ch0_ecc_ap_err_intr_force <= 1'b0;
         end else begin
            if (rwselect[60] && write_en) begin
               ff_regb_ddrc_ch0_ecc_ap_err_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_FORCE] & regb_ddrc_ch0_eccctl_ecc_ap_err_intr_force_mask[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_FORCE];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR0
   //------------------------
         if (rwselect[61] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_col[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_COL +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL] & regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_col_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_COL +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL];
            end
         end
         if (rwselect[61] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_rank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_RANK +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK] & regb_ddrc_ch0_eccpoisonaddr0_ecc_poison_rank_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_RANK +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR1
   //------------------------
         if (rwselect[62] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_row[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_ROW +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW] & regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_row_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_ROW +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW];
            end
         end
         if (rwselect[62] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_bank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BANK +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK] & regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bank_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BANK +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK];
            end
         end
         if (rwselect[62] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_bg[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BG +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG] & regb_ddrc_ch0_eccpoisonaddr1_ecc_poison_bg_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BG +: `REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT0
   //------------------------
         if (rwselect[64] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_data_31_0[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT0_ECC_POISON_DATA_31_0 +: `REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0] & regb_ddrc_ch0_eccpoisonpat0_ecc_poison_data_31_0_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT0_ECC_POISON_DATA_31_0 +: `REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT2
   //------------------------
         if (rwselect[66] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_ecc_poison_data_71_64[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT2_ECC_POISON_DATA_71_64 +: `REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64] & regb_ddrc_ch0_eccpoisonpat2_ecc_poison_data_71_64_mask[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT2_ECC_POISON_DATA_71_64 +: `REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCTL1
   //------------------------
         if (rwselect[84] && write_en) begin
            ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_en_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN];
         end
         if (reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR];
            end
         end
         if (reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_cnt_clr_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR];
            end
         end
         if (reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_corr_intr_force_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE];
            end
         end
         if (rwselect[84] && write_en) begin
            ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_en_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN];
         end
         if (reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_clr_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR];
            end
         end
         if (reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_cnt_clr_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR];
            end
         end
         if (reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk) begin
            ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force <= 1'b0;
         end else begin
            if (rwselect[84] && write_en) begin
               ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE] & regb_ddrc_ch0_lnkeccctl1_rd_link_ecc_uncorr_intr_force_mask[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE +: `REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONCTL0
   //------------------------
         if (rwselect[85] && write_en) begin
            ff_regb_ddrc_ch0_linkecc_poison_inject_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN] & regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_inject_en_mask[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN];
         end
         if (rwselect[85] && write_en) begin
            ff_regb_ddrc_ch0_linkecc_poison_type <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_TYPE +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_TYPE] & regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_type_mask[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_TYPE +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_TYPE];
         end
         if (rwselect[85] && write_en) begin
            ff_regb_ddrc_ch0_linkecc_poison_rw <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_RW +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_RW] & regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_rw_mask[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_RW +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_RW];
         end
         if (rwselect[85] && write_en) begin
            ff_regb_ddrc_ch0_linkecc_poison_dmi_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL] & regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_dmi_sel_mask[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL];
         end
         if (rwselect[85] && write_en) begin
            ff_regb_ddrc_ch0_linkecc_poison_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL] & regb_ddrc_ch0_lnkeccpoisonctl0_linkecc_poison_byte_sel_mask[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL];
         end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCINDEX
   //------------------------
         if (rwselect[86] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rd_link_ecc_err_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL] & regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_byte_sel_mask[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL];
            end
         end
         if (rwselect[86] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rd_link_ecc_err_rank_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL] & regb_ddrc_ch0_lnkeccindex_rd_link_ecc_err_rank_sel_mask[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL +: `REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL0
   //------------------------
         if (rwselect[129] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_wc <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_WC +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_WC] & regb_ddrc_ch0_opctrl0_dis_wc_mask[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_WC +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_WC];
            end
         end
         if (rwselect[129] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_max_rank_rd_opt <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_RD_OPT +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_RD_OPT] & regb_ddrc_ch0_opctrl0_dis_max_rank_rd_opt_mask[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_RD_OPT +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_RD_OPT];
            end
         end
         if (rwselect[129] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_dis_max_rank_wr_opt <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_WR_OPT +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_WR_OPT] & regb_ddrc_ch0_opctrl0_dis_max_rank_wr_opt_mask[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_WR_OPT +: `REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_WR_OPT];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL1
   //------------------------
         if (rwselect[130] && write_en) begin
            ff_regb_ddrc_ch0_dis_dq <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_DQ +: `REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_DQ] & regb_ddrc_ch0_opctrl1_dis_dq_mask[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_DQ +: `REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_DQ];
         end
         if (rwselect[130] && write_en) begin
            ff_regb_ddrc_ch0_dis_hif <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_HIF +: `REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_HIF] & regb_ddrc_ch0_opctrl1_dis_hif_mask[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_HIF +: `REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_HIF];
         end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCMD
   //------------------------
         if (reg_ddrc_zq_calib_short_ack_pclk) begin
            ff_regb_ddrc_ch0_zq_calib_short <= 1'b0;
            ff_regb_ddrc_ch0_zq_calib_short_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_zq_calib_short_todo & (!ddrc_reg_zq_calib_short_busy_int)) begin
               ff_regb_ddrc_ch0_zq_calib_short_todo <= 1'b0;
               ff_regb_ddrc_ch0_zq_calib_short <= ff_regb_ddrc_ch0_zq_calib_short_saved;
            end else if (rwselect[131] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT] & regb_ddrc_ch0_opctrlcmd_zq_calib_short_mask[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT]) ) begin
               if (ddrc_reg_zq_calib_short_busy_int) begin
                  ff_regb_ddrc_ch0_zq_calib_short_todo <= 1'b1;
                  ff_regb_ddrc_ch0_zq_calib_short_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_zq_calib_short <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT] & regb_ddrc_ch0_opctrlcmd_zq_calib_short_mask[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT];
               end
            end
         end
         if (reg_ddrc_ctrlupd_ack_pclk) begin
            ff_regb_ddrc_ch0_ctrlupd <= 1'b0;
            ff_regb_ddrc_ch0_ctrlupd_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_ctrlupd_todo & (!ddrc_reg_ctrlupd_busy_int)) begin
               ff_regb_ddrc_ch0_ctrlupd_todo <= 1'b0;
               ff_regb_ddrc_ch0_ctrlupd <= ff_regb_ddrc_ch0_ctrlupd_saved;
            end else if (rwselect[131] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD] & regb_ddrc_ch0_opctrlcmd_ctrlupd_mask[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD]) ) begin
               if (ddrc_reg_ctrlupd_busy_int) begin
                  ff_regb_ddrc_ch0_ctrlupd_todo <= 1'b1;
                  ff_regb_ddrc_ch0_ctrlupd_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_ctrlupd <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD] & regb_ddrc_ch0_opctrlcmd_ctrlupd_mask[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD];
               end
            end
         end
         if (rwselect[131] && write_en) begin
            ff_regb_ddrc_ch0_ctrlupd_burst <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD_BURST +: `REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD_BURST] & regb_ddrc_ch0_opctrlcmd_ctrlupd_burst_mask[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD_BURST +: `REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD_BURST];
         end
   //------------------------
   // Register REGB_DDRC_CH0.OPREFCTRL0
   //------------------------
         if (reg_ddrc_rank0_refresh_ack_pclk) begin
            ff_regb_ddrc_ch0_rank0_refresh <= 1'b0;
            ff_regb_ddrc_ch0_rank0_refresh_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_rank0_refresh_todo & (!ddrc_reg_rank0_refresh_busy_int)) begin
               ff_regb_ddrc_ch0_rank0_refresh_todo <= 1'b0;
               ff_regb_ddrc_ch0_rank0_refresh <= ff_regb_ddrc_ch0_rank0_refresh_saved;
            end else if (rwselect[132] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH] & regb_ddrc_ch0_oprefctrl0_rank0_refresh_mask[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH]) ) begin
               if (ddrc_reg_rank0_refresh_busy_int) begin
                  ff_regb_ddrc_ch0_rank0_refresh_todo <= 1'b1;
                  ff_regb_ddrc_ch0_rank0_refresh_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_rank0_refresh <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH] & regb_ddrc_ch0_oprefctrl0_rank0_refresh_mask[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH];
               end
            end
         end
         if (reg_ddrc_rank1_refresh_ack_pclk) begin
            ff_regb_ddrc_ch0_rank1_refresh <= 1'b0;
            ff_regb_ddrc_ch0_rank1_refresh_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_rank1_refresh_todo & (!ddrc_reg_rank1_refresh_busy_int)) begin
               ff_regb_ddrc_ch0_rank1_refresh_todo <= 1'b0;
               ff_regb_ddrc_ch0_rank1_refresh <= ff_regb_ddrc_ch0_rank1_refresh_saved;
            end else if (rwselect[132] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH] & regb_ddrc_ch0_oprefctrl0_rank1_refresh_mask[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH]) ) begin
               if (ddrc_reg_rank1_refresh_busy_int) begin
                  ff_regb_ddrc_ch0_rank1_refresh_todo <= 1'b1;
                  ff_regb_ddrc_ch0_rank1_refresh_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_rank1_refresh <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH] & regb_ddrc_ch0_oprefctrl0_rank1_refresh_mask[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH];
               end
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SWCTL
   //------------------------
         if (rwselect[136] && write_en) begin
            cfgs_ff_regb_ddrc_ch0_sw_done <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SWCTL_SW_DONE +: `REGB_DDRC_CH0_SIZE_SWCTL_SW_DONE] & regb_ddrc_ch0_swctl_sw_done_mask[`REGB_DDRC_CH0_OFFSET_SWCTL_SW_DONE +: `REGB_DDRC_CH0_SIZE_SWCTL_SW_DONE];
         end
   //------------------------
   // Register REGB_DDRC_CH0.RANKCTL
   //------------------------
         if (rwselect[139] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_max_rank_rd[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_RD +: `REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD] & regb_ddrc_ch0_rankctl_max_rank_rd_mask[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_RD +: `REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD];
            end
         end
         if (rwselect[139] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_ddrc_ch0_max_rank_wr[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_WR +: `REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR] & regb_ddrc_ch0_rankctl_max_rank_wr_mask[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_WR +: `REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.DBICTL
   //------------------------
         if (rwselect[140] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_dm_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DBICTL_DM_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_DM_EN] & regb_ddrc_ch0_dbictl_dm_en_mask[`REGB_DDRC_CH0_OFFSET_DBICTL_DM_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_DM_EN];
            end
         end
         if (rwselect[140] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_wr_dbi_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DBICTL_WR_DBI_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_WR_DBI_EN] & regb_ddrc_ch0_dbictl_wr_dbi_en_mask[`REGB_DDRC_CH0_OFFSET_DBICTL_WR_DBI_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_WR_DBI_EN];
            end
         end
         if (rwselect[140] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rd_dbi_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DBICTL_RD_DBI_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_RD_DBI_EN] & regb_ddrc_ch0_dbictl_rd_dbi_en_mask[`REGB_DDRC_CH0_OFFSET_DBICTL_RD_DBI_EN +: `REGB_DDRC_CH0_SIZE_DBICTL_RD_DBI_EN];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.ODTMAP
   //------------------------
         if (rwselect[141] && write_en) begin
            ff_regb_ddrc_ch0_rank0_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_WR_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT] & regb_ddrc_ch0_odtmap_rank0_wr_odt_mask[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_WR_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT];
         end
         if (rwselect[141] && write_en) begin
            ff_regb_ddrc_ch0_rank0_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_RD_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT] & regb_ddrc_ch0_odtmap_rank0_rd_odt_mask[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_RD_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT];
         end
         if (rwselect[141] && write_en) begin
            ff_regb_ddrc_ch0_rank1_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_WR_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT] & regb_ddrc_ch0_odtmap_rank1_wr_odt_mask[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_WR_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT];
         end
         if (rwselect[141] && write_en) begin
            ff_regb_ddrc_ch0_rank1_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_RD_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT] & regb_ddrc_ch0_odtmap_rank1_rd_odt_mask[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_RD_ODT +: `REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT];
         end
   //------------------------
   // Register REGB_DDRC_CH0.DATACTL0
   //------------------------
         if (rwselect[142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_rd_data_copy_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DATACTL0_RD_DATA_COPY_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_RD_DATA_COPY_EN] & regb_ddrc_ch0_datactl0_rd_data_copy_en_mask[`REGB_DDRC_CH0_OFFSET_DATACTL0_RD_DATA_COPY_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_RD_DATA_COPY_EN];
            end
         end
         if (rwselect[142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_wr_data_copy_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_COPY_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_COPY_EN] & regb_ddrc_ch0_datactl0_wr_data_copy_en_mask[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_COPY_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_COPY_EN];
            end
         end
         if (rwselect[142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_wr_data_x_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_X_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_X_EN] & regb_ddrc_ch0_datactl0_wr_data_x_en_mask[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_X_EN +: `REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_X_EN];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.SWCTLSTATIC
   //------------------------
         if (rwselect[143] && write_en) begin
            cfgs_ff_regb_ddrc_ch0_sw_static_unlock <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_SWCTLSTATIC_SW_STATIC_UNLOCK +: `REGB_DDRC_CH0_SIZE_SWCTLSTATIC_SW_STATIC_UNLOCK] & regb_ddrc_ch0_swctlstatic_sw_static_unlock_mask[`REGB_DDRC_CH0_OFFSET_SWCTLSTATIC_SW_STATIC_UNLOCK +: `REGB_DDRC_CH0_SIZE_SWCTLSTATIC_SW_STATIC_UNLOCK];
         end
   //------------------------
   // Register REGB_DDRC_CH0.CGCTL
   //------------------------
         if (rwselect[144] && write_en) begin
            ff_regb_ddrc_ch0_force_clk_te_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_TE_EN +: `REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_TE_EN] & regb_ddrc_ch0_cgctl_force_clk_te_en_mask[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_TE_EN +: `REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_TE_EN];
         end
         if (rwselect[144] && write_en) begin
            ff_regb_ddrc_ch0_force_clk_arb_en <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_ARB_EN +: `REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_ARB_EN] & regb_ddrc_ch0_cgctl_force_clk_arb_en_mask[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_ARB_EN +: `REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_ARB_EN];
         end
   //------------------------
   // Register REGB_DDRC_CH0.INITTMG0
   //------------------------
         if (rwselect[145] && write_en) begin
            ff_regb_ddrc_ch0_pre_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_INITTMG0_PRE_CKE_X1024 +: `REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024] & regb_ddrc_ch0_inittmg0_pre_cke_x1024_mask[`REGB_DDRC_CH0_OFFSET_INITTMG0_PRE_CKE_X1024 +: `REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024];
         end
         if (rwselect[145] && write_en) begin
            ff_regb_ddrc_ch0_post_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_INITTMG0_POST_CKE_X1024 +: `REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024] & regb_ddrc_ch0_inittmg0_post_cke_x1024_mask[`REGB_DDRC_CH0_OFFSET_INITTMG0_POST_CKE_X1024 +: `REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024];
         end
         if (rwselect[145] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_ddrc_ch0_skip_dram_init[(`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_INITTMG0_SKIP_DRAM_INIT +: `REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT] & regb_ddrc_ch0_inittmg0_skip_dram_init_mask[`REGB_DDRC_CH0_OFFSET_INITTMG0_SKIP_DRAM_INIT +: `REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT];
            end
         end
   //------------------------
   // Register REGB_DDRC_CH0.PPT2CTRL0
   //------------------------
         if (rwselect[150] && write_en) begin
            ff_regb_ddrc_ch0_ppt2_burst_num[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST_NUM +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM] & regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_num_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST_NUM +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM];
         end
         if (rwselect[150] && write_en) begin
            ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi0[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0 +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0] & regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi0_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0 +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0];
         end
         if (rwselect[150] && write_en) begin
            ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi1[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1) -1:0] <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1 +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1] & regb_ddrc_ch0_ppt2ctrl0_ppt2_ctrlupd_num_dfi1_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1 +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1];
         end
         if (reg_ddrc_ppt2_burst_ack_pclk) begin
            ff_regb_ddrc_ch0_ppt2_burst <= 1'b0;
            ff_regb_ddrc_ch0_ppt2_burst_saved <= 1'b0;
         end else begin
            if (ff_regb_ddrc_ch0_ppt2_burst_todo & (!ddrc_reg_ppt2_burst_busy_int)) begin
               ff_regb_ddrc_ch0_ppt2_burst_todo <= 1'b0;
               ff_regb_ddrc_ch0_ppt2_burst <= ff_regb_ddrc_ch0_ppt2_burst_saved;
            end else if (rwselect[150] & store_rqst & (apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST] & regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST]) ) begin
               if (ddrc_reg_ppt2_burst_busy_int) begin
                  ff_regb_ddrc_ch0_ppt2_burst_todo <= 1'b1;
                  ff_regb_ddrc_ch0_ppt2_burst_saved <= 1'b1;
               end else begin
                  ff_regb_ddrc_ch0_ppt2_burst <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST] & regb_ddrc_ch0_ppt2ctrl0_ppt2_burst_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST];
               end
            end
         end
         if (rwselect[150] && write_en) begin
            ff_regb_ddrc_ch0_ppt2_wait_ref <= apb_data_expanded[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_WAIT_REF +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_WAIT_REF] & regb_ddrc_ch0_ppt2ctrl0_ppt2_wait_ref_mask[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_WAIT_REF +: `REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_WAIT_REF];
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP1
   //------------------------
         if (rwselect[236] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_cs_bit0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP1_ADDRMAP_CS_BIT0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0] & regb_addr_map0_addrmap1_addrmap_cs_bit0_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP1_ADDRMAP_CS_BIT0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP3
   //------------------------
         if (rwselect[238] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_bank_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0] & regb_addr_map0_addrmap3_addrmap_bank_b0_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0];
            end
         end
         if (rwselect[238] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_bank_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1] & regb_addr_map0_addrmap3_addrmap_bank_b1_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1];
            end
         end
         if (rwselect[238] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_bank_b2[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B2 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2] & regb_addr_map0_addrmap3_addrmap_bank_b2_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B2 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP4
   //------------------------
         if (rwselect[239] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_bg_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0] & regb_addr_map0_addrmap4_addrmap_bg_b0_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0];
            end
         end
         if (rwselect[239] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_bg_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1] & regb_addr_map0_addrmap4_addrmap_bg_b1_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP5
   //------------------------
         if (rwselect[240] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b7[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B7 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7] & regb_addr_map0_addrmap5_addrmap_col_b7_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B7 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7];
            end
         end
         if (rwselect[240] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b8[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B8 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8] & regb_addr_map0_addrmap5_addrmap_col_b8_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B8 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8];
            end
         end
         if (rwselect[240] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b9[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B9 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9] & regb_addr_map0_addrmap5_addrmap_col_b9_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B9 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9];
            end
         end
         if (rwselect[240] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b10[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B10 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10] & regb_addr_map0_addrmap5_addrmap_col_b10_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B10 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP6
   //------------------------
         if (rwselect[241] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b3[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B3 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3] & regb_addr_map0_addrmap6_addrmap_col_b3_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B3 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3];
            end
         end
         if (rwselect[241] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b4[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B4 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4] & regb_addr_map0_addrmap6_addrmap_col_b4_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B4 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4];
            end
         end
         if (rwselect[241] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b5[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B5 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5] & regb_addr_map0_addrmap6_addrmap_col_b5_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B5 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5];
            end
         end
         if (rwselect[241] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_col_b6[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B6 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6] & regb_addr_map0_addrmap6_addrmap_col_b6_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B6 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP7
   //------------------------
         if (rwselect[242] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b14[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B14 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14] & regb_addr_map0_addrmap7_addrmap_row_b14_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B14 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14];
            end
         end
         if (rwselect[242] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b15[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B15 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15] & regb_addr_map0_addrmap7_addrmap_row_b15_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B15 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15];
            end
         end
         if (rwselect[242] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b16[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B16 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16] & regb_addr_map0_addrmap7_addrmap_row_b16_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B16 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16];
            end
         end
         if (rwselect[242] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b17[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B17 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17] & regb_addr_map0_addrmap7_addrmap_row_b17_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B17 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP8
   //------------------------
         if (rwselect[243] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b10[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B10 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10] & regb_addr_map0_addrmap8_addrmap_row_b10_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B10 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10];
            end
         end
         if (rwselect[243] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b11[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B11 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11] & regb_addr_map0_addrmap8_addrmap_row_b11_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B11 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11];
            end
         end
         if (rwselect[243] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b12[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B12 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12] & regb_addr_map0_addrmap8_addrmap_row_b12_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B12 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12];
            end
         end
         if (rwselect[243] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b13[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B13 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13] & regb_addr_map0_addrmap8_addrmap_row_b13_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B13 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP9
   //------------------------
         if (rwselect[244] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b6[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B6 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6] & regb_addr_map0_addrmap9_addrmap_row_b6_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B6 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6];
            end
         end
         if (rwselect[244] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b7[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B7 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7] & regb_addr_map0_addrmap9_addrmap_row_b7_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B7 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7];
            end
         end
         if (rwselect[244] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b8[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B8 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8] & regb_addr_map0_addrmap9_addrmap_row_b8_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B8 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8];
            end
         end
         if (rwselect[244] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b9[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B9 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9] & regb_addr_map0_addrmap9_addrmap_row_b9_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B9 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP10
   //------------------------
         if (rwselect[245] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b2[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B2 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2] & regb_addr_map0_addrmap10_addrmap_row_b2_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B2 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2];
            end
         end
         if (rwselect[245] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b3[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B3 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3] & regb_addr_map0_addrmap10_addrmap_row_b3_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B3 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3];
            end
         end
         if (rwselect[245] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b4[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B4 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4] & regb_addr_map0_addrmap10_addrmap_row_b4_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B4 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4];
            end
         end
         if (rwselect[245] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b5[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B5 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5] & regb_addr_map0_addrmap10_addrmap_row_b5_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B5 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP11
   //------------------------
         if (rwselect[246] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0] & regb_addr_map0_addrmap11_addrmap_row_b0_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B0 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0];
            end
         end
         if (rwselect[246] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_addr_map0_addrmap_row_b1[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1] & regb_addr_map0_addrmap11_addrmap_row_b1_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B1 +: `REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1];
            end
         end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP12
   //------------------------
         if (rwselect[247] && write_en) begin
            ff_regb_addr_map0_nonbinary_device_density[(`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY) -1:0] <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_NONBINARY_DEVICE_DENSITY +: `REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY] & regb_addr_map0_addrmap12_nonbinary_device_density_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_NONBINARY_DEVICE_DENSITY +: `REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY];
         end
         if (rwselect[247] && write_en) begin
            ff_regb_addr_map0_bank_hash_en <= apb_data_expanded[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_BANK_HASH_EN +: `REGB_ADDR_MAP0_SIZE_ADDRMAP12_BANK_HASH_EN] & regb_addr_map0_addrmap12_bank_hash_en_mask[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_BANK_HASH_EN +: `REGB_ADDR_MAP0_SIZE_ADDRMAP12_BANK_HASH_EN];
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCCFG
   //------------------------
         if (rwselect[261] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_go2critical_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCCFG_GO2CRITICAL_EN +: `REGB_ARB_PORT0_SIZE_PCCFG_GO2CRITICAL_EN] & regb_arb_port0_pccfg_go2critical_en_mask[`REGB_ARB_PORT0_OFFSET_PCCFG_GO2CRITICAL_EN +: `REGB_ARB_PORT0_SIZE_PCCFG_GO2CRITICAL_EN];
            end
         end
         if (rwselect[261] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_pagematch_limit <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCCFG_PAGEMATCH_LIMIT +: `REGB_ARB_PORT0_SIZE_PCCFG_PAGEMATCH_LIMIT] & regb_arb_port0_pccfg_pagematch_limit_mask[`REGB_ARB_PORT0_OFFSET_PCCFG_PAGEMATCH_LIMIT +: `REGB_ARB_PORT0_SIZE_PCCFG_PAGEMATCH_LIMIT];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGR
   //------------------------
         if (rwselect[262] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rd_port_priority[(`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PRIORITY +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY] & regb_arb_port0_pcfgr_rd_port_priority_mask[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PRIORITY +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY];
            end
         end
         if (rwselect[262] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rd_port_aging_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_AGING_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_AGING_EN] & regb_arb_port0_pcfgr_rd_port_aging_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_AGING_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_AGING_EN];
            end
         end
         if (rwselect[262] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rd_port_urgent_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_URGENT_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_URGENT_EN] & regb_arb_port0_pcfgr_rd_port_urgent_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_URGENT_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_URGENT_EN];
            end
         end
         if (rwselect[262] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rd_port_pagematch_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PAGEMATCH_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PAGEMATCH_EN] & regb_arb_port0_pcfgr_rd_port_pagematch_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PAGEMATCH_EN +: `REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PAGEMATCH_EN];
            end
         end
         if (rwselect[262] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rrb_lock_threshold[(`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGR_RRB_LOCK_THRESHOLD +: `REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD] & regb_arb_port0_pcfgr_rrb_lock_threshold_mask[`REGB_ARB_PORT0_OFFSET_PCFGR_RRB_LOCK_THRESHOLD +: `REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGW
   //------------------------
         if (rwselect[263] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wr_port_priority[(`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PRIORITY +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY] & regb_arb_port0_pcfgw_wr_port_priority_mask[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PRIORITY +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY];
            end
         end
         if (rwselect[263] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wr_port_aging_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_AGING_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_AGING_EN] & regb_arb_port0_pcfgw_wr_port_aging_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_AGING_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_AGING_EN];
            end
         end
         if (rwselect[263] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wr_port_urgent_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_URGENT_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_URGENT_EN] & regb_arb_port0_pcfgw_wr_port_urgent_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_URGENT_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_URGENT_EN];
            end
         end
         if (rwselect[263] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wr_port_pagematch_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PAGEMATCH_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PAGEMATCH_EN] & regb_arb_port0_pcfgw_wr_port_pagematch_en_mask[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PAGEMATCH_EN +: `REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PAGEMATCH_EN];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCTRL
   //------------------------
         if (rwselect[296] && write_en) begin
            ff_regb_arb_port0_port_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN +: `REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN] & regb_arb_port0_pctrl_port_en_mask[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN +: `REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN];
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS0
   //------------------------
         if (rwselect[297] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_rqos_map_level1[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL1 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1] & regb_arb_port0_pcfgqos0_rqos_map_level1_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL1 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1];
            end
         end
         if (rwselect[297] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_rqos_map_level2[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL2 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2] & regb_arb_port0_pcfgqos0_rqos_map_level2_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL2 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2];
            end
         end
         if (rwselect[297] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_rqos_map_region0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION0 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0] & regb_arb_port0_pcfgqos0_rqos_map_region0_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION0 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0];
            end
         end
         if (rwselect[297] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_rqos_map_region1[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION1 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1] & regb_arb_port0_pcfgqos0_rqos_map_region1_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION1 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1];
            end
         end
         if (rwselect[297] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_rqos_map_region2[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION2 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2] & regb_arb_port0_pcfgqos0_rqos_map_region2_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION2 +: `REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS1
   //------------------------
         if (rwselect[298] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rqos_map_timeoutb[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTB +: `REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB] & regb_arb_port0_pcfgqos1_rqos_map_timeoutb_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTB +: `REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB];
            end
         end
         if (rwselect[298] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_rqos_map_timeoutr[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTR +: `REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR] & regb_arb_port0_pcfgqos1_rqos_map_timeoutr_mask[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTR +: `REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS0
   //------------------------
         if (rwselect[299] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_wqos_map_level1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1] & regb_arb_port0_pcfgwqos0_wqos_map_level1_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1];
            end
         end
         if (rwselect[299] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_wqos_map_level2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2] & regb_arb_port0_pcfgwqos0_wqos_map_level2_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2];
            end
         end
         if (rwselect[299] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_wqos_map_region0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION0 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0] & regb_arb_port0_pcfgwqos0_wqos_map_region0_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION0 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0];
            end
         end
         if (rwselect[299] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_wqos_map_region1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1] & regb_arb_port0_pcfgwqos0_wqos_map_region1_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1];
            end
         end
         if (rwselect[299] && write_en) begin
            if (quasi_dyn_wr_en_aclk_0 == 1'b0) begin // quasi dynamic write enable @aclk_0
               cfgs_ff_regb_arb_port0_wqos_map_region2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2] & regb_arb_port0_pcfgwqos0_wqos_map_region2_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS1
   //------------------------
         if (rwselect[300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wqos_map_timeout1[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1] & regb_arb_port0_pcfgwqos1_wqos_map_timeout1_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT1 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1];
            end
         end
         if (rwselect[300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_arb_port0_wqos_map_timeout2[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2] & regb_arb_port0_pcfgwqos1_wqos_map_timeout2_mask[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT2 +: `REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2];
            end
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRCTL
   //------------------------
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_en <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_EN +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_EN] & regb_arb_port0_sbrctl_scrub_en_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_EN +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_EN];
         end
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_during_lowpower <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_DURING_LOWPOWER +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_DURING_LOWPOWER] & regb_arb_port0_sbrctl_scrub_during_lowpower_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_DURING_LOWPOWER +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_DURING_LOWPOWER];
         end
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_burst_length_nm[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_NM +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM] & regb_arb_port0_sbrctl_scrub_burst_length_nm_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_NM +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM];
         end
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_interval[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_INTERVAL +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL] & regb_arb_port0_sbrctl_scrub_interval_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_INTERVAL +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL];
         end
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_cmd_type[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_CMD_TYPE +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE] & regb_arb_port0_sbrctl_scrub_cmd_type_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_CMD_TYPE +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE];
         end
         if (rwselect[309] && write_en) begin
            ff_regb_arb_port0_scrub_burst_length_lp[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_LP +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP] & regb_arb_port0_sbrctl_scrub_burst_length_lp_mask[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_LP +: `REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP];
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRWDATA0
   //------------------------
         if (rwselect[310] && write_en) begin
            ff_regb_arb_port0_scrub_pattern0[(`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRWDATA0_SCRUB_PATTERN0 +: `REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0] & regb_arb_port0_sbrwdata0_scrub_pattern0_mask[`REGB_ARB_PORT0_OFFSET_SBRWDATA0_SCRUB_PATTERN0 +: `REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0];
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART0
   //------------------------
         if (rwselect[312] && write_en) begin
            ff_regb_arb_port0_sbr_address_start_mask_0[(`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRSTART0_SBR_ADDRESS_START_MASK_0 +: `REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0] & regb_arb_port0_sbrstart0_sbr_address_start_mask_0_mask[`REGB_ARB_PORT0_OFFSET_SBRSTART0_SBR_ADDRESS_START_MASK_0 +: `REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0];
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART1
   //------------------------
         if (rwselect[313] && write_en) begin
            ff_regb_arb_port0_sbr_address_start_mask_1[(`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRSTART1_SBR_ADDRESS_START_MASK_1 +: `REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1] & regb_arb_port0_sbrstart1_sbr_address_start_mask_1_mask[`REGB_ARB_PORT0_OFFSET_SBRSTART1_SBR_ADDRESS_START_MASK_1 +: `REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1];
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE0
   //------------------------
         if (rwselect[314] && write_en) begin
            ff_regb_arb_port0_sbr_address_range_mask_0[(`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0 +: `REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0] & regb_arb_port0_sbrrange0_sbr_address_range_mask_0_mask[`REGB_ARB_PORT0_OFFSET_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0 +: `REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0];
         end
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE1
   //------------------------
         if (rwselect[315] && write_en) begin
            ff_regb_arb_port0_sbr_address_range_mask_1[(`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1) -1:0] <= apb_data_expanded[`REGB_ARB_PORT0_OFFSET_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1 +: `REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1] & regb_arb_port0_sbrrange1_sbr_address_range_mask_1_mask[`REGB_ARB_PORT0_OFFSET_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1 +: `REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG0
   //------------------------
         if (rwselect[1487] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ras_min[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] & regb_freq0_ch0_dramset1tmg0_t_ras_min_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
            end
         end
         if (rwselect[1487] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ras_max[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] & regb_freq0_ch0_dramset1tmg0_t_ras_max_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
            end
         end
         if (rwselect[1487] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_faw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW] & regb_freq0_ch0_dramset1tmg0_t_faw_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW];
            end
         end
         if (rwselect[1487] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wr2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE] & regb_freq0_ch0_dramset1tmg0_wr2pre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG1
   //------------------------
         if (rwselect[1488] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rc[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC] & regb_freq0_ch0_dramset1tmg1_t_rc_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC];
            end
         end
         if (rwselect[1488] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rd2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE] & regb_freq0_ch0_dramset1tmg1_rd2pre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
            end
         end
         if (rwselect[1488] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_xp[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP] & regb_freq0_ch0_dramset1tmg1_t_xp_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP];
            end
         end
         if (rwselect[1488] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rcd_write[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] & regb_freq0_ch0_dramset1tmg1_t_rcd_write_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG2
   //------------------------
         if (rwselect[1489] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wr2rd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD] & regb_freq0_ch0_dramset1tmg2_wr2rd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD];
            end
         end
         if (rwselect[1489] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rd2wr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR] & regb_freq0_ch0_dramset1tmg2_rd2wr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR];
            end
         end
         if (rwselect[1489] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_read_latency[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] & regb_freq0_ch0_dramset1tmg2_read_latency_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
            end
         end
         if (rwselect[1489] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_write_latency[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] & regb_freq0_ch0_dramset1tmg2_write_latency_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG3
   //------------------------
         if (rwselect[1490] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wr2mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR] & regb_freq0_ch0_dramset1tmg3_wr2mr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR];
            end
         end
         if (rwselect[1490] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rd2mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR] & regb_freq0_ch0_dramset1tmg3_rd2mr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR];
            end
         end
         if (rwselect[1490] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_mr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR] & regb_freq0_ch0_dramset1tmg3_t_mr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG4
   //------------------------
         if (rwselect[1491] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rp[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP] & regb_freq0_ch0_dramset1tmg4_t_rp_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP];
            end
         end
         if (rwselect[1491] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rrd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD] & regb_freq0_ch0_dramset1tmg4_t_rrd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD];
            end
         end
         if (rwselect[1491] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ccd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD] & regb_freq0_ch0_dramset1tmg4_t_ccd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD];
            end
         end
         if (rwselect[1491] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rcd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD] & regb_freq0_ch0_dramset1tmg4_t_rcd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG5
   //------------------------
         if (rwselect[1492] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_cke[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE] & regb_freq0_ch0_dramset1tmg5_t_cke_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE];
            end
         end
         if (rwselect[1492] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_ckesr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR] & regb_freq0_ch0_dramset1tmg5_t_ckesr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
            end
         end
         if (rwselect[1492] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_cksre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] & regb_freq0_ch0_dramset1tmg5_t_cksre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
            end
         end
         if (rwselect[1492] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_cksrx[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] & regb_freq0_ch0_dramset1tmg5_t_cksrx_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG6
   //------------------------
         if (rwselect[1493] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ckcsx[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] & regb_freq0_ch0_dramset1tmg6_t_ckcsx_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG7
   //------------------------
         if (rwselect[1494] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_csh[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH] & regb_freq0_ch0_dramset1tmg7_t_csh_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG9
   //------------------------
         if (rwselect[1496] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wr2rd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] & regb_freq0_ch0_dramset1tmg9_wr2rd_s_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
            end
         end
         if (rwselect[1496] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_rrd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] & regb_freq0_ch0_dramset1tmg9_t_rrd_s_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
            end
         end
         if (rwselect[1496] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ccd_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] & regb_freq0_ch0_dramset1tmg9_t_ccd_s_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG12
   //------------------------
         if (rwselect[1499] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_cmdcke[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] & regb_freq0_ch0_dramset1tmg12_t_cmdcke_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG13
   //------------------------
         if (rwselect[1500] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ppd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD] & regb_freq0_ch0_dramset1tmg13_t_ppd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD];
            end
         end
         if (rwselect[1500] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_ccd_mw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] & regb_freq0_ch0_dramset1tmg13_t_ccd_mw_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
            end
         end
         if (rwselect[1500] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_odtloff[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] & regb_freq0_ch0_dramset1tmg13_odtloff_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG14
   //------------------------
         if (rwselect[1501] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_xsr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR] & regb_freq0_ch0_dramset1tmg14_t_xsr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR];
            end
         end
         if (rwselect[1501] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_osco[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO] & regb_freq0_ch0_dramset1tmg14_t_osco_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG17
   //------------------------
         if (rwselect[1504] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_vrcg_disable[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] & regb_freq0_ch0_dramset1tmg17_t_vrcg_disable_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
            end
         end
         if (rwselect[1504] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_vrcg_enable[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] & regb_freq0_ch0_dramset1tmg17_t_vrcg_enable_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG23
   //------------------------
         if (rwselect[1509] && write_en) begin
            ff_regb_freq0_ch0_t_pdn[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN] & regb_freq0_ch0_dramset1tmg23_t_pdn_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN];
         end
         if (rwselect[1509] && write_en) begin
            ff_regb_freq0_ch0_t_xsr_dsm_x1024[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] & regb_freq0_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG24
   //------------------------
         if (rwselect[1510] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_max_wr_sync[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] & regb_freq0_ch0_dramset1tmg24_max_wr_sync_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
            end
         end
         if (rwselect[1510] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_max_rd_sync[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] & regb_freq0_ch0_dramset1tmg24_max_rd_sync_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
            end
         end
         if (rwselect[1510] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rd2wr_s[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] & regb_freq0_ch0_dramset1tmg24_rd2wr_s_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
            end
         end
         if (rwselect[1510] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_bank_org[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] & regb_freq0_ch0_dramset1tmg24_bank_org_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG25
   //------------------------
         if (rwselect[1511] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rda2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] & regb_freq0_ch0_dramset1tmg25_rda2pre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
            end
         end
         if (rwselect[1511] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wra2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] & regb_freq0_ch0_dramset1tmg25_wra2pre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
            end
         end
         if (rwselect[1511] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] & regb_freq0_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG30
   //------------------------
         if (rwselect[1516] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_mrr2rd[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD] & regb_freq0_ch0_dramset1tmg30_mrr2rd_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
            end
         end
         if (rwselect[1516] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_mrr2wr[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR] & regb_freq0_ch0_dramset1tmg30_mrr2wr_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
            end
         end
         if (rwselect[1516] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_mrr2mrw[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] & regb_freq0_ch0_dramset1tmg30_mrr2mrw_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG32
   //------------------------
         if (rwselect[1518] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_ws_fs2wck_sus[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] & regb_freq0_ch0_dramset1tmg32_ws_fs2wck_sus_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
            end
         end
         if (rwselect[1518] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_wcksus[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] & regb_freq0_ch0_dramset1tmg32_t_wcksus_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
            end
         end
         if (rwselect[1518] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_ws_off2ws_fs[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] & regb_freq0_ch0_dramset1tmg32_ws_off2ws_fs_mask[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR0
   //------------------------
         if (rwselect[1549] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_emr[(`REGB_FREQ0_CH0_SIZE_INITMR0_EMR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ0_CH0_SIZE_INITMR0_EMR] & regb_freq0_ch0_initmr0_emr_mask[`REGB_FREQ0_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ0_CH0_SIZE_INITMR0_EMR];
            end
         end
         if (rwselect[1549] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr[(`REGB_FREQ0_CH0_SIZE_INITMR0_MR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ0_CH0_SIZE_INITMR0_MR] & regb_freq0_ch0_initmr0_mr_mask[`REGB_FREQ0_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ0_CH0_SIZE_INITMR0_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR1
   //------------------------
         if (rwselect[1550] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_emr3[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ0_CH0_SIZE_INITMR1_EMR3] & regb_freq0_ch0_initmr1_emr3_mask[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ0_CH0_SIZE_INITMR1_EMR3];
            end
         end
         if (rwselect[1550] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_emr2[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ0_CH0_SIZE_INITMR1_EMR2] & regb_freq0_ch0_initmr1_emr2_mask[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ0_CH0_SIZE_INITMR1_EMR2];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR2
   //------------------------
         if (rwselect[1551] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr5[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR5) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ0_CH0_SIZE_INITMR2_MR5] & regb_freq0_ch0_initmr2_mr5_mask[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ0_CH0_SIZE_INITMR2_MR5];
            end
         end
         if (rwselect[1551] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr4[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR4) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ0_CH0_SIZE_INITMR2_MR4] & regb_freq0_ch0_initmr2_mr4_mask[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ0_CH0_SIZE_INITMR2_MR4];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR3
   //------------------------
         if (rwselect[1552] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr6[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR6) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ0_CH0_SIZE_INITMR3_MR6] & regb_freq0_ch0_initmr3_mr6_mask[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ0_CH0_SIZE_INITMR3_MR6];
            end
         end
         if (rwselect[1552] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr22[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR22) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ0_CH0_SIZE_INITMR3_MR22] & regb_freq0_ch0_initmr3_mr22_mask[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ0_CH0_SIZE_INITMR3_MR22];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG0
   //------------------------
         if (rwselect[1553] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_tphy_wrlat[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] & regb_freq0_ch0_dfitmg0_dfi_tphy_wrlat_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
            end
         end
         if (rwselect[1553] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_tphy_wrdata[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] & regb_freq0_ch0_dfitmg0_dfi_tphy_wrdata_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
            end
         end
         if (rwselect[1553] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_t_rddata_en[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] & regb_freq0_ch0_dfitmg0_dfi_t_rddata_en_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
            end
         end
         if (rwselect[1553] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_t_ctrl_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] & regb_freq0_ch0_dfitmg0_dfi_t_ctrl_delay_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG1
   //------------------------
         if (rwselect[1554] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] & regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_enable_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
            end
         end
         if (rwselect[1554] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] & regb_freq0_ch0_dfitmg1_dfi_t_dram_clk_disable_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
            end
         end
         if (rwselect[1554] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_dfi_t_wrdata_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] & regb_freq0_ch0_dfitmg1_dfi_t_wrdata_delay_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG2
   //------------------------
         if (rwselect[1555] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_tphy_wrcslat[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] & regb_freq0_ch0_dfitmg2_dfi_tphy_wrcslat_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
            end
         end
         if (rwselect[1555] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_tphy_rdcslat[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] & regb_freq0_ch0_dfitmg2_dfi_tphy_rdcslat_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
            end
         end
         if (rwselect[1555] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_delay[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] & regb_freq0_ch0_dfitmg2_dfi_twck_delay_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG4
   //------------------------
         if (rwselect[1557] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_dis[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] & regb_freq0_ch0_dfitmg4_dfi_twck_dis_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
            end
         end
         if (rwselect[1557] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_en_fs[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] & regb_freq0_ch0_dfitmg4_dfi_twck_en_fs_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
            end
         end
         if (rwselect[1557] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_en_wr[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] & regb_freq0_ch0_dfitmg4_dfi_twck_en_wr_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
            end
         end
         if (rwselect[1557] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_en_rd[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] & regb_freq0_ch0_dfitmg4_dfi_twck_en_rd_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG5
   //------------------------
         if (rwselect[1558] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] & regb_freq0_ch0_dfitmg5_dfi_twck_toggle_post_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
            end
         end
         if (rwselect[1558] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_cs[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] & regb_freq0_ch0_dfitmg5_dfi_twck_toggle_cs_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
            end
         end
         if (rwselect[1558] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_toggle[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] & regb_freq0_ch0_dfitmg5_dfi_twck_toggle_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
            end
         end
         if (rwselect[1558] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_fast_toggle[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] & regb_freq0_ch0_dfitmg5_dfi_twck_fast_toggle_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG6
   //------------------------
         if (rwselect[1559] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] & regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
            end
         end
         if (rwselect[1559] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd_en <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] & regb_freq0_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG0
   //------------------------
         if (rwselect[1561] && write_en) begin
            ff_regb_freq0_ch0_dfi_lp_wakeup_pd[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_PD +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD] & regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_pd_mask[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_PD +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD];
         end
         if (rwselect[1561] && write_en) begin
            ff_regb_freq0_ch0_dfi_lp_wakeup_sr[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_SR +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR] & regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_sr_mask[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_SR +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR];
         end
         if (rwselect[1561] && write_en) begin
            ff_regb_freq0_ch0_dfi_lp_wakeup_dsm[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_DSM +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM] & regb_freq0_ch0_dfilptmg0_dfi_lp_wakeup_dsm_mask[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_DSM +: `REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG1
   //------------------------
         if (rwselect[1562] && write_en) begin
            ff_regb_freq0_ch0_dfi_lp_wakeup_data[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_LP_WAKEUP_DATA +: `REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA] & regb_freq0_ch0_dfilptmg1_dfi_lp_wakeup_data_mask[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_LP_WAKEUP_DATA +: `REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA];
         end
         if (rwselect[1562] && write_en) begin
            ff_regb_freq0_ch0_dfi_tlp_resp[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_TLP_RESP +: `REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP] & regb_freq0_ch0_dfilptmg1_dfi_tlp_resp_mask[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_TLP_RESP +: `REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG0
   //------------------------
         if (rwselect[1563] && write_en) begin
            ff_regb_freq0_ch0_dfi_t_ctrlup_min[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MIN +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN] & regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_min_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MIN +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN];
         end
         if (rwselect[1563] && write_en) begin
            ff_regb_freq0_ch0_dfi_t_ctrlup_max[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MAX +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX] & regb_freq0_ch0_dfiupdtmg0_dfi_t_ctrlup_max_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MAX +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG1
   //------------------------
         if (rwselect[1564] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] & regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
            end
         end
         if (rwselect[1564] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] & regb_freq0_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG2
   //------------------------
         if (rwselect[1566] && write_en) begin
            ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] & regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
         end
         if (rwselect[1566] && write_en) begin
            ff_regb_freq0_ch0_ctrlupd_after_dqsosc <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] & regb_freq0_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
         end
         if (rwselect[1566] && write_en) begin
            ff_regb_freq0_ch0_ppt2_override <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] & regb_freq0_ch0_dfiupdtmg2_ppt2_override_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
         end
         if (rwselect[1566] && write_en) begin
            ff_regb_freq0_ch0_ppt2_en <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_EN] & regb_freq0_ch0_dfiupdtmg2_ppt2_en_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
         end
         if (rwselect[1566] && write_en) begin
            ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] & regb_freq0_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG3
   //------------------------
         if (rwselect[1567] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] & regb_freq0_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG0
   //------------------------
         if (rwselect[1568] && write_en) begin
            ff_regb_freq0_ch0_t_refi_x1_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] & regb_freq0_ch0_rfshset1tmg0_t_refi_x1_x32_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
         end
         if (rwselect[1568] && write_en) begin
            ff_regb_freq0_ch0_refresh_to_x1_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] & regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_x32_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
         end
         if (rwselect[1568] && write_en) begin
            ff_regb_freq0_ch0_refresh_margin[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] & regb_freq0_ch0_rfshset1tmg0_refresh_margin_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
         end
         if (rwselect[1568] && write_en) begin
            ff_regb_freq0_ch0_refresh_to_x1_sel <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] & regb_freq0_ch0_rfshset1tmg0_refresh_to_x1_sel_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
         end
         if (rwselect[1568] && write_en) begin
            ff_regb_freq0_ch0_t_refi_x1_sel <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] & regb_freq0_ch0_rfshset1tmg0_t_refi_x1_sel_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG1
   //------------------------
         if (rwselect[1569] && write_en) begin
            ff_regb_freq0_ch0_t_rfc_min[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] & regb_freq0_ch0_rfshset1tmg1_t_rfc_min_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
         end
         if (rwselect[1569] && write_en) begin
            ff_regb_freq0_ch0_t_rfc_min_ab[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] & regb_freq0_ch0_rfshset1tmg1_t_rfc_min_ab_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG2
   //------------------------
         if (rwselect[1570] && write_en) begin
            ff_regb_freq0_ch0_t_pbr2pbr[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] & regb_freq0_ch0_rfshset1tmg2_t_pbr2pbr_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
         end
         if (rwselect[1570] && write_en) begin
            ff_regb_freq0_ch0_t_pbr2act[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] & regb_freq0_ch0_rfshset1tmg2_t_pbr2act_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG3
   //------------------------
         if (rwselect[1571] && write_en) begin
            ff_regb_freq0_ch0_refresh_to_ab_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] & regb_freq0_ch0_rfshset1tmg3_refresh_to_ab_x32_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG4
   //------------------------
         if (rwselect[1572] && write_en) begin
            ff_regb_freq0_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] & regb_freq0_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
         end
         if (rwselect[1572] && write_en) begin
            ff_regb_freq0_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] & regb_freq0_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RFMSET1TMG0
   //------------------------
         if (rwselect[1582] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_t_rfmpb[(`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB] & regb_freq0_ch0_rfmset1tmg0_t_rfmpb_mask[`REGB_FREQ0_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG0
   //------------------------
         if (rwselect[1593] && write_en) begin
            ff_regb_freq0_ch0_t_zq_long_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] & regb_freq0_ch0_zqset1tmg0_t_zq_long_nop_mask[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
         end
         if (rwselect[1593] && write_en) begin
            ff_regb_freq0_ch0_t_zq_short_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] & regb_freq0_ch0_zqset1tmg0_t_zq_short_nop_mask[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG1
   //------------------------
         if (rwselect[1594] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_zq_short_interval_x1024[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] & regb_freq0_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
            end
         end
         if (rwselect[1594] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_zq_reset_nop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] & regb_freq0_ch0_zqset1tmg1_t_zq_reset_nop_mask[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG2
   //------------------------
         if (rwselect[1595] && write_en) begin
            ff_regb_freq0_ch0_t_zq_stop[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] & regb_freq0_ch0_zqset1tmg2_t_zq_stop_mask[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DQSOSCCTL0
   //------------------------
         if (rwselect[1604] && write_en) begin
            ff_regb_freq0_ch0_dqsosc_enable <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] & regb_freq0_ch0_dqsoscctl0_dqsosc_enable_mask[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
         end
         if (rwselect[1604] && write_en) begin
            ff_regb_freq0_ch0_dqsosc_interval_unit <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] & regb_freq0_ch0_dqsoscctl0_dqsosc_interval_unit_mask[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
         end
         if (rwselect[1604] && write_en) begin
            ff_regb_freq0_ch0_dqsosc_interval[(`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] & regb_freq0_ch0_dqsoscctl0_dqsosc_interval_mask[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEINT
   //------------------------
         if (rwselect[1605] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_mr4_read_interval[(`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] & regb_freq0_ch0_derateint_mr4_read_interval_mask[`REGB_FREQ0_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL0
   //------------------------
         if (rwselect[1606] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_rrd[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] & regb_freq0_ch0_derateval0_derated_t_rrd_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
            end
         end
         if (rwselect[1606] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_rp[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP] & regb_freq0_ch0_derateval0_derated_t_rp_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
            end
         end
         if (rwselect[1606] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_ras_min[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] & regb_freq0_ch0_derateval0_derated_t_ras_min_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
            end
         end
         if (rwselect[1606] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_rcd[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] & regb_freq0_ch0_derateval0_derated_t_rcd_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL1
   //------------------------
         if (rwselect[1607] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_rc[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC] & regb_freq0_ch0_derateval1_derated_t_rc_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
            end
         end
         if (rwselect[1607] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_derated_t_rcd_write[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] & regb_freq0_ch0_derateval1_derated_t_rcd_write_mask[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.HWLPTMG0
   //------------------------
         if (rwselect[1608] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_hw_lp_idle_x32[(`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] & regb_freq0_ch0_hwlptmg0_hw_lp_idle_x32_mask[`REGB_FREQ0_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DVFSCTL0
   //------------------------
         if (rwselect[1609] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_dvfsq_enable <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ0_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] & regb_freq0_ch0_dvfsctl0_dvfsq_enable_mask[`REGB_FREQ0_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ0_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.SCHEDTMG0
   //------------------------
         if (rwselect[1610] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_pageclose_timer[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] & regb_freq0_ch0_schedtmg0_pageclose_timer_mask[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
            end
         end
         if (rwselect[1610] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rdwr_idle_gap[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] & regb_freq0_ch0_schedtmg0_rdwr_idle_gap_mask[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFHPR1
   //------------------------
         if (rwselect[1611] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_hpr_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] & regb_freq0_ch0_perfhpr1_hpr_max_starve_mask[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
            end
         end
         if (rwselect[1611] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_hpr_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] & regb_freq0_ch0_perfhpr1_hpr_xact_run_length_mask[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFLPR1
   //------------------------
         if (rwselect[1612] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_lpr_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] & regb_freq0_ch0_perflpr1_lpr_max_starve_mask[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
            end
         end
         if (rwselect[1612] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_lpr_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] & regb_freq0_ch0_perflpr1_lpr_xact_run_length_mask[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.PERFWR1
   //------------------------
         if (rwselect[1613] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_w_max_starve[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE] & regb_freq0_ch0_perfwr1_w_max_starve_mask[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE];
            end
         end
         if (rwselect[1613] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_w_xact_run_length[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] & regb_freq0_ch0_perfwr1_w_xact_run_length_mask[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.TMGCFG
   //------------------------
         if (rwselect[1614] && write_en) begin
            ff_regb_freq0_ch0_frequency_ratio <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ0_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] & regb_freq0_ch0_tmgcfg_frequency_ratio_mask[`REGB_FREQ0_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ0_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG0
   //------------------------
         if (rwselect[1615] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_diff_rank_rd_gap[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] & regb_freq0_ch0_ranktmg0_diff_rank_rd_gap_mask[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
            end
         end
         if (rwselect[1615] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_diff_rank_wr_gap[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] & regb_freq0_ch0_ranktmg0_diff_rank_wr_gap_mask[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG1
   //------------------------
         if (rwselect[1616] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_wr2rd_dr[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR] & regb_freq0_ch0_ranktmg1_wr2rd_dr_mask[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR];
            end
         end
         if (rwselect[1616] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_rd2wr_dr[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR] & regb_freq0_ch0_ranktmg1_rd2wr_dr_mask[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.PWRTMG
   //------------------------
         if (rwselect[1617] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_powerdown_to_x32[(`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] & regb_freq0_ch0_pwrtmg_powerdown_to_x32_mask[`REGB_FREQ0_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
            end
         end
         if (rwselect[1617] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_selfref_to_x32[(`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32] & regb_freq0_ch0_pwrtmg_selfref_to_x32_mask[`REGB_FREQ0_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG0
   //------------------------
         if (rwselect[1623] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_pgm_x1_x1024[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] & regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
            end
         end
         if (rwselect[1623] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_pgm_x1_sel <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] & regb_freq0_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG1
   //------------------------
         if (rwselect[1624] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_pgmpst_x32[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] & regb_freq0_ch0_ddr4pprtmg1_t_pgmpst_x32_mask[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
            end
         end
         if (rwselect[1624] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq0_ch0_t_pgm_exit[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] & regb_freq0_ch0_ddr4pprtmg1_t_pgm_exit_mask[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
            end
         end
   //------------------------
   // Register REGB_FREQ0_CH0.LNKECCCTL0
   //------------------------
         if (rwselect[1625] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_wr_link_ecc_enable <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ0_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] & regb_freq0_ch0_lnkeccctl0_wr_link_ecc_enable_mask[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ0_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
            end
         end
         if (rwselect[1625] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq0_ch0_rd_link_ecc_enable <= apb_data_expanded[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ0_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] & regb_freq0_ch0_lnkeccctl0_rd_link_ecc_enable_mask[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ0_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG0
   //------------------------
         if (rwselect[1759] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ras_min[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] & regb_freq1_ch0_dramset1tmg0_t_ras_min_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
            end
         end
         if (rwselect[1759] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ras_max[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] & regb_freq1_ch0_dramset1tmg0_t_ras_max_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
            end
         end
         if (rwselect[1759] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_faw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW] & regb_freq1_ch0_dramset1tmg0_t_faw_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW];
            end
         end
         if (rwselect[1759] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wr2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE] & regb_freq1_ch0_dramset1tmg0_wr2pre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG1
   //------------------------
         if (rwselect[1760] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rc[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC] & regb_freq1_ch0_dramset1tmg1_t_rc_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC];
            end
         end
         if (rwselect[1760] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rd2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE] & regb_freq1_ch0_dramset1tmg1_rd2pre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
            end
         end
         if (rwselect[1760] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_xp[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP] & regb_freq1_ch0_dramset1tmg1_t_xp_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP];
            end
         end
         if (rwselect[1760] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rcd_write[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] & regb_freq1_ch0_dramset1tmg1_t_rcd_write_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG2
   //------------------------
         if (rwselect[1761] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wr2rd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD] & regb_freq1_ch0_dramset1tmg2_wr2rd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD];
            end
         end
         if (rwselect[1761] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rd2wr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR] & regb_freq1_ch0_dramset1tmg2_rd2wr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR];
            end
         end
         if (rwselect[1761] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_read_latency[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] & regb_freq1_ch0_dramset1tmg2_read_latency_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
            end
         end
         if (rwselect[1761] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_write_latency[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] & regb_freq1_ch0_dramset1tmg2_write_latency_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG3
   //------------------------
         if (rwselect[1762] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wr2mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR] & regb_freq1_ch0_dramset1tmg3_wr2mr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR];
            end
         end
         if (rwselect[1762] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rd2mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR] & regb_freq1_ch0_dramset1tmg3_rd2mr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR];
            end
         end
         if (rwselect[1762] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_mr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR] & regb_freq1_ch0_dramset1tmg3_t_mr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG4
   //------------------------
         if (rwselect[1763] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rp[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP] & regb_freq1_ch0_dramset1tmg4_t_rp_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP];
            end
         end
         if (rwselect[1763] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rrd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD] & regb_freq1_ch0_dramset1tmg4_t_rrd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD];
            end
         end
         if (rwselect[1763] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ccd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD] & regb_freq1_ch0_dramset1tmg4_t_ccd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD];
            end
         end
         if (rwselect[1763] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rcd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD] & regb_freq1_ch0_dramset1tmg4_t_rcd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG5
   //------------------------
         if (rwselect[1764] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_cke[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE] & regb_freq1_ch0_dramset1tmg5_t_cke_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE];
            end
         end
         if (rwselect[1764] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_ckesr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR] & regb_freq1_ch0_dramset1tmg5_t_ckesr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
            end
         end
         if (rwselect[1764] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_cksre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] & regb_freq1_ch0_dramset1tmg5_t_cksre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
            end
         end
         if (rwselect[1764] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_cksrx[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] & regb_freq1_ch0_dramset1tmg5_t_cksrx_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG6
   //------------------------
         if (rwselect[1765] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ckcsx[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] & regb_freq1_ch0_dramset1tmg6_t_ckcsx_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG7
   //------------------------
         if (rwselect[1766] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_csh[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH] & regb_freq1_ch0_dramset1tmg7_t_csh_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG9
   //------------------------
         if (rwselect[1768] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wr2rd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] & regb_freq1_ch0_dramset1tmg9_wr2rd_s_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
            end
         end
         if (rwselect[1768] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_rrd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] & regb_freq1_ch0_dramset1tmg9_t_rrd_s_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
            end
         end
         if (rwselect[1768] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ccd_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] & regb_freq1_ch0_dramset1tmg9_t_ccd_s_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG12
   //------------------------
         if (rwselect[1771] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_cmdcke[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] & regb_freq1_ch0_dramset1tmg12_t_cmdcke_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG13
   //------------------------
         if (rwselect[1772] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ppd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD] & regb_freq1_ch0_dramset1tmg13_t_ppd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD];
            end
         end
         if (rwselect[1772] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_ccd_mw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] & regb_freq1_ch0_dramset1tmg13_t_ccd_mw_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
            end
         end
         if (rwselect[1772] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_odtloff[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] & regb_freq1_ch0_dramset1tmg13_odtloff_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG14
   //------------------------
         if (rwselect[1773] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_xsr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR] & regb_freq1_ch0_dramset1tmg14_t_xsr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR];
            end
         end
         if (rwselect[1773] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_osco[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO] & regb_freq1_ch0_dramset1tmg14_t_osco_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG17
   //------------------------
         if (rwselect[1776] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_vrcg_disable[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] & regb_freq1_ch0_dramset1tmg17_t_vrcg_disable_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
            end
         end
         if (rwselect[1776] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_vrcg_enable[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] & regb_freq1_ch0_dramset1tmg17_t_vrcg_enable_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG23
   //------------------------
         if (rwselect[1781] && write_en) begin
            ff_regb_freq1_ch0_t_pdn[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN] & regb_freq1_ch0_dramset1tmg23_t_pdn_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN];
         end
         if (rwselect[1781] && write_en) begin
            ff_regb_freq1_ch0_t_xsr_dsm_x1024[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] & regb_freq1_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG24
   //------------------------
         if (rwselect[1782] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_max_wr_sync[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] & regb_freq1_ch0_dramset1tmg24_max_wr_sync_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
            end
         end
         if (rwselect[1782] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_max_rd_sync[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] & regb_freq1_ch0_dramset1tmg24_max_rd_sync_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
            end
         end
         if (rwselect[1782] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rd2wr_s[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] & regb_freq1_ch0_dramset1tmg24_rd2wr_s_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
            end
         end
         if (rwselect[1782] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_bank_org[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] & regb_freq1_ch0_dramset1tmg24_bank_org_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG25
   //------------------------
         if (rwselect[1783] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rda2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] & regb_freq1_ch0_dramset1tmg25_rda2pre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
            end
         end
         if (rwselect[1783] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wra2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] & regb_freq1_ch0_dramset1tmg25_wra2pre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
            end
         end
         if (rwselect[1783] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] & regb_freq1_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG30
   //------------------------
         if (rwselect[1788] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_mrr2rd[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD] & regb_freq1_ch0_dramset1tmg30_mrr2rd_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
            end
         end
         if (rwselect[1788] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_mrr2wr[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR] & regb_freq1_ch0_dramset1tmg30_mrr2wr_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
            end
         end
         if (rwselect[1788] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_mrr2mrw[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] & regb_freq1_ch0_dramset1tmg30_mrr2mrw_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG32
   //------------------------
         if (rwselect[1790] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_ws_fs2wck_sus[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] & regb_freq1_ch0_dramset1tmg32_ws_fs2wck_sus_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
            end
         end
         if (rwselect[1790] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_wcksus[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] & regb_freq1_ch0_dramset1tmg32_t_wcksus_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
            end
         end
         if (rwselect[1790] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_ws_off2ws_fs[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] & regb_freq1_ch0_dramset1tmg32_ws_off2ws_fs_mask[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR0
   //------------------------
         if (rwselect[1821] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_emr[(`REGB_FREQ1_CH0_SIZE_INITMR0_EMR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ1_CH0_SIZE_INITMR0_EMR] & regb_freq1_ch0_initmr0_emr_mask[`REGB_FREQ1_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ1_CH0_SIZE_INITMR0_EMR];
            end
         end
         if (rwselect[1821] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr[(`REGB_FREQ1_CH0_SIZE_INITMR0_MR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ1_CH0_SIZE_INITMR0_MR] & regb_freq1_ch0_initmr0_mr_mask[`REGB_FREQ1_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ1_CH0_SIZE_INITMR0_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR1
   //------------------------
         if (rwselect[1822] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_emr3[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ1_CH0_SIZE_INITMR1_EMR3] & regb_freq1_ch0_initmr1_emr3_mask[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ1_CH0_SIZE_INITMR1_EMR3];
            end
         end
         if (rwselect[1822] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_emr2[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ1_CH0_SIZE_INITMR1_EMR2] & regb_freq1_ch0_initmr1_emr2_mask[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ1_CH0_SIZE_INITMR1_EMR2];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR2
   //------------------------
         if (rwselect[1823] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr5[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR5) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ1_CH0_SIZE_INITMR2_MR5] & regb_freq1_ch0_initmr2_mr5_mask[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ1_CH0_SIZE_INITMR2_MR5];
            end
         end
         if (rwselect[1823] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr4[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR4) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ1_CH0_SIZE_INITMR2_MR4] & regb_freq1_ch0_initmr2_mr4_mask[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ1_CH0_SIZE_INITMR2_MR4];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR3
   //------------------------
         if (rwselect[1824] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr6[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR6) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ1_CH0_SIZE_INITMR3_MR6] & regb_freq1_ch0_initmr3_mr6_mask[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ1_CH0_SIZE_INITMR3_MR6];
            end
         end
         if (rwselect[1824] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr22[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR22) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ1_CH0_SIZE_INITMR3_MR22] & regb_freq1_ch0_initmr3_mr22_mask[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ1_CH0_SIZE_INITMR3_MR22];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG0
   //------------------------
         if (rwselect[1825] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_tphy_wrlat[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] & regb_freq1_ch0_dfitmg0_dfi_tphy_wrlat_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
            end
         end
         if (rwselect[1825] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_tphy_wrdata[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] & regb_freq1_ch0_dfitmg0_dfi_tphy_wrdata_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
            end
         end
         if (rwselect[1825] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_t_rddata_en[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] & regb_freq1_ch0_dfitmg0_dfi_t_rddata_en_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
            end
         end
         if (rwselect[1825] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_t_ctrl_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] & regb_freq1_ch0_dfitmg0_dfi_t_ctrl_delay_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG1
   //------------------------
         if (rwselect[1826] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] & regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_enable_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
            end
         end
         if (rwselect[1826] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] & regb_freq1_ch0_dfitmg1_dfi_t_dram_clk_disable_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
            end
         end
         if (rwselect[1826] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_dfi_t_wrdata_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] & regb_freq1_ch0_dfitmg1_dfi_t_wrdata_delay_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG2
   //------------------------
         if (rwselect[1827] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_tphy_wrcslat[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] & regb_freq1_ch0_dfitmg2_dfi_tphy_wrcslat_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
            end
         end
         if (rwselect[1827] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_tphy_rdcslat[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] & regb_freq1_ch0_dfitmg2_dfi_tphy_rdcslat_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
            end
         end
         if (rwselect[1827] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_delay[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] & regb_freq1_ch0_dfitmg2_dfi_twck_delay_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG4
   //------------------------
         if (rwselect[1829] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_dis[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] & regb_freq1_ch0_dfitmg4_dfi_twck_dis_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
            end
         end
         if (rwselect[1829] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_en_fs[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] & regb_freq1_ch0_dfitmg4_dfi_twck_en_fs_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
            end
         end
         if (rwselect[1829] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_en_wr[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] & regb_freq1_ch0_dfitmg4_dfi_twck_en_wr_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
            end
         end
         if (rwselect[1829] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_en_rd[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] & regb_freq1_ch0_dfitmg4_dfi_twck_en_rd_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG5
   //------------------------
         if (rwselect[1830] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] & regb_freq1_ch0_dfitmg5_dfi_twck_toggle_post_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
            end
         end
         if (rwselect[1830] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_cs[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] & regb_freq1_ch0_dfitmg5_dfi_twck_toggle_cs_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
            end
         end
         if (rwselect[1830] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_toggle[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] & regb_freq1_ch0_dfitmg5_dfi_twck_toggle_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
            end
         end
         if (rwselect[1830] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_fast_toggle[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] & regb_freq1_ch0_dfitmg5_dfi_twck_fast_toggle_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG6
   //------------------------
         if (rwselect[1831] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] & regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
            end
         end
         if (rwselect[1831] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_twck_toggle_post_rd_en <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] & regb_freq1_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG1
   //------------------------
         if (rwselect[1833] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] & regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
            end
         end
         if (rwselect[1833] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] & regb_freq1_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG2
   //------------------------
         if (rwselect[1834] && write_en) begin
            ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] & regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
         end
         if (rwselect[1834] && write_en) begin
            ff_regb_freq1_ch0_ctrlupd_after_dqsosc <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] & regb_freq1_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
         end
         if (rwselect[1834] && write_en) begin
            ff_regb_freq1_ch0_ppt2_override <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] & regb_freq1_ch0_dfiupdtmg2_ppt2_override_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
         end
         if (rwselect[1834] && write_en) begin
            ff_regb_freq1_ch0_ppt2_en <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_EN] & regb_freq1_ch0_dfiupdtmg2_ppt2_en_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
         end
         if (rwselect[1834] && write_en) begin
            ff_regb_freq1_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] & regb_freq1_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG3
   //------------------------
         if (rwselect[1835] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] & regb_freq1_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG0
   //------------------------
         if (rwselect[1836] && write_en) begin
            ff_regb_freq1_ch0_t_refi_x1_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] & regb_freq1_ch0_rfshset1tmg0_t_refi_x1_x32_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
         end
         if (rwselect[1836] && write_en) begin
            ff_regb_freq1_ch0_refresh_to_x1_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] & regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_x32_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
         end
         if (rwselect[1836] && write_en) begin
            ff_regb_freq1_ch0_refresh_margin[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] & regb_freq1_ch0_rfshset1tmg0_refresh_margin_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
         end
         if (rwselect[1836] && write_en) begin
            ff_regb_freq1_ch0_refresh_to_x1_sel <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] & regb_freq1_ch0_rfshset1tmg0_refresh_to_x1_sel_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
         end
         if (rwselect[1836] && write_en) begin
            ff_regb_freq1_ch0_t_refi_x1_sel <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] & regb_freq1_ch0_rfshset1tmg0_t_refi_x1_sel_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG1
   //------------------------
         if (rwselect[1837] && write_en) begin
            ff_regb_freq1_ch0_t_rfc_min[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] & regb_freq1_ch0_rfshset1tmg1_t_rfc_min_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
         end
         if (rwselect[1837] && write_en) begin
            ff_regb_freq1_ch0_t_rfc_min_ab[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] & regb_freq1_ch0_rfshset1tmg1_t_rfc_min_ab_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG2
   //------------------------
         if (rwselect[1838] && write_en) begin
            ff_regb_freq1_ch0_t_pbr2pbr[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] & regb_freq1_ch0_rfshset1tmg2_t_pbr2pbr_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
         end
         if (rwselect[1838] && write_en) begin
            ff_regb_freq1_ch0_t_pbr2act[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] & regb_freq1_ch0_rfshset1tmg2_t_pbr2act_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG3
   //------------------------
         if (rwselect[1839] && write_en) begin
            ff_regb_freq1_ch0_refresh_to_ab_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] & regb_freq1_ch0_rfshset1tmg3_refresh_to_ab_x32_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG4
   //------------------------
         if (rwselect[1840] && write_en) begin
            ff_regb_freq1_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] & regb_freq1_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
         end
         if (rwselect[1840] && write_en) begin
            ff_regb_freq1_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] & regb_freq1_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RFMSET1TMG0
   //------------------------
         if (rwselect[1850] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_t_rfmpb[(`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB] & regb_freq1_ch0_rfmset1tmg0_t_rfmpb_mask[`REGB_FREQ1_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG0
   //------------------------
         if (rwselect[1861] && write_en) begin
            ff_regb_freq1_ch0_t_zq_long_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] & regb_freq1_ch0_zqset1tmg0_t_zq_long_nop_mask[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
         end
         if (rwselect[1861] && write_en) begin
            ff_regb_freq1_ch0_t_zq_short_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] & regb_freq1_ch0_zqset1tmg0_t_zq_short_nop_mask[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG1
   //------------------------
         if (rwselect[1862] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_zq_short_interval_x1024[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] & regb_freq1_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
            end
         end
         if (rwselect[1862] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_zq_reset_nop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] & regb_freq1_ch0_zqset1tmg1_t_zq_reset_nop_mask[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG2
   //------------------------
         if (rwselect[1863] && write_en) begin
            ff_regb_freq1_ch0_t_zq_stop[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] & regb_freq1_ch0_zqset1tmg2_t_zq_stop_mask[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DQSOSCCTL0
   //------------------------
         if (rwselect[1872] && write_en) begin
            ff_regb_freq1_ch0_dqsosc_enable <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] & regb_freq1_ch0_dqsoscctl0_dqsosc_enable_mask[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
         end
         if (rwselect[1872] && write_en) begin
            ff_regb_freq1_ch0_dqsosc_interval_unit <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] & regb_freq1_ch0_dqsoscctl0_dqsosc_interval_unit_mask[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
         end
         if (rwselect[1872] && write_en) begin
            ff_regb_freq1_ch0_dqsosc_interval[(`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] & regb_freq1_ch0_dqsoscctl0_dqsosc_interval_mask[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEINT
   //------------------------
         if (rwselect[1873] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_mr4_read_interval[(`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] & regb_freq1_ch0_derateint_mr4_read_interval_mask[`REGB_FREQ1_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL0
   //------------------------
         if (rwselect[1874] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_rrd[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] & regb_freq1_ch0_derateval0_derated_t_rrd_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
            end
         end
         if (rwselect[1874] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_rp[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP] & regb_freq1_ch0_derateval0_derated_t_rp_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
            end
         end
         if (rwselect[1874] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_ras_min[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] & regb_freq1_ch0_derateval0_derated_t_ras_min_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
            end
         end
         if (rwselect[1874] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_rcd[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] & regb_freq1_ch0_derateval0_derated_t_rcd_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL1
   //------------------------
         if (rwselect[1875] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_rc[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC] & regb_freq1_ch0_derateval1_derated_t_rc_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
            end
         end
         if (rwselect[1875] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_derated_t_rcd_write[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] & regb_freq1_ch0_derateval1_derated_t_rcd_write_mask[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.HWLPTMG0
   //------------------------
         if (rwselect[1876] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_hw_lp_idle_x32[(`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] & regb_freq1_ch0_hwlptmg0_hw_lp_idle_x32_mask[`REGB_FREQ1_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DVFSCTL0
   //------------------------
         if (rwselect[1877] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_dvfsq_enable <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ1_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] & regb_freq1_ch0_dvfsctl0_dvfsq_enable_mask[`REGB_FREQ1_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ1_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.SCHEDTMG0
   //------------------------
         if (rwselect[1878] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_pageclose_timer[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] & regb_freq1_ch0_schedtmg0_pageclose_timer_mask[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
            end
         end
         if (rwselect[1878] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rdwr_idle_gap[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] & regb_freq1_ch0_schedtmg0_rdwr_idle_gap_mask[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFHPR1
   //------------------------
         if (rwselect[1879] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_hpr_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] & regb_freq1_ch0_perfhpr1_hpr_max_starve_mask[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
            end
         end
         if (rwselect[1879] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_hpr_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] & regb_freq1_ch0_perfhpr1_hpr_xact_run_length_mask[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFLPR1
   //------------------------
         if (rwselect[1880] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_lpr_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] & regb_freq1_ch0_perflpr1_lpr_max_starve_mask[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
            end
         end
         if (rwselect[1880] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_lpr_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] & regb_freq1_ch0_perflpr1_lpr_xact_run_length_mask[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.PERFWR1
   //------------------------
         if (rwselect[1881] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_w_max_starve[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE] & regb_freq1_ch0_perfwr1_w_max_starve_mask[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE];
            end
         end
         if (rwselect[1881] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_w_xact_run_length[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] & regb_freq1_ch0_perfwr1_w_xact_run_length_mask[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.TMGCFG
   //------------------------
         if (rwselect[1882] && write_en) begin
            ff_regb_freq1_ch0_frequency_ratio <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ1_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] & regb_freq1_ch0_tmgcfg_frequency_ratio_mask[`REGB_FREQ1_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ1_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG0
   //------------------------
         if (rwselect[1883] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_diff_rank_rd_gap[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] & regb_freq1_ch0_ranktmg0_diff_rank_rd_gap_mask[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
            end
         end
         if (rwselect[1883] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_diff_rank_wr_gap[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] & regb_freq1_ch0_ranktmg0_diff_rank_wr_gap_mask[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG1
   //------------------------
         if (rwselect[1884] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_wr2rd_dr[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR] & regb_freq1_ch0_ranktmg1_wr2rd_dr_mask[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR];
            end
         end
         if (rwselect[1884] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_rd2wr_dr[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR] & regb_freq1_ch0_ranktmg1_rd2wr_dr_mask[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.PWRTMG
   //------------------------
         if (rwselect[1885] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_powerdown_to_x32[(`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] & regb_freq1_ch0_pwrtmg_powerdown_to_x32_mask[`REGB_FREQ1_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
            end
         end
         if (rwselect[1885] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_selfref_to_x32[(`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32] & regb_freq1_ch0_pwrtmg_selfref_to_x32_mask[`REGB_FREQ1_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG0
   //------------------------
         if (rwselect[1891] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_pgm_x1_x1024[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] & regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
            end
         end
         if (rwselect[1891] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_pgm_x1_sel <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] & regb_freq1_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG1
   //------------------------
         if (rwselect[1892] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_pgmpst_x32[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] & regb_freq1_ch0_ddr4pprtmg1_t_pgmpst_x32_mask[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
            end
         end
         if (rwselect[1892] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq1_ch0_t_pgm_exit[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] & regb_freq1_ch0_ddr4pprtmg1_t_pgm_exit_mask[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
            end
         end
   //------------------------
   // Register REGB_FREQ1_CH0.LNKECCCTL0
   //------------------------
         if (rwselect[1893] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_wr_link_ecc_enable <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ1_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] & regb_freq1_ch0_lnkeccctl0_wr_link_ecc_enable_mask[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ1_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
            end
         end
         if (rwselect[1893] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq1_ch0_rd_link_ecc_enable <= apb_data_expanded[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ1_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] & regb_freq1_ch0_lnkeccctl0_rd_link_ecc_enable_mask[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ1_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG0
   //------------------------
         if (rwselect[2027] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ras_min[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] & regb_freq2_ch0_dramset1tmg0_t_ras_min_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
            end
         end
         if (rwselect[2027] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ras_max[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] & regb_freq2_ch0_dramset1tmg0_t_ras_max_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
            end
         end
         if (rwselect[2027] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_faw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW] & regb_freq2_ch0_dramset1tmg0_t_faw_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW];
            end
         end
         if (rwselect[2027] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wr2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE] & regb_freq2_ch0_dramset1tmg0_wr2pre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG1
   //------------------------
         if (rwselect[2028] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rc[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC] & regb_freq2_ch0_dramset1tmg1_t_rc_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC];
            end
         end
         if (rwselect[2028] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rd2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE] & regb_freq2_ch0_dramset1tmg1_rd2pre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
            end
         end
         if (rwselect[2028] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_xp[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP] & regb_freq2_ch0_dramset1tmg1_t_xp_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP];
            end
         end
         if (rwselect[2028] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rcd_write[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] & regb_freq2_ch0_dramset1tmg1_t_rcd_write_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG2
   //------------------------
         if (rwselect[2029] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wr2rd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD] & regb_freq2_ch0_dramset1tmg2_wr2rd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD];
            end
         end
         if (rwselect[2029] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rd2wr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR] & regb_freq2_ch0_dramset1tmg2_rd2wr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR];
            end
         end
         if (rwselect[2029] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_read_latency[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] & regb_freq2_ch0_dramset1tmg2_read_latency_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
            end
         end
         if (rwselect[2029] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_write_latency[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] & regb_freq2_ch0_dramset1tmg2_write_latency_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG3
   //------------------------
         if (rwselect[2030] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wr2mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR] & regb_freq2_ch0_dramset1tmg3_wr2mr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR];
            end
         end
         if (rwselect[2030] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rd2mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR] & regb_freq2_ch0_dramset1tmg3_rd2mr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR];
            end
         end
         if (rwselect[2030] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_mr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR] & regb_freq2_ch0_dramset1tmg3_t_mr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG4
   //------------------------
         if (rwselect[2031] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rp[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP] & regb_freq2_ch0_dramset1tmg4_t_rp_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP];
            end
         end
         if (rwselect[2031] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rrd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD] & regb_freq2_ch0_dramset1tmg4_t_rrd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD];
            end
         end
         if (rwselect[2031] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ccd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD] & regb_freq2_ch0_dramset1tmg4_t_ccd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD];
            end
         end
         if (rwselect[2031] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rcd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD] & regb_freq2_ch0_dramset1tmg4_t_rcd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG5
   //------------------------
         if (rwselect[2032] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_cke[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE] & regb_freq2_ch0_dramset1tmg5_t_cke_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE];
            end
         end
         if (rwselect[2032] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_ckesr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR] & regb_freq2_ch0_dramset1tmg5_t_ckesr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
            end
         end
         if (rwselect[2032] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_cksre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] & regb_freq2_ch0_dramset1tmg5_t_cksre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
            end
         end
         if (rwselect[2032] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_cksrx[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] & regb_freq2_ch0_dramset1tmg5_t_cksrx_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG6
   //------------------------
         if (rwselect[2033] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ckcsx[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] & regb_freq2_ch0_dramset1tmg6_t_ckcsx_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG7
   //------------------------
         if (rwselect[2034] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_csh[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH] & regb_freq2_ch0_dramset1tmg7_t_csh_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG9
   //------------------------
         if (rwselect[2036] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wr2rd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] & regb_freq2_ch0_dramset1tmg9_wr2rd_s_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
            end
         end
         if (rwselect[2036] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_rrd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] & regb_freq2_ch0_dramset1tmg9_t_rrd_s_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
            end
         end
         if (rwselect[2036] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ccd_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] & regb_freq2_ch0_dramset1tmg9_t_ccd_s_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG12
   //------------------------
         if (rwselect[2039] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_cmdcke[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] & regb_freq2_ch0_dramset1tmg12_t_cmdcke_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG13
   //------------------------
         if (rwselect[2040] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ppd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD] & regb_freq2_ch0_dramset1tmg13_t_ppd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD];
            end
         end
         if (rwselect[2040] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_ccd_mw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] & regb_freq2_ch0_dramset1tmg13_t_ccd_mw_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
            end
         end
         if (rwselect[2040] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_odtloff[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] & regb_freq2_ch0_dramset1tmg13_odtloff_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG14
   //------------------------
         if (rwselect[2041] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_xsr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR] & regb_freq2_ch0_dramset1tmg14_t_xsr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR];
            end
         end
         if (rwselect[2041] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_osco[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO] & regb_freq2_ch0_dramset1tmg14_t_osco_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG17
   //------------------------
         if (rwselect[2044] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_vrcg_disable[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] & regb_freq2_ch0_dramset1tmg17_t_vrcg_disable_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
            end
         end
         if (rwselect[2044] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_vrcg_enable[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] & regb_freq2_ch0_dramset1tmg17_t_vrcg_enable_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG23
   //------------------------
         if (rwselect[2049] && write_en) begin
            ff_regb_freq2_ch0_t_pdn[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN] & regb_freq2_ch0_dramset1tmg23_t_pdn_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN];
         end
         if (rwselect[2049] && write_en) begin
            ff_regb_freq2_ch0_t_xsr_dsm_x1024[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] & regb_freq2_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG24
   //------------------------
         if (rwselect[2050] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_max_wr_sync[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] & regb_freq2_ch0_dramset1tmg24_max_wr_sync_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
            end
         end
         if (rwselect[2050] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_max_rd_sync[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] & regb_freq2_ch0_dramset1tmg24_max_rd_sync_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
            end
         end
         if (rwselect[2050] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rd2wr_s[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] & regb_freq2_ch0_dramset1tmg24_rd2wr_s_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
            end
         end
         if (rwselect[2050] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_bank_org[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] & regb_freq2_ch0_dramset1tmg24_bank_org_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG25
   //------------------------
         if (rwselect[2051] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rda2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] & regb_freq2_ch0_dramset1tmg25_rda2pre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
            end
         end
         if (rwselect[2051] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wra2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] & regb_freq2_ch0_dramset1tmg25_wra2pre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
            end
         end
         if (rwselect[2051] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] & regb_freq2_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG30
   //------------------------
         if (rwselect[2056] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_mrr2rd[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD] & regb_freq2_ch0_dramset1tmg30_mrr2rd_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
            end
         end
         if (rwselect[2056] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_mrr2wr[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR] & regb_freq2_ch0_dramset1tmg30_mrr2wr_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
            end
         end
         if (rwselect[2056] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_mrr2mrw[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] & regb_freq2_ch0_dramset1tmg30_mrr2mrw_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG32
   //------------------------
         if (rwselect[2058] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_ws_fs2wck_sus[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] & regb_freq2_ch0_dramset1tmg32_ws_fs2wck_sus_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
            end
         end
         if (rwselect[2058] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_wcksus[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] & regb_freq2_ch0_dramset1tmg32_t_wcksus_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
            end
         end
         if (rwselect[2058] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_ws_off2ws_fs[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] & regb_freq2_ch0_dramset1tmg32_ws_off2ws_fs_mask[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR0
   //------------------------
         if (rwselect[2089] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_emr[(`REGB_FREQ2_CH0_SIZE_INITMR0_EMR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ2_CH0_SIZE_INITMR0_EMR] & regb_freq2_ch0_initmr0_emr_mask[`REGB_FREQ2_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ2_CH0_SIZE_INITMR0_EMR];
            end
         end
         if (rwselect[2089] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr[(`REGB_FREQ2_CH0_SIZE_INITMR0_MR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ2_CH0_SIZE_INITMR0_MR] & regb_freq2_ch0_initmr0_mr_mask[`REGB_FREQ2_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ2_CH0_SIZE_INITMR0_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR1
   //------------------------
         if (rwselect[2090] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_emr3[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ2_CH0_SIZE_INITMR1_EMR3] & regb_freq2_ch0_initmr1_emr3_mask[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ2_CH0_SIZE_INITMR1_EMR3];
            end
         end
         if (rwselect[2090] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_emr2[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ2_CH0_SIZE_INITMR1_EMR2] & regb_freq2_ch0_initmr1_emr2_mask[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ2_CH0_SIZE_INITMR1_EMR2];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR2
   //------------------------
         if (rwselect[2091] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr5[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR5) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ2_CH0_SIZE_INITMR2_MR5] & regb_freq2_ch0_initmr2_mr5_mask[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ2_CH0_SIZE_INITMR2_MR5];
            end
         end
         if (rwselect[2091] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr4[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR4) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ2_CH0_SIZE_INITMR2_MR4] & regb_freq2_ch0_initmr2_mr4_mask[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ2_CH0_SIZE_INITMR2_MR4];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR3
   //------------------------
         if (rwselect[2092] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr6[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR6) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ2_CH0_SIZE_INITMR3_MR6] & regb_freq2_ch0_initmr3_mr6_mask[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ2_CH0_SIZE_INITMR3_MR6];
            end
         end
         if (rwselect[2092] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr22[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR22) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ2_CH0_SIZE_INITMR3_MR22] & regb_freq2_ch0_initmr3_mr22_mask[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ2_CH0_SIZE_INITMR3_MR22];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG0
   //------------------------
         if (rwselect[2093] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_tphy_wrlat[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] & regb_freq2_ch0_dfitmg0_dfi_tphy_wrlat_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
            end
         end
         if (rwselect[2093] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_tphy_wrdata[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] & regb_freq2_ch0_dfitmg0_dfi_tphy_wrdata_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
            end
         end
         if (rwselect[2093] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_t_rddata_en[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] & regb_freq2_ch0_dfitmg0_dfi_t_rddata_en_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
            end
         end
         if (rwselect[2093] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_t_ctrl_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] & regb_freq2_ch0_dfitmg0_dfi_t_ctrl_delay_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG1
   //------------------------
         if (rwselect[2094] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] & regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_enable_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
            end
         end
         if (rwselect[2094] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] & regb_freq2_ch0_dfitmg1_dfi_t_dram_clk_disable_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
            end
         end
         if (rwselect[2094] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_dfi_t_wrdata_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] & regb_freq2_ch0_dfitmg1_dfi_t_wrdata_delay_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG2
   //------------------------
         if (rwselect[2095] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_tphy_wrcslat[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] & regb_freq2_ch0_dfitmg2_dfi_tphy_wrcslat_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
            end
         end
         if (rwselect[2095] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_tphy_rdcslat[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] & regb_freq2_ch0_dfitmg2_dfi_tphy_rdcslat_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
            end
         end
         if (rwselect[2095] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_delay[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] & regb_freq2_ch0_dfitmg2_dfi_twck_delay_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG4
   //------------------------
         if (rwselect[2097] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_dis[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] & regb_freq2_ch0_dfitmg4_dfi_twck_dis_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
            end
         end
         if (rwselect[2097] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_en_fs[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] & regb_freq2_ch0_dfitmg4_dfi_twck_en_fs_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
            end
         end
         if (rwselect[2097] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_en_wr[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] & regb_freq2_ch0_dfitmg4_dfi_twck_en_wr_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
            end
         end
         if (rwselect[2097] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_en_rd[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] & regb_freq2_ch0_dfitmg4_dfi_twck_en_rd_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG5
   //------------------------
         if (rwselect[2098] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] & regb_freq2_ch0_dfitmg5_dfi_twck_toggle_post_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
            end
         end
         if (rwselect[2098] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_cs[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] & regb_freq2_ch0_dfitmg5_dfi_twck_toggle_cs_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
            end
         end
         if (rwselect[2098] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_toggle[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] & regb_freq2_ch0_dfitmg5_dfi_twck_toggle_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
            end
         end
         if (rwselect[2098] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_fast_toggle[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] & regb_freq2_ch0_dfitmg5_dfi_twck_fast_toggle_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG6
   //------------------------
         if (rwselect[2099] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] & regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
            end
         end
         if (rwselect[2099] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_twck_toggle_post_rd_en <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] & regb_freq2_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG1
   //------------------------
         if (rwselect[2101] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] & regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
            end
         end
         if (rwselect[2101] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] & regb_freq2_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG2
   //------------------------
         if (rwselect[2102] && write_en) begin
            ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] & regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
         end
         if (rwselect[2102] && write_en) begin
            ff_regb_freq2_ch0_ctrlupd_after_dqsosc <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] & regb_freq2_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
         end
         if (rwselect[2102] && write_en) begin
            ff_regb_freq2_ch0_ppt2_override <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] & regb_freq2_ch0_dfiupdtmg2_ppt2_override_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
         end
         if (rwselect[2102] && write_en) begin
            ff_regb_freq2_ch0_ppt2_en <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_EN] & regb_freq2_ch0_dfiupdtmg2_ppt2_en_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
         end
         if (rwselect[2102] && write_en) begin
            ff_regb_freq2_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] & regb_freq2_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG3
   //------------------------
         if (rwselect[2103] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] & regb_freq2_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG0
   //------------------------
         if (rwselect[2104] && write_en) begin
            ff_regb_freq2_ch0_t_refi_x1_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] & regb_freq2_ch0_rfshset1tmg0_t_refi_x1_x32_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
         end
         if (rwselect[2104] && write_en) begin
            ff_regb_freq2_ch0_refresh_to_x1_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] & regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_x32_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
         end
         if (rwselect[2104] && write_en) begin
            ff_regb_freq2_ch0_refresh_margin[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] & regb_freq2_ch0_rfshset1tmg0_refresh_margin_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
         end
         if (rwselect[2104] && write_en) begin
            ff_regb_freq2_ch0_refresh_to_x1_sel <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] & regb_freq2_ch0_rfshset1tmg0_refresh_to_x1_sel_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
         end
         if (rwselect[2104] && write_en) begin
            ff_regb_freq2_ch0_t_refi_x1_sel <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] & regb_freq2_ch0_rfshset1tmg0_t_refi_x1_sel_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG1
   //------------------------
         if (rwselect[2105] && write_en) begin
            ff_regb_freq2_ch0_t_rfc_min[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] & regb_freq2_ch0_rfshset1tmg1_t_rfc_min_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
         end
         if (rwselect[2105] && write_en) begin
            ff_regb_freq2_ch0_t_rfc_min_ab[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] & regb_freq2_ch0_rfshset1tmg1_t_rfc_min_ab_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG2
   //------------------------
         if (rwselect[2106] && write_en) begin
            ff_regb_freq2_ch0_t_pbr2pbr[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] & regb_freq2_ch0_rfshset1tmg2_t_pbr2pbr_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
         end
         if (rwselect[2106] && write_en) begin
            ff_regb_freq2_ch0_t_pbr2act[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] & regb_freq2_ch0_rfshset1tmg2_t_pbr2act_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG3
   //------------------------
         if (rwselect[2107] && write_en) begin
            ff_regb_freq2_ch0_refresh_to_ab_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] & regb_freq2_ch0_rfshset1tmg3_refresh_to_ab_x32_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG4
   //------------------------
         if (rwselect[2108] && write_en) begin
            ff_regb_freq2_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] & regb_freq2_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
         end
         if (rwselect[2108] && write_en) begin
            ff_regb_freq2_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] & regb_freq2_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RFMSET1TMG0
   //------------------------
         if (rwselect[2118] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_t_rfmpb[(`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB] & regb_freq2_ch0_rfmset1tmg0_t_rfmpb_mask[`REGB_FREQ2_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG0
   //------------------------
         if (rwselect[2129] && write_en) begin
            ff_regb_freq2_ch0_t_zq_long_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] & regb_freq2_ch0_zqset1tmg0_t_zq_long_nop_mask[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
         end
         if (rwselect[2129] && write_en) begin
            ff_regb_freq2_ch0_t_zq_short_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] & regb_freq2_ch0_zqset1tmg0_t_zq_short_nop_mask[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG1
   //------------------------
         if (rwselect[2130] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_zq_short_interval_x1024[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] & regb_freq2_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
            end
         end
         if (rwselect[2130] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_zq_reset_nop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] & regb_freq2_ch0_zqset1tmg1_t_zq_reset_nop_mask[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG2
   //------------------------
         if (rwselect[2131] && write_en) begin
            ff_regb_freq2_ch0_t_zq_stop[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] & regb_freq2_ch0_zqset1tmg2_t_zq_stop_mask[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DQSOSCCTL0
   //------------------------
         if (rwselect[2140] && write_en) begin
            ff_regb_freq2_ch0_dqsosc_enable <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] & regb_freq2_ch0_dqsoscctl0_dqsosc_enable_mask[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
         end
         if (rwselect[2140] && write_en) begin
            ff_regb_freq2_ch0_dqsosc_interval_unit <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] & regb_freq2_ch0_dqsoscctl0_dqsosc_interval_unit_mask[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
         end
         if (rwselect[2140] && write_en) begin
            ff_regb_freq2_ch0_dqsosc_interval[(`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] & regb_freq2_ch0_dqsoscctl0_dqsosc_interval_mask[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEINT
   //------------------------
         if (rwselect[2141] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_mr4_read_interval[(`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] & regb_freq2_ch0_derateint_mr4_read_interval_mask[`REGB_FREQ2_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL0
   //------------------------
         if (rwselect[2142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_rrd[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] & regb_freq2_ch0_derateval0_derated_t_rrd_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
            end
         end
         if (rwselect[2142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_rp[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP] & regb_freq2_ch0_derateval0_derated_t_rp_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
            end
         end
         if (rwselect[2142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_ras_min[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] & regb_freq2_ch0_derateval0_derated_t_ras_min_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
            end
         end
         if (rwselect[2142] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_rcd[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] & regb_freq2_ch0_derateval0_derated_t_rcd_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL1
   //------------------------
         if (rwselect[2143] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_rc[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC] & regb_freq2_ch0_derateval1_derated_t_rc_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
            end
         end
         if (rwselect[2143] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_derated_t_rcd_write[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] & regb_freq2_ch0_derateval1_derated_t_rcd_write_mask[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.HWLPTMG0
   //------------------------
         if (rwselect[2144] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_hw_lp_idle_x32[(`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] & regb_freq2_ch0_hwlptmg0_hw_lp_idle_x32_mask[`REGB_FREQ2_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DVFSCTL0
   //------------------------
         if (rwselect[2145] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_dvfsq_enable <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ2_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] & regb_freq2_ch0_dvfsctl0_dvfsq_enable_mask[`REGB_FREQ2_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ2_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.SCHEDTMG0
   //------------------------
         if (rwselect[2146] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_pageclose_timer[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] & regb_freq2_ch0_schedtmg0_pageclose_timer_mask[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
            end
         end
         if (rwselect[2146] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rdwr_idle_gap[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] & regb_freq2_ch0_schedtmg0_rdwr_idle_gap_mask[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFHPR1
   //------------------------
         if (rwselect[2147] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_hpr_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] & regb_freq2_ch0_perfhpr1_hpr_max_starve_mask[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
            end
         end
         if (rwselect[2147] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_hpr_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] & regb_freq2_ch0_perfhpr1_hpr_xact_run_length_mask[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFLPR1
   //------------------------
         if (rwselect[2148] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_lpr_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] & regb_freq2_ch0_perflpr1_lpr_max_starve_mask[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
            end
         end
         if (rwselect[2148] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_lpr_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] & regb_freq2_ch0_perflpr1_lpr_xact_run_length_mask[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.PERFWR1
   //------------------------
         if (rwselect[2149] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_w_max_starve[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE] & regb_freq2_ch0_perfwr1_w_max_starve_mask[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE];
            end
         end
         if (rwselect[2149] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_w_xact_run_length[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] & regb_freq2_ch0_perfwr1_w_xact_run_length_mask[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.TMGCFG
   //------------------------
         if (rwselect[2150] && write_en) begin
            ff_regb_freq2_ch0_frequency_ratio <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ2_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] & regb_freq2_ch0_tmgcfg_frequency_ratio_mask[`REGB_FREQ2_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ2_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG0
   //------------------------
         if (rwselect[2151] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_diff_rank_rd_gap[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] & regb_freq2_ch0_ranktmg0_diff_rank_rd_gap_mask[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
            end
         end
         if (rwselect[2151] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_diff_rank_wr_gap[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] & regb_freq2_ch0_ranktmg0_diff_rank_wr_gap_mask[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG1
   //------------------------
         if (rwselect[2152] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_wr2rd_dr[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR] & regb_freq2_ch0_ranktmg1_wr2rd_dr_mask[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR];
            end
         end
         if (rwselect[2152] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_rd2wr_dr[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR] & regb_freq2_ch0_ranktmg1_rd2wr_dr_mask[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.PWRTMG
   //------------------------
         if (rwselect[2153] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_powerdown_to_x32[(`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] & regb_freq2_ch0_pwrtmg_powerdown_to_x32_mask[`REGB_FREQ2_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
            end
         end
         if (rwselect[2153] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_selfref_to_x32[(`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32] & regb_freq2_ch0_pwrtmg_selfref_to_x32_mask[`REGB_FREQ2_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG0
   //------------------------
         if (rwselect[2159] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_pgm_x1_x1024[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] & regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
            end
         end
         if (rwselect[2159] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_pgm_x1_sel <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] & regb_freq2_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG1
   //------------------------
         if (rwselect[2160] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_pgmpst_x32[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] & regb_freq2_ch0_ddr4pprtmg1_t_pgmpst_x32_mask[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
            end
         end
         if (rwselect[2160] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq2_ch0_t_pgm_exit[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] & regb_freq2_ch0_ddr4pprtmg1_t_pgm_exit_mask[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
            end
         end
   //------------------------
   // Register REGB_FREQ2_CH0.LNKECCCTL0
   //------------------------
         if (rwselect[2161] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_wr_link_ecc_enable <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ2_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] & regb_freq2_ch0_lnkeccctl0_wr_link_ecc_enable_mask[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ2_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
            end
         end
         if (rwselect[2161] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq2_ch0_rd_link_ecc_enable <= apb_data_expanded[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ2_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] & regb_freq2_ch0_lnkeccctl0_rd_link_ecc_enable_mask[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ2_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG0
   //------------------------
         if (rwselect[2295] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ras_min[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN] & regb_freq3_ch0_dramset1tmg0_t_ras_min_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
            end
         end
         if (rwselect[2295] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ras_max[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX] & regb_freq3_ch0_dramset1tmg0_t_ras_max_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
            end
         end
         if (rwselect[2295] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_faw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW] & regb_freq3_ch0_dramset1tmg0_t_faw_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_FAW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW];
            end
         end
         if (rwselect[2295] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wr2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE] & regb_freq3_ch0_dramset1tmg0_wr2pre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_WR2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG1
   //------------------------
         if (rwselect[2296] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rc[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC] & regb_freq3_ch0_dramset1tmg1_t_rc_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC];
            end
         end
         if (rwselect[2296] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rd2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE] & regb_freq3_ch0_dramset1tmg1_rd2pre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_RD2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
            end
         end
         if (rwselect[2296] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_xp[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP] & regb_freq3_ch0_dramset1tmg1_t_xp_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_XP +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP];
            end
         end
         if (rwselect[2296] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rcd_write[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE] & regb_freq3_ch0_dramset1tmg1_t_rcd_write_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG2
   //------------------------
         if (rwselect[2297] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wr2rd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD] & regb_freq3_ch0_dramset1tmg2_wr2rd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WR2RD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD];
            end
         end
         if (rwselect[2297] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rd2wr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR] & regb_freq3_ch0_dramset1tmg2_rd2wr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_RD2WR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR];
            end
         end
         if (rwselect[2297] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_read_latency[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY] & regb_freq3_ch0_dramset1tmg2_read_latency_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
            end
         end
         if (rwselect[2297] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_write_latency[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY] & regb_freq3_ch0_dramset1tmg2_write_latency_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG3
   //------------------------
         if (rwselect[2298] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wr2mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR] & regb_freq3_ch0_dramset1tmg3_wr2mr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_WR2MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR];
            end
         end
         if (rwselect[2298] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rd2mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR] & regb_freq3_ch0_dramset1tmg3_rd2mr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_RD2MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR];
            end
         end
         if (rwselect[2298] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_mr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR] & regb_freq3_ch0_dramset1tmg3_t_mr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_T_MR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG4
   //------------------------
         if (rwselect[2299] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rp[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP] & regb_freq3_ch0_dramset1tmg4_t_rp_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RP +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP];
            end
         end
         if (rwselect[2299] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rrd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD] & regb_freq3_ch0_dramset1tmg4_t_rrd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RRD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD];
            end
         end
         if (rwselect[2299] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ccd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD] & regb_freq3_ch0_dramset1tmg4_t_ccd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_CCD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD];
            end
         end
         if (rwselect[2299] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rcd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD] & regb_freq3_ch0_dramset1tmg4_t_rcd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RCD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG5
   //------------------------
         if (rwselect[2300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_cke[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE] & regb_freq3_ch0_dramset1tmg5_t_cke_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE];
            end
         end
         if (rwselect[2300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_ckesr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR] & regb_freq3_ch0_dramset1tmg5_t_ckesr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKESR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
            end
         end
         if (rwselect[2300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_cksre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE] & regb_freq3_ch0_dramset1tmg5_t_cksre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
            end
         end
         if (rwselect[2300] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_cksrx[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX] & regb_freq3_ch0_dramset1tmg5_t_cksrx_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG6
   //------------------------
         if (rwselect[2301] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ckcsx[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX] & regb_freq3_ch0_dramset1tmg6_t_ckcsx_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG7
   //------------------------
         if (rwselect[2302] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_csh[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH] & regb_freq3_ch0_dramset1tmg7_t_csh_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG7_T_CSH +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG9
   //------------------------
         if (rwselect[2304] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wr2rd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S] & regb_freq3_ch0_dramset1tmg9_wr2rd_s_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
            end
         end
         if (rwselect[2304] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_rrd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S] & regb_freq3_ch0_dramset1tmg9_t_rrd_s_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
            end
         end
         if (rwselect[2304] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ccd_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S] & regb_freq3_ch0_dramset1tmg9_t_ccd_s_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG12
   //------------------------
         if (rwselect[2307] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_cmdcke[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE] & regb_freq3_ch0_dramset1tmg12_t_cmdcke_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG13
   //------------------------
         if (rwselect[2308] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ppd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD] & regb_freq3_ch0_dramset1tmg13_t_ppd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_PPD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD];
            end
         end
         if (rwselect[2308] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_ccd_mw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW] & regb_freq3_ch0_dramset1tmg13_t_ccd_mw_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
            end
         end
         if (rwselect[2308] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_odtloff[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF] & regb_freq3_ch0_dramset1tmg13_odtloff_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG14
   //------------------------
         if (rwselect[2309] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_xsr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR] & regb_freq3_ch0_dramset1tmg14_t_xsr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_XSR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR];
            end
         end
         if (rwselect[2309] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_osco[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO] & regb_freq3_ch0_dramset1tmg14_t_osco_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_OSCO +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG17
   //------------------------
         if (rwselect[2312] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_vrcg_disable[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE] & regb_freq3_ch0_dramset1tmg17_t_vrcg_disable_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
            end
         end
         if (rwselect[2312] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_vrcg_enable[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE] & regb_freq3_ch0_dramset1tmg17_t_vrcg_enable_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG23
   //------------------------
         if (rwselect[2317] && write_en) begin
            ff_regb_freq3_ch0_t_pdn[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN] & regb_freq3_ch0_dramset1tmg23_t_pdn_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_PDN +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN];
         end
         if (rwselect[2317] && write_en) begin
            ff_regb_freq3_ch0_t_xsr_dsm_x1024[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024] & regb_freq3_ch0_dramset1tmg23_t_xsr_dsm_x1024_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024 +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG24
   //------------------------
         if (rwselect[2318] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_max_wr_sync[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC] & regb_freq3_ch0_dramset1tmg24_max_wr_sync_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
            end
         end
         if (rwselect[2318] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_max_rd_sync[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC] & regb_freq3_ch0_dramset1tmg24_max_rd_sync_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
            end
         end
         if (rwselect[2318] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rd2wr_s[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S] & regb_freq3_ch0_dramset1tmg24_rd2wr_s_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
            end
         end
         if (rwselect[2318] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_bank_org[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG] & regb_freq3_ch0_dramset1tmg24_bank_org_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG25
   //------------------------
         if (rwselect[2319] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rda2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE] & regb_freq3_ch0_dramset1tmg25_rda2pre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
            end
         end
         if (rwselect[2319] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wra2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE] & regb_freq3_ch0_dramset1tmg25_wra2pre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
            end
         end
         if (rwselect[2319] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_lpddr4_diff_bank_rwa2pre[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE] & regb_freq3_ch0_dramset1tmg25_lpddr4_diff_bank_rwa2pre_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG30
   //------------------------
         if (rwselect[2324] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_mrr2rd[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD] & regb_freq3_ch0_dramset1tmg30_mrr2rd_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2RD +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
            end
         end
         if (rwselect[2324] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_mrr2wr[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR] & regb_freq3_ch0_dramset1tmg30_mrr2wr_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2WR +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
            end
         end
         if (rwselect[2324] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_mrr2mrw[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW] & regb_freq3_ch0_dramset1tmg30_mrr2mrw_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG32
   //------------------------
         if (rwselect[2326] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_ws_fs2wck_sus[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS] & regb_freq3_ch0_dramset1tmg32_ws_fs2wck_sus_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
            end
         end
         if (rwselect[2326] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_wcksus[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS] & regb_freq3_ch0_dramset1tmg32_t_wcksus_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
            end
         end
         if (rwselect[2326] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_ws_off2ws_fs[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS] & regb_freq3_ch0_dramset1tmg32_ws_off2ws_fs_mask[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS +: `REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR0
   //------------------------
         if (rwselect[2357] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_emr[(`REGB_FREQ3_CH0_SIZE_INITMR0_EMR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ3_CH0_SIZE_INITMR0_EMR] & regb_freq3_ch0_initmr0_emr_mask[`REGB_FREQ3_CH0_OFFSET_INITMR0_EMR +: `REGB_FREQ3_CH0_SIZE_INITMR0_EMR];
            end
         end
         if (rwselect[2357] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr[(`REGB_FREQ3_CH0_SIZE_INITMR0_MR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ3_CH0_SIZE_INITMR0_MR] & regb_freq3_ch0_initmr0_mr_mask[`REGB_FREQ3_CH0_OFFSET_INITMR0_MR +: `REGB_FREQ3_CH0_SIZE_INITMR0_MR];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR1
   //------------------------
         if (rwselect[2358] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_emr3[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ3_CH0_SIZE_INITMR1_EMR3] & regb_freq3_ch0_initmr1_emr3_mask[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR3 +: `REGB_FREQ3_CH0_SIZE_INITMR1_EMR3];
            end
         end
         if (rwselect[2358] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_emr2[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ3_CH0_SIZE_INITMR1_EMR2] & regb_freq3_ch0_initmr1_emr2_mask[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR2 +: `REGB_FREQ3_CH0_SIZE_INITMR1_EMR2];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR2
   //------------------------
         if (rwselect[2359] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr5[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR5) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ3_CH0_SIZE_INITMR2_MR5] & regb_freq3_ch0_initmr2_mr5_mask[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR5 +: `REGB_FREQ3_CH0_SIZE_INITMR2_MR5];
            end
         end
         if (rwselect[2359] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr4[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR4) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ3_CH0_SIZE_INITMR2_MR4] & regb_freq3_ch0_initmr2_mr4_mask[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR4 +: `REGB_FREQ3_CH0_SIZE_INITMR2_MR4];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR3
   //------------------------
         if (rwselect[2360] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr6[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR6) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ3_CH0_SIZE_INITMR3_MR6] & regb_freq3_ch0_initmr3_mr6_mask[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR6 +: `REGB_FREQ3_CH0_SIZE_INITMR3_MR6];
            end
         end
         if (rwselect[2360] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr22[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR22) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ3_CH0_SIZE_INITMR3_MR22] & regb_freq3_ch0_initmr3_mr22_mask[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR22 +: `REGB_FREQ3_CH0_SIZE_INITMR3_MR22];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG0
   //------------------------
         if (rwselect[2361] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_tphy_wrlat[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT] & regb_freq3_ch0_dfitmg0_dfi_tphy_wrlat_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
            end
         end
         if (rwselect[2361] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_tphy_wrdata[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA] & regb_freq3_ch0_dfitmg0_dfi_tphy_wrdata_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
            end
         end
         if (rwselect[2361] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_t_rddata_en[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN] & regb_freq3_ch0_dfitmg0_dfi_t_rddata_en_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
            end
         end
         if (rwselect[2361] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_t_ctrl_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY] & regb_freq3_ch0_dfitmg0_dfi_t_ctrl_delay_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG1
   //------------------------
         if (rwselect[2362] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_t_dram_clk_enable[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE] & regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_enable_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
            end
         end
         if (rwselect[2362] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_t_dram_clk_disable[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE] & regb_freq3_ch0_dfitmg1_dfi_t_dram_clk_disable_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
            end
         end
         if (rwselect[2362] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_dfi_t_wrdata_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY] & regb_freq3_ch0_dfitmg1_dfi_t_wrdata_delay_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG2
   //------------------------
         if (rwselect[2363] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_tphy_wrcslat[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT] & regb_freq3_ch0_dfitmg2_dfi_tphy_wrcslat_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
            end
         end
         if (rwselect[2363] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_tphy_rdcslat[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT] & regb_freq3_ch0_dfitmg2_dfi_tphy_rdcslat_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
            end
         end
         if (rwselect[2363] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_delay[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY] & regb_freq3_ch0_dfitmg2_dfi_twck_delay_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY +: `REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG4
   //------------------------
         if (rwselect[2365] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_dis[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS] & regb_freq3_ch0_dfitmg4_dfi_twck_dis_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
            end
         end
         if (rwselect[2365] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_en_fs[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS] & regb_freq3_ch0_dfitmg4_dfi_twck_en_fs_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
            end
         end
         if (rwselect[2365] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_en_wr[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR] & regb_freq3_ch0_dfitmg4_dfi_twck_en_wr_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
            end
         end
         if (rwselect[2365] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_en_rd[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD] & regb_freq3_ch0_dfitmg4_dfi_twck_en_rd_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD +: `REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG5
   //------------------------
         if (rwselect[2366] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST] & regb_freq3_ch0_dfitmg5_dfi_twck_toggle_post_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
            end
         end
         if (rwselect[2366] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_cs[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS] & regb_freq3_ch0_dfitmg5_dfi_twck_toggle_cs_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
            end
         end
         if (rwselect[2366] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_toggle[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE] & regb_freq3_ch0_dfitmg5_dfi_twck_toggle_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
            end
         end
         if (rwselect[2366] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_fast_toggle[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE] & regb_freq3_ch0_dfitmg5_dfi_twck_fast_toggle_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE +: `REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG6
   //------------------------
         if (rwselect[2367] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd[(`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD] & regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD +: `REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
            end
         end
         if (rwselect[2367] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_twck_toggle_post_rd_en <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN] & regb_freq3_ch0_dfitmg6_dfi_twck_toggle_post_rd_en_mask[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN +: `REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG1
   //------------------------
         if (rwselect[2369] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_max_x1024[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024] & regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_max_x1024_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
            end
         end
         if (rwselect[2369] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_min_x1024[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024] & regb_freq3_ch0_dfiupdtmg1_dfi_t_ctrlupd_interval_min_x1024_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG2
   //------------------------
         if (rwselect[2370] && write_en) begin
            ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1] & regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
         end
         if (rwselect[2370] && write_en) begin
            ff_regb_freq3_ch0_ctrlupd_after_dqsosc <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC] & regb_freq3_ch0_dfiupdtmg2_ctrlupd_after_dqsosc_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
         end
         if (rwselect[2370] && write_en) begin
            ff_regb_freq3_ch0_ppt2_override <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE] & regb_freq3_ch0_dfiupdtmg2_ppt2_override_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
         end
         if (rwselect[2370] && write_en) begin
            ff_regb_freq3_ch0_ppt2_en <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_EN] & regb_freq3_ch0_dfiupdtmg2_ppt2_en_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_EN +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
         end
         if (rwselect[2370] && write_en) begin
            ff_regb_freq3_ch0_dfi_t_ctrlupd_interval_type1_unit[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT] & regb_freq3_ch0_dfiupdtmg2_dfi_t_ctrlupd_interval_type1_unit_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG3
   //------------------------
         if (rwselect[2371] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dfi_t_ctrlupd_burst_interval_x8[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8] & regb_freq3_ch0_dfiupdtmg3_dfi_t_ctrlupd_burst_interval_x8_mask[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8 +: `REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG0
   //------------------------
         if (rwselect[2372] && write_en) begin
            ff_regb_freq3_ch0_t_refi_x1_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32] & regb_freq3_ch0_rfshset1tmg0_t_refi_x1_x32_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
         end
         if (rwselect[2372] && write_en) begin
            ff_regb_freq3_ch0_refresh_to_x1_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32] & regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_x32_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
         end
         if (rwselect[2372] && write_en) begin
            ff_regb_freq3_ch0_refresh_margin[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN] & regb_freq3_ch0_rfshset1tmg0_refresh_margin_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
         end
         if (rwselect[2372] && write_en) begin
            ff_regb_freq3_ch0_refresh_to_x1_sel <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL] & regb_freq3_ch0_rfshset1tmg0_refresh_to_x1_sel_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
         end
         if (rwselect[2372] && write_en) begin
            ff_regb_freq3_ch0_t_refi_x1_sel <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL] & regb_freq3_ch0_rfshset1tmg0_t_refi_x1_sel_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG1
   //------------------------
         if (rwselect[2373] && write_en) begin
            ff_regb_freq3_ch0_t_rfc_min[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN] & regb_freq3_ch0_rfshset1tmg1_t_rfc_min_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
         end
         if (rwselect[2373] && write_en) begin
            ff_regb_freq3_ch0_t_rfc_min_ab[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB] & regb_freq3_ch0_rfshset1tmg1_t_rfc_min_ab_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG2
   //------------------------
         if (rwselect[2374] && write_en) begin
            ff_regb_freq3_ch0_t_pbr2pbr[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR] & regb_freq3_ch0_rfshset1tmg2_t_pbr2pbr_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
         end
         if (rwselect[2374] && write_en) begin
            ff_regb_freq3_ch0_t_pbr2act[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT] & regb_freq3_ch0_rfshset1tmg2_t_pbr2act_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG3
   //------------------------
         if (rwselect[2375] && write_en) begin
            ff_regb_freq3_ch0_refresh_to_ab_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32] & regb_freq3_ch0_rfshset1tmg3_refresh_to_ab_x32_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG4
   //------------------------
         if (rwselect[2376] && write_en) begin
            ff_regb_freq3_ch0_refresh_timer0_start_value_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32] & regb_freq3_ch0_rfshset1tmg4_refresh_timer0_start_value_x32_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
         end
         if (rwselect[2376] && write_en) begin
            ff_regb_freq3_ch0_refresh_timer1_start_value_x32[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32] & regb_freq3_ch0_rfshset1tmg4_refresh_timer1_start_value_x32_mask[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32 +: `REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RFMSET1TMG0
   //------------------------
         if (rwselect[2386] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_t_rfmpb[(`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB] & regb_freq3_ch0_rfmset1tmg0_t_rfmpb_mask[`REGB_FREQ3_CH0_OFFSET_RFMSET1TMG0_T_RFMPB +: `REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG0
   //------------------------
         if (rwselect[2397] && write_en) begin
            ff_regb_freq3_ch0_t_zq_long_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP] & regb_freq3_ch0_zqset1tmg0_t_zq_long_nop_mask[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
         end
         if (rwselect[2397] && write_en) begin
            ff_regb_freq3_ch0_t_zq_short_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP] & regb_freq3_ch0_zqset1tmg0_t_zq_short_nop_mask[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG1
   //------------------------
         if (rwselect[2398] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_zq_short_interval_x1024[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024] & regb_freq3_ch0_zqset1tmg1_t_zq_short_interval_x1024_mask[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024 +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
            end
         end
         if (rwselect[2398] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_zq_reset_nop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP] & regb_freq3_ch0_zqset1tmg1_t_zq_reset_nop_mask[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG2
   //------------------------
         if (rwselect[2399] && write_en) begin
            ff_regb_freq3_ch0_t_zq_stop[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP] & regb_freq3_ch0_zqset1tmg2_t_zq_stop_mask[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP +: `REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DQSOSCCTL0
   //------------------------
         if (rwselect[2408] && write_en) begin
            ff_regb_freq3_ch0_dqsosc_enable <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE] & regb_freq3_ch0_dqsoscctl0_dqsosc_enable_mask[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
         end
         if (rwselect[2408] && write_en) begin
            ff_regb_freq3_ch0_dqsosc_interval_unit <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT] & regb_freq3_ch0_dqsoscctl0_dqsosc_interval_unit_mask[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
         end
         if (rwselect[2408] && write_en) begin
            ff_regb_freq3_ch0_dqsosc_interval[(`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL] & regb_freq3_ch0_dqsoscctl0_dqsosc_interval_mask[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL +: `REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEINT
   //------------------------
         if (rwselect[2409] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_mr4_read_interval[(`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL] & regb_freq3_ch0_derateint_mr4_read_interval_mask[`REGB_FREQ3_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL +: `REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL0
   //------------------------
         if (rwselect[2410] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_rrd[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD] & regb_freq3_ch0_derateval0_derated_t_rrd_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
            end
         end
         if (rwselect[2410] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_rp[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP] & regb_freq3_ch0_derateval0_derated_t_rp_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RP +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
            end
         end
         if (rwselect[2410] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_ras_min[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN] & regb_freq3_ch0_derateval0_derated_t_ras_min_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
            end
         end
         if (rwselect[2410] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_rcd[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD] & regb_freq3_ch0_derateval0_derated_t_rcd_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD +: `REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL1
   //------------------------
         if (rwselect[2411] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_rc[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC] & regb_freq3_ch0_derateval1_derated_t_rc_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RC +: `REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
            end
         end
         if (rwselect[2411] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_derated_t_rcd_write[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE] & regb_freq3_ch0_derateval1_derated_t_rcd_write_mask[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE +: `REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.HWLPTMG0
   //------------------------
         if (rwselect[2412] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_hw_lp_idle_x32[(`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32] & regb_freq3_ch0_hwlptmg0_hw_lp_idle_x32_mask[`REGB_FREQ3_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32 +: `REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DVFSCTL0
   //------------------------
         if (rwselect[2413] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_dvfsq_enable <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ3_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE] & regb_freq3_ch0_dvfsctl0_dvfsq_enable_mask[`REGB_FREQ3_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE +: `REGB_FREQ3_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.SCHEDTMG0
   //------------------------
         if (rwselect[2414] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_pageclose_timer[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER] & regb_freq3_ch0_schedtmg0_pageclose_timer_mask[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER +: `REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
            end
         end
         if (rwselect[2414] && write_en) begin
            if (static_wr_en_core_ddrc_core_clk == 1'b0) begin // static write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rdwr_idle_gap[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP] & regb_freq3_ch0_schedtmg0_rdwr_idle_gap_mask[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP +: `REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFHPR1
   //------------------------
         if (rwselect[2415] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_hpr_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE] & regb_freq3_ch0_perfhpr1_hpr_max_starve_mask[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
            end
         end
         if (rwselect[2415] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_hpr_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH] & regb_freq3_ch0_perfhpr1_hpr_xact_run_length_mask[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFLPR1
   //------------------------
         if (rwselect[2416] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_lpr_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE] & regb_freq3_ch0_perflpr1_lpr_max_starve_mask[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
            end
         end
         if (rwselect[2416] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_lpr_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH] & regb_freq3_ch0_perflpr1_lpr_xact_run_length_mask[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.PERFWR1
   //------------------------
         if (rwselect[2417] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_w_max_starve[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE] & regb_freq3_ch0_perfwr1_w_max_starve_mask[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_MAX_STARVE +: `REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE];
            end
         end
         if (rwselect[2417] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_w_xact_run_length[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH] & regb_freq3_ch0_perfwr1_w_xact_run_length_mask[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH +: `REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.TMGCFG
   //------------------------
         if (rwselect[2418] && write_en) begin
            ff_regb_freq3_ch0_frequency_ratio <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ3_CH0_SIZE_TMGCFG_FREQUENCY_RATIO] & regb_freq3_ch0_tmgcfg_frequency_ratio_mask[`REGB_FREQ3_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO +: `REGB_FREQ3_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG0
   //------------------------
         if (rwselect[2419] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_diff_rank_rd_gap[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP] & regb_freq3_ch0_ranktmg0_diff_rank_rd_gap_mask[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP +: `REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
            end
         end
         if (rwselect[2419] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_diff_rank_wr_gap[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP] & regb_freq3_ch0_ranktmg0_diff_rank_wr_gap_mask[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP +: `REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG1
   //------------------------
         if (rwselect[2420] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_wr2rd_dr[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR] & regb_freq3_ch0_ranktmg1_wr2rd_dr_mask[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_WR2RD_DR +: `REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR];
            end
         end
         if (rwselect[2420] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_rd2wr_dr[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR] & regb_freq3_ch0_ranktmg1_rd2wr_dr_mask[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_RD2WR_DR +: `REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.PWRTMG
   //------------------------
         if (rwselect[2421] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_powerdown_to_x32[(`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32] & regb_freq3_ch0_pwrtmg_powerdown_to_x32_mask[`REGB_FREQ3_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32 +: `REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
            end
         end
         if (rwselect[2421] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_selfref_to_x32[(`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32] & regb_freq3_ch0_pwrtmg_selfref_to_x32_mask[`REGB_FREQ3_CH0_OFFSET_PWRTMG_SELFREF_TO_X32 +: `REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG0
   //------------------------
         if (rwselect[2427] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_pgm_x1_x1024[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024] & regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_x1024_mask[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024 +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
            end
         end
         if (rwselect[2427] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_pgm_x1_sel <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL] & regb_freq3_ch0_ddr4pprtmg0_t_pgm_x1_sel_mask[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG1
   //------------------------
         if (rwselect[2428] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_pgmpst_x32[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32] & regb_freq3_ch0_ddr4pprtmg1_t_pgmpst_x32_mask[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32 +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
            end
         end
         if (rwselect[2428] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               cfgs_ff_regb_freq3_ch0_t_pgm_exit[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT] & regb_freq3_ch0_ddr4pprtmg1_t_pgm_exit_mask[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT +: `REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
            end
         end
   //------------------------
   // Register REGB_FREQ3_CH0.LNKECCCTL0
   //------------------------
         if (rwselect[2429] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_wr_link_ecc_enable <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ3_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE] & regb_freq3_ch0_lnkeccctl0_wr_link_ecc_enable_mask[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE +: `REGB_FREQ3_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
            end
         end
         if (rwselect[2429] && write_en) begin
            if (quasi_dyn_wr_en_core_ddrc_core_clk == 1'b0) begin // quasi dynamic write enable @core_ddrc_core_clk
               ff_regb_freq3_ch0_rd_link_ecc_enable <= apb_data_expanded[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ3_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE] & regb_freq3_ch0_lnkeccctl0_rd_link_ecc_enable_mask[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE +: `REGB_FREQ3_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
            end
         end

      end 
   end


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

  // Check that ff_rank0_refresh_todo goes to 1 at least once.
  property p_apb_ff_todo_is_one(ff_todo_signal);
    @(posedge pclk) disable iff(!presetn)
         (ff_todo_signal == 0);
  endproperty

  a_antoniot_ff_regb_ddrc_ch0_zq_reset_todo_is_1 : assert property (p_apb_ff_todo_is_one(ff_regb_ddrc_ch0_zq_reset_todo)) else
    `SNPS_SVA_MSG("ERROR", "CODE COVERAGE assertion to check that ff_regb_ddrc_ch0_zq_reset_todo goes to 1. Please, assign to antoniot.");

  a_antoniot_ff_zq_calib_short_todo_is_1 : assert property (p_apb_ff_todo_is_one(ff_regb_ddrc_ch0_zq_calib_short_todo)) else
    `SNPS_SVA_MSG("ERROR", "CODE COVERAGE assertion to check that ff_regb_ddrc_ch0_zq_calib_short_todo goes to 1. Please, assign to antoniot.");

`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

endmodule
