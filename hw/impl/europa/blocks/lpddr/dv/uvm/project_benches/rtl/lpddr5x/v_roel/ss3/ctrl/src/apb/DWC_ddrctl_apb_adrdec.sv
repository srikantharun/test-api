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

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddrctl_apb_adrdec.sv#14 $
`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"

module DWC_ddrctl_apb_adrdec
import DWC_ddrctl_reg_pkg::*;
  #(parameter APB_AW       = 16,
    parameter APB_DW       = 32,
    parameter REG_WIDTH    = 32,    
    parameter N_REGS       = `UMCTL2_REGS_N_REGS,
    parameter RW_REGS      = `UMCTL2_REGS_RW_REGS,
    parameter RWSELWIDTH   = RW_REGS,
    parameter N_APBFSMSTAT =
                            5
    )
   (input                       presetn,
    input                       pclk,
    input [APB_AW-1:2]          paddr,
    input                       pwrite,
    input                       psel,
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Secure access is not supported    
    input                       apb_secure,
//spyglass enable_block W240
    input [N_APBFSMSTAT-1:0]    apb_slv_ns,
    output reg [RWSELWIDTH-1:0] rwselect,
    output     [APB_DW-1:0]     prdata,
    output reg                  pslverr
   ,input [REG_WIDTH -1:0] r0_mstr0
   ,input [REG_WIDTH -1:0] r2_mstr2
   ,input [REG_WIDTH -1:0] r4_mstr4
   ,input [REG_WIDTH -1:0] r5_stat
   ,input [REG_WIDTH -1:0] r8_mrctrl0
   ,input [REG_WIDTH -1:0] r9_mrctrl1
   ,input [REG_WIDTH -1:0] r11_mrstat
   ,input [REG_WIDTH -1:0] r12_mrrdata0
   ,input [REG_WIDTH -1:0] r13_mrrdata1
   ,input [REG_WIDTH -1:0] r14_deratectl0
   ,input [REG_WIDTH -1:0] r15_deratectl1
   ,input [REG_WIDTH -1:0] r16_deratectl2
   ,input [REG_WIDTH -1:0] r19_deratectl5
   ,input [REG_WIDTH -1:0] r20_deratectl6
   ,input [REG_WIDTH -1:0] r22_deratestat0
   ,input [REG_WIDTH -1:0] r24_deratedbgctl
   ,input [REG_WIDTH -1:0] r25_deratedbgstat
   ,input [REG_WIDTH -1:0] r26_pwrctl
   ,input [REG_WIDTH -1:0] r27_hwlpctl
   ,input [REG_WIDTH -1:0] r29_clkgatectl
   ,input [REG_WIDTH -1:0] r30_rfshmod0
   ,input [REG_WIDTH -1:0] r32_rfshctl0
   ,input [REG_WIDTH -1:0] r33_rfmmod0
   ,input [REG_WIDTH -1:0] r34_rfmmod1
   ,input [REG_WIDTH -1:0] r35_rfmctl
   ,input [REG_WIDTH -1:0] r36_rfmstat
   ,input [REG_WIDTH -1:0] r37_zqctl0
   ,input [REG_WIDTH -1:0] r38_zqctl1
   ,input [REG_WIDTH -1:0] r39_zqctl2
   ,input [REG_WIDTH -1:0] r40_zqstat
   ,input [REG_WIDTH -1:0] r41_dqsoscruntime
   ,input [REG_WIDTH -1:0] r42_dqsoscstat0
   ,input [REG_WIDTH -1:0] r43_dqsosccfg0
   ,input [REG_WIDTH -1:0] r45_sched0
   ,input [REG_WIDTH -1:0] r46_sched1
   ,input [REG_WIDTH -1:0] r48_sched3
   ,input [REG_WIDTH -1:0] r49_sched4
   ,input [REG_WIDTH -1:0] r50_sched5
   ,input [REG_WIDTH -1:0] r51_hwffcctl
   ,input [REG_WIDTH -1:0] r52_hwffcstat
   ,input [REG_WIDTH -1:0] r62_dfilpcfg0
   ,input [REG_WIDTH -1:0] r63_dfiupd0
   ,input [REG_WIDTH -1:0] r65_dfimisc
   ,input [REG_WIDTH -1:0] r66_dfistat
   ,input [REG_WIDTH -1:0] r67_dfiphymstr
   ,input [REG_WIDTH -1:0] r77_poisoncfg
   ,input [REG_WIDTH -1:0] r78_poisonstat
   ,input [REG_WIDTH -1:0] r79_ecccfg0
   ,input [REG_WIDTH -1:0] r80_ecccfg1
   ,input [REG_WIDTH -1:0] r81_eccstat
   ,input [REG_WIDTH -1:0] r82_eccctl
   ,input [REG_WIDTH -1:0] r83_eccerrcnt
   ,input [REG_WIDTH -1:0] r84_ecccaddr0
   ,input [REG_WIDTH -1:0] r85_ecccaddr1
   ,input [REG_WIDTH -1:0] r86_ecccsyn0
   ,input [REG_WIDTH -1:0] r87_ecccsyn1
   ,input [REG_WIDTH -1:0] r88_ecccsyn2
   ,input [REG_WIDTH -1:0] r89_eccbitmask0
   ,input [REG_WIDTH -1:0] r90_eccbitmask1
   ,input [REG_WIDTH -1:0] r91_eccbitmask2
   ,input [REG_WIDTH -1:0] r92_eccuaddr0
   ,input [REG_WIDTH -1:0] r93_eccuaddr1
   ,input [REG_WIDTH -1:0] r94_eccusyn0
   ,input [REG_WIDTH -1:0] r95_eccusyn1
   ,input [REG_WIDTH -1:0] r96_eccusyn2
   ,input [REG_WIDTH -1:0] r97_eccpoisonaddr0
   ,input [REG_WIDTH -1:0] r98_eccpoisonaddr1
   ,input [REG_WIDTH -1:0] r101_eccpoisonpat0
   ,input [REG_WIDTH -1:0] r103_eccpoisonpat2
   ,input [REG_WIDTH -1:0] r104_eccapstat
   ,input [REG_WIDTH -1:0] r161_lnkeccctl1
   ,input [REG_WIDTH -1:0] r162_lnkeccpoisonctl0
   ,input [REG_WIDTH -1:0] r163_lnkeccpoisonstat
   ,input [REG_WIDTH -1:0] r164_lnkeccindex
   ,input [REG_WIDTH -1:0] r165_lnkeccerrcnt0
   ,input [REG_WIDTH -1:0] r166_lnkeccerrstat
   ,input [REG_WIDTH -1:0] r175_lnkecccaddr0
   ,input [REG_WIDTH -1:0] r176_lnkecccaddr1
   ,input [REG_WIDTH -1:0] r177_lnkeccuaddr0
   ,input [REG_WIDTH -1:0] r178_lnkeccuaddr1
   ,input [REG_WIDTH -1:0] r234_opctrl0
   ,input [REG_WIDTH -1:0] r235_opctrl1
   ,input [REG_WIDTH -1:0] r236_opctrlcam
   ,input [REG_WIDTH -1:0] r237_opctrlcmd
   ,input [REG_WIDTH -1:0] r238_opctrlstat
   ,input [REG_WIDTH -1:0] r239_opctrlcam1
   ,input [REG_WIDTH -1:0] r240_oprefctrl0
   ,input [REG_WIDTH -1:0] r242_oprefstat0
   ,input [REG_WIDTH -1:0] r249_swctl
   ,input [REG_WIDTH -1:0] r250_swstat
   ,input [REG_WIDTH -1:0] r253_rankctl
   ,input [REG_WIDTH -1:0] r254_dbictl
   ,input [REG_WIDTH -1:0] r256_odtmap
   ,input [REG_WIDTH -1:0] r257_datactl0
   ,input [REG_WIDTH -1:0] r258_swctlstatic
   ,input [REG_WIDTH -1:0] r259_cgctl
   ,input [REG_WIDTH -1:0] r260_inittmg0
   ,input [REG_WIDTH -1:0] r285_ppt2ctrl0
   ,input [REG_WIDTH -1:0] r286_ppt2stat0
   ,input [REG_WIDTH -1:0] r289_ddrctl_ver_number
   ,input [REG_WIDTH -1:0] r290_ddrctl_ver_type
   ,input [REG_WIDTH -1:0] r495_addrmap1_map0
   ,input [REG_WIDTH -1:0] r497_addrmap3_map0
   ,input [REG_WIDTH -1:0] r498_addrmap4_map0
   ,input [REG_WIDTH -1:0] r499_addrmap5_map0
   ,input [REG_WIDTH -1:0] r500_addrmap6_map0
   ,input [REG_WIDTH -1:0] r501_addrmap7_map0
   ,input [REG_WIDTH -1:0] r502_addrmap8_map0
   ,input [REG_WIDTH -1:0] r503_addrmap9_map0
   ,input [REG_WIDTH -1:0] r504_addrmap10_map0
   ,input [REG_WIDTH -1:0] r505_addrmap11_map0
   ,input [REG_WIDTH -1:0] r506_addrmap12_map0
   ,input [REG_WIDTH -1:0] r521_pccfg_port0
   ,input [REG_WIDTH -1:0] r522_pcfgr_port0
   ,input [REG_WIDTH -1:0] r523_pcfgw_port0
   ,input [REG_WIDTH -1:0] r556_pctrl_port0
   ,input [REG_WIDTH -1:0] r557_pcfgqos0_port0
   ,input [REG_WIDTH -1:0] r558_pcfgqos1_port0
   ,input [REG_WIDTH -1:0] r559_pcfgwqos0_port0
   ,input [REG_WIDTH -1:0] r560_pcfgwqos1_port0
   ,input [REG_WIDTH -1:0] r569_sbrctl_port0
   ,input [REG_WIDTH -1:0] r570_sbrstat_port0
   ,input [REG_WIDTH -1:0] r571_sbrwdata0_port0
   ,input [REG_WIDTH -1:0] r573_sbrstart0_port0
   ,input [REG_WIDTH -1:0] r574_sbrstart1_port0
   ,input [REG_WIDTH -1:0] r575_sbrrange0_port0
   ,input [REG_WIDTH -1:0] r576_sbrrange1_port0
   ,input [REG_WIDTH -1:0] r582_pstat_port0
   ,input [REG_WIDTH -1:0] r1929_dramset1tmg0_freq0
   ,input [REG_WIDTH -1:0] r1930_dramset1tmg1_freq0
   ,input [REG_WIDTH -1:0] r1931_dramset1tmg2_freq0
   ,input [REG_WIDTH -1:0] r1932_dramset1tmg3_freq0
   ,input [REG_WIDTH -1:0] r1933_dramset1tmg4_freq0
   ,input [REG_WIDTH -1:0] r1934_dramset1tmg5_freq0
   ,input [REG_WIDTH -1:0] r1935_dramset1tmg6_freq0
   ,input [REG_WIDTH -1:0] r1936_dramset1tmg7_freq0
   ,input [REG_WIDTH -1:0] r1938_dramset1tmg9_freq0
   ,input [REG_WIDTH -1:0] r1941_dramset1tmg12_freq0
   ,input [REG_WIDTH -1:0] r1942_dramset1tmg13_freq0
   ,input [REG_WIDTH -1:0] r1943_dramset1tmg14_freq0
   ,input [REG_WIDTH -1:0] r1946_dramset1tmg17_freq0
   ,input [REG_WIDTH -1:0] r1951_dramset1tmg23_freq0
   ,input [REG_WIDTH -1:0] r1952_dramset1tmg24_freq0
   ,input [REG_WIDTH -1:0] r1953_dramset1tmg25_freq0
   ,input [REG_WIDTH -1:0] r1958_dramset1tmg30_freq0
   ,input [REG_WIDTH -1:0] r1960_dramset1tmg32_freq0
   ,input [REG_WIDTH -1:0] r1991_initmr0_freq0
   ,input [REG_WIDTH -1:0] r1992_initmr1_freq0
   ,input [REG_WIDTH -1:0] r1993_initmr2_freq0
   ,input [REG_WIDTH -1:0] r1994_initmr3_freq0
   ,input [REG_WIDTH -1:0] r1995_dfitmg0_freq0
   ,input [REG_WIDTH -1:0] r1996_dfitmg1_freq0
   ,input [REG_WIDTH -1:0] r1997_dfitmg2_freq0
   ,input [REG_WIDTH -1:0] r1999_dfitmg4_freq0
   ,input [REG_WIDTH -1:0] r2000_dfitmg5_freq0
   ,input [REG_WIDTH -1:0] r2001_dfitmg6_freq0
   ,input [REG_WIDTH -1:0] r2003_dfilptmg0_freq0
   ,input [REG_WIDTH -1:0] r2004_dfilptmg1_freq0
   ,input [REG_WIDTH -1:0] r2005_dfiupdtmg0_freq0
   ,input [REG_WIDTH -1:0] r2006_dfiupdtmg1_freq0
   ,input [REG_WIDTH -1:0] r2008_dfiupdtmg2_freq0
   ,input [REG_WIDTH -1:0] r2009_dfiupdtmg3_freq0
   ,input [REG_WIDTH -1:0] r2010_rfshset1tmg0_freq0
   ,input [REG_WIDTH -1:0] r2011_rfshset1tmg1_freq0
   ,input [REG_WIDTH -1:0] r2012_rfshset1tmg2_freq0
   ,input [REG_WIDTH -1:0] r2013_rfshset1tmg3_freq0
   ,input [REG_WIDTH -1:0] r2014_rfshset1tmg4_freq0
   ,input [REG_WIDTH -1:0] r2024_rfmset1tmg0_freq0
   ,input [REG_WIDTH -1:0] r2035_zqset1tmg0_freq0
   ,input [REG_WIDTH -1:0] r2036_zqset1tmg1_freq0
   ,input [REG_WIDTH -1:0] r2037_zqset1tmg2_freq0
   ,input [REG_WIDTH -1:0] r2046_dqsoscctl0_freq0
   ,input [REG_WIDTH -1:0] r2047_derateint_freq0
   ,input [REG_WIDTH -1:0] r2048_derateval0_freq0
   ,input [REG_WIDTH -1:0] r2049_derateval1_freq0
   ,input [REG_WIDTH -1:0] r2050_hwlptmg0_freq0
   ,input [REG_WIDTH -1:0] r2051_dvfsctl0_freq0
   ,input [REG_WIDTH -1:0] r2052_schedtmg0_freq0
   ,input [REG_WIDTH -1:0] r2053_perfhpr1_freq0
   ,input [REG_WIDTH -1:0] r2054_perflpr1_freq0
   ,input [REG_WIDTH -1:0] r2055_perfwr1_freq0
   ,input [REG_WIDTH -1:0] r2056_tmgcfg_freq0
   ,input [REG_WIDTH -1:0] r2057_ranktmg0_freq0
   ,input [REG_WIDTH -1:0] r2058_ranktmg1_freq0
   ,input [REG_WIDTH -1:0] r2059_pwrtmg_freq0
   ,input [REG_WIDTH -1:0] r2065_ddr4pprtmg0_freq0
   ,input [REG_WIDTH -1:0] r2066_ddr4pprtmg1_freq0
   ,input [REG_WIDTH -1:0] r2067_lnkeccctl0_freq0
   ,input [REG_WIDTH -1:0] r2201_dramset1tmg0_freq1
   ,input [REG_WIDTH -1:0] r2202_dramset1tmg1_freq1
   ,input [REG_WIDTH -1:0] r2203_dramset1tmg2_freq1
   ,input [REG_WIDTH -1:0] r2204_dramset1tmg3_freq1
   ,input [REG_WIDTH -1:0] r2205_dramset1tmg4_freq1
   ,input [REG_WIDTH -1:0] r2206_dramset1tmg5_freq1
   ,input [REG_WIDTH -1:0] r2207_dramset1tmg6_freq1
   ,input [REG_WIDTH -1:0] r2208_dramset1tmg7_freq1
   ,input [REG_WIDTH -1:0] r2210_dramset1tmg9_freq1
   ,input [REG_WIDTH -1:0] r2213_dramset1tmg12_freq1
   ,input [REG_WIDTH -1:0] r2214_dramset1tmg13_freq1
   ,input [REG_WIDTH -1:0] r2215_dramset1tmg14_freq1
   ,input [REG_WIDTH -1:0] r2218_dramset1tmg17_freq1
   ,input [REG_WIDTH -1:0] r2223_dramset1tmg23_freq1
   ,input [REG_WIDTH -1:0] r2224_dramset1tmg24_freq1
   ,input [REG_WIDTH -1:0] r2225_dramset1tmg25_freq1
   ,input [REG_WIDTH -1:0] r2230_dramset1tmg30_freq1
   ,input [REG_WIDTH -1:0] r2232_dramset1tmg32_freq1
   ,input [REG_WIDTH -1:0] r2263_initmr0_freq1
   ,input [REG_WIDTH -1:0] r2264_initmr1_freq1
   ,input [REG_WIDTH -1:0] r2265_initmr2_freq1
   ,input [REG_WIDTH -1:0] r2266_initmr3_freq1
   ,input [REG_WIDTH -1:0] r2267_dfitmg0_freq1
   ,input [REG_WIDTH -1:0] r2268_dfitmg1_freq1
   ,input [REG_WIDTH -1:0] r2269_dfitmg2_freq1
   ,input [REG_WIDTH -1:0] r2271_dfitmg4_freq1
   ,input [REG_WIDTH -1:0] r2272_dfitmg5_freq1
   ,input [REG_WIDTH -1:0] r2273_dfitmg6_freq1
   ,input [REG_WIDTH -1:0] r2275_dfiupdtmg1_freq1
   ,input [REG_WIDTH -1:0] r2276_dfiupdtmg2_freq1
   ,input [REG_WIDTH -1:0] r2277_dfiupdtmg3_freq1
   ,input [REG_WIDTH -1:0] r2278_rfshset1tmg0_freq1
   ,input [REG_WIDTH -1:0] r2279_rfshset1tmg1_freq1
   ,input [REG_WIDTH -1:0] r2280_rfshset1tmg2_freq1
   ,input [REG_WIDTH -1:0] r2281_rfshset1tmg3_freq1
   ,input [REG_WIDTH -1:0] r2282_rfshset1tmg4_freq1
   ,input [REG_WIDTH -1:0] r2292_rfmset1tmg0_freq1
   ,input [REG_WIDTH -1:0] r2303_zqset1tmg0_freq1
   ,input [REG_WIDTH -1:0] r2304_zqset1tmg1_freq1
   ,input [REG_WIDTH -1:0] r2305_zqset1tmg2_freq1
   ,input [REG_WIDTH -1:0] r2314_dqsoscctl0_freq1
   ,input [REG_WIDTH -1:0] r2315_derateint_freq1
   ,input [REG_WIDTH -1:0] r2316_derateval0_freq1
   ,input [REG_WIDTH -1:0] r2317_derateval1_freq1
   ,input [REG_WIDTH -1:0] r2318_hwlptmg0_freq1
   ,input [REG_WIDTH -1:0] r2319_dvfsctl0_freq1
   ,input [REG_WIDTH -1:0] r2320_schedtmg0_freq1
   ,input [REG_WIDTH -1:0] r2321_perfhpr1_freq1
   ,input [REG_WIDTH -1:0] r2322_perflpr1_freq1
   ,input [REG_WIDTH -1:0] r2323_perfwr1_freq1
   ,input [REG_WIDTH -1:0] r2324_tmgcfg_freq1
   ,input [REG_WIDTH -1:0] r2325_ranktmg0_freq1
   ,input [REG_WIDTH -1:0] r2326_ranktmg1_freq1
   ,input [REG_WIDTH -1:0] r2327_pwrtmg_freq1
   ,input [REG_WIDTH -1:0] r2333_ddr4pprtmg0_freq1
   ,input [REG_WIDTH -1:0] r2334_ddr4pprtmg1_freq1
   ,input [REG_WIDTH -1:0] r2335_lnkeccctl0_freq1
   ,input [REG_WIDTH -1:0] r2469_dramset1tmg0_freq2
   ,input [REG_WIDTH -1:0] r2470_dramset1tmg1_freq2
   ,input [REG_WIDTH -1:0] r2471_dramset1tmg2_freq2
   ,input [REG_WIDTH -1:0] r2472_dramset1tmg3_freq2
   ,input [REG_WIDTH -1:0] r2473_dramset1tmg4_freq2
   ,input [REG_WIDTH -1:0] r2474_dramset1tmg5_freq2
   ,input [REG_WIDTH -1:0] r2475_dramset1tmg6_freq2
   ,input [REG_WIDTH -1:0] r2476_dramset1tmg7_freq2
   ,input [REG_WIDTH -1:0] r2478_dramset1tmg9_freq2
   ,input [REG_WIDTH -1:0] r2481_dramset1tmg12_freq2
   ,input [REG_WIDTH -1:0] r2482_dramset1tmg13_freq2
   ,input [REG_WIDTH -1:0] r2483_dramset1tmg14_freq2
   ,input [REG_WIDTH -1:0] r2486_dramset1tmg17_freq2
   ,input [REG_WIDTH -1:0] r2491_dramset1tmg23_freq2
   ,input [REG_WIDTH -1:0] r2492_dramset1tmg24_freq2
   ,input [REG_WIDTH -1:0] r2493_dramset1tmg25_freq2
   ,input [REG_WIDTH -1:0] r2498_dramset1tmg30_freq2
   ,input [REG_WIDTH -1:0] r2500_dramset1tmg32_freq2
   ,input [REG_WIDTH -1:0] r2531_initmr0_freq2
   ,input [REG_WIDTH -1:0] r2532_initmr1_freq2
   ,input [REG_WIDTH -1:0] r2533_initmr2_freq2
   ,input [REG_WIDTH -1:0] r2534_initmr3_freq2
   ,input [REG_WIDTH -1:0] r2535_dfitmg0_freq2
   ,input [REG_WIDTH -1:0] r2536_dfitmg1_freq2
   ,input [REG_WIDTH -1:0] r2537_dfitmg2_freq2
   ,input [REG_WIDTH -1:0] r2539_dfitmg4_freq2
   ,input [REG_WIDTH -1:0] r2540_dfitmg5_freq2
   ,input [REG_WIDTH -1:0] r2541_dfitmg6_freq2
   ,input [REG_WIDTH -1:0] r2543_dfiupdtmg1_freq2
   ,input [REG_WIDTH -1:0] r2544_dfiupdtmg2_freq2
   ,input [REG_WIDTH -1:0] r2545_dfiupdtmg3_freq2
   ,input [REG_WIDTH -1:0] r2546_rfshset1tmg0_freq2
   ,input [REG_WIDTH -1:0] r2547_rfshset1tmg1_freq2
   ,input [REG_WIDTH -1:0] r2548_rfshset1tmg2_freq2
   ,input [REG_WIDTH -1:0] r2549_rfshset1tmg3_freq2
   ,input [REG_WIDTH -1:0] r2550_rfshset1tmg4_freq2
   ,input [REG_WIDTH -1:0] r2560_rfmset1tmg0_freq2
   ,input [REG_WIDTH -1:0] r2571_zqset1tmg0_freq2
   ,input [REG_WIDTH -1:0] r2572_zqset1tmg1_freq2
   ,input [REG_WIDTH -1:0] r2573_zqset1tmg2_freq2
   ,input [REG_WIDTH -1:0] r2582_dqsoscctl0_freq2
   ,input [REG_WIDTH -1:0] r2583_derateint_freq2
   ,input [REG_WIDTH -1:0] r2584_derateval0_freq2
   ,input [REG_WIDTH -1:0] r2585_derateval1_freq2
   ,input [REG_WIDTH -1:0] r2586_hwlptmg0_freq2
   ,input [REG_WIDTH -1:0] r2587_dvfsctl0_freq2
   ,input [REG_WIDTH -1:0] r2588_schedtmg0_freq2
   ,input [REG_WIDTH -1:0] r2589_perfhpr1_freq2
   ,input [REG_WIDTH -1:0] r2590_perflpr1_freq2
   ,input [REG_WIDTH -1:0] r2591_perfwr1_freq2
   ,input [REG_WIDTH -1:0] r2592_tmgcfg_freq2
   ,input [REG_WIDTH -1:0] r2593_ranktmg0_freq2
   ,input [REG_WIDTH -1:0] r2594_ranktmg1_freq2
   ,input [REG_WIDTH -1:0] r2595_pwrtmg_freq2
   ,input [REG_WIDTH -1:0] r2601_ddr4pprtmg0_freq2
   ,input [REG_WIDTH -1:0] r2602_ddr4pprtmg1_freq2
   ,input [REG_WIDTH -1:0] r2603_lnkeccctl0_freq2
   ,input [REG_WIDTH -1:0] r2737_dramset1tmg0_freq3
   ,input [REG_WIDTH -1:0] r2738_dramset1tmg1_freq3
   ,input [REG_WIDTH -1:0] r2739_dramset1tmg2_freq3
   ,input [REG_WIDTH -1:0] r2740_dramset1tmg3_freq3
   ,input [REG_WIDTH -1:0] r2741_dramset1tmg4_freq3
   ,input [REG_WIDTH -1:0] r2742_dramset1tmg5_freq3
   ,input [REG_WIDTH -1:0] r2743_dramset1tmg6_freq3
   ,input [REG_WIDTH -1:0] r2744_dramset1tmg7_freq3
   ,input [REG_WIDTH -1:0] r2746_dramset1tmg9_freq3
   ,input [REG_WIDTH -1:0] r2749_dramset1tmg12_freq3
   ,input [REG_WIDTH -1:0] r2750_dramset1tmg13_freq3
   ,input [REG_WIDTH -1:0] r2751_dramset1tmg14_freq3
   ,input [REG_WIDTH -1:0] r2754_dramset1tmg17_freq3
   ,input [REG_WIDTH -1:0] r2759_dramset1tmg23_freq3
   ,input [REG_WIDTH -1:0] r2760_dramset1tmg24_freq3
   ,input [REG_WIDTH -1:0] r2761_dramset1tmg25_freq3
   ,input [REG_WIDTH -1:0] r2766_dramset1tmg30_freq3
   ,input [REG_WIDTH -1:0] r2768_dramset1tmg32_freq3
   ,input [REG_WIDTH -1:0] r2799_initmr0_freq3
   ,input [REG_WIDTH -1:0] r2800_initmr1_freq3
   ,input [REG_WIDTH -1:0] r2801_initmr2_freq3
   ,input [REG_WIDTH -1:0] r2802_initmr3_freq3
   ,input [REG_WIDTH -1:0] r2803_dfitmg0_freq3
   ,input [REG_WIDTH -1:0] r2804_dfitmg1_freq3
   ,input [REG_WIDTH -1:0] r2805_dfitmg2_freq3
   ,input [REG_WIDTH -1:0] r2807_dfitmg4_freq3
   ,input [REG_WIDTH -1:0] r2808_dfitmg5_freq3
   ,input [REG_WIDTH -1:0] r2809_dfitmg6_freq3
   ,input [REG_WIDTH -1:0] r2811_dfiupdtmg1_freq3
   ,input [REG_WIDTH -1:0] r2812_dfiupdtmg2_freq3
   ,input [REG_WIDTH -1:0] r2813_dfiupdtmg3_freq3
   ,input [REG_WIDTH -1:0] r2814_rfshset1tmg0_freq3
   ,input [REG_WIDTH -1:0] r2815_rfshset1tmg1_freq3
   ,input [REG_WIDTH -1:0] r2816_rfshset1tmg2_freq3
   ,input [REG_WIDTH -1:0] r2817_rfshset1tmg3_freq3
   ,input [REG_WIDTH -1:0] r2818_rfshset1tmg4_freq3
   ,input [REG_WIDTH -1:0] r2828_rfmset1tmg0_freq3
   ,input [REG_WIDTH -1:0] r2839_zqset1tmg0_freq3
   ,input [REG_WIDTH -1:0] r2840_zqset1tmg1_freq3
   ,input [REG_WIDTH -1:0] r2841_zqset1tmg2_freq3
   ,input [REG_WIDTH -1:0] r2850_dqsoscctl0_freq3
   ,input [REG_WIDTH -1:0] r2851_derateint_freq3
   ,input [REG_WIDTH -1:0] r2852_derateval0_freq3
   ,input [REG_WIDTH -1:0] r2853_derateval1_freq3
   ,input [REG_WIDTH -1:0] r2854_hwlptmg0_freq3
   ,input [REG_WIDTH -1:0] r2855_dvfsctl0_freq3
   ,input [REG_WIDTH -1:0] r2856_schedtmg0_freq3
   ,input [REG_WIDTH -1:0] r2857_perfhpr1_freq3
   ,input [REG_WIDTH -1:0] r2858_perflpr1_freq3
   ,input [REG_WIDTH -1:0] r2859_perfwr1_freq3
   ,input [REG_WIDTH -1:0] r2860_tmgcfg_freq3
   ,input [REG_WIDTH -1:0] r2861_ranktmg0_freq3
   ,input [REG_WIDTH -1:0] r2862_ranktmg1_freq3
   ,input [REG_WIDTH -1:0] r2863_pwrtmg_freq3
   ,input [REG_WIDTH -1:0] r2869_ddr4pprtmg0_freq3
   ,input [REG_WIDTH -1:0] r2870_ddr4pprtmg1_freq3
   ,input [REG_WIDTH -1:0] r2871_lnkeccctl0_freq3

    );   

   localparam IDLE       = 5'b00001;
   localparam ADDRDECODE = 5'b00010;
   localparam SAMPLERDY  = 5'b01000;
   localparam SELWIDTH   = N_REGS;

   localparam REG_AW = APB_AW - 2;
   localparam REGB_DDRC_CH0_MSTR0_ADDR = `REGB_DDRC_CH0_MSTR0_ADDR;
   localparam REGB_DDRC_CH0_MSTR2_ADDR = `REGB_DDRC_CH0_MSTR2_ADDR;
   localparam REGB_DDRC_CH0_MSTR4_ADDR = `REGB_DDRC_CH0_MSTR4_ADDR;
   localparam REGB_DDRC_CH0_STAT_ADDR = `REGB_DDRC_CH0_STAT_ADDR;
   localparam REGB_DDRC_CH0_MRCTRL0_ADDR = `REGB_DDRC_CH0_MRCTRL0_ADDR;
   localparam REGB_DDRC_CH0_MRCTRL1_ADDR = `REGB_DDRC_CH0_MRCTRL1_ADDR;
   localparam REGB_DDRC_CH0_MRSTAT_ADDR = `REGB_DDRC_CH0_MRSTAT_ADDR;
   localparam REGB_DDRC_CH0_MRRDATA0_ADDR = `REGB_DDRC_CH0_MRRDATA0_ADDR;
   localparam REGB_DDRC_CH0_MRRDATA1_ADDR = `REGB_DDRC_CH0_MRRDATA1_ADDR;
   localparam REGB_DDRC_CH0_DERATECTL0_ADDR = `REGB_DDRC_CH0_DERATECTL0_ADDR;
   localparam REGB_DDRC_CH0_DERATECTL1_ADDR = `REGB_DDRC_CH0_DERATECTL1_ADDR;
   localparam REGB_DDRC_CH0_DERATECTL2_ADDR = `REGB_DDRC_CH0_DERATECTL2_ADDR;
   localparam REGB_DDRC_CH0_DERATECTL5_ADDR = `REGB_DDRC_CH0_DERATECTL5_ADDR;
   localparam REGB_DDRC_CH0_DERATECTL6_ADDR = `REGB_DDRC_CH0_DERATECTL6_ADDR;
   localparam REGB_DDRC_CH0_DERATESTAT0_ADDR = `REGB_DDRC_CH0_DERATESTAT0_ADDR;
   localparam REGB_DDRC_CH0_DERATEDBGCTL_ADDR = `REGB_DDRC_CH0_DERATEDBGCTL_ADDR;
   localparam REGB_DDRC_CH0_DERATEDBGSTAT_ADDR = `REGB_DDRC_CH0_DERATEDBGSTAT_ADDR;
   localparam REGB_DDRC_CH0_PWRCTL_ADDR = `REGB_DDRC_CH0_PWRCTL_ADDR;
   localparam REGB_DDRC_CH0_HWLPCTL_ADDR = `REGB_DDRC_CH0_HWLPCTL_ADDR;
   localparam REGB_DDRC_CH0_CLKGATECTL_ADDR = `REGB_DDRC_CH0_CLKGATECTL_ADDR;
   localparam REGB_DDRC_CH0_RFSHMOD0_ADDR = `REGB_DDRC_CH0_RFSHMOD0_ADDR;
   localparam REGB_DDRC_CH0_RFSHCTL0_ADDR = `REGB_DDRC_CH0_RFSHCTL0_ADDR;
   localparam REGB_DDRC_CH0_RFMMOD0_ADDR = `REGB_DDRC_CH0_RFMMOD0_ADDR;
   localparam REGB_DDRC_CH0_RFMMOD1_ADDR = `REGB_DDRC_CH0_RFMMOD1_ADDR;
   localparam REGB_DDRC_CH0_RFMCTL_ADDR = `REGB_DDRC_CH0_RFMCTL_ADDR;
   localparam REGB_DDRC_CH0_RFMSTAT_ADDR = `REGB_DDRC_CH0_RFMSTAT_ADDR;
   localparam REGB_DDRC_CH0_ZQCTL0_ADDR = `REGB_DDRC_CH0_ZQCTL0_ADDR;
   localparam REGB_DDRC_CH0_ZQCTL1_ADDR = `REGB_DDRC_CH0_ZQCTL1_ADDR;
   localparam REGB_DDRC_CH0_ZQCTL2_ADDR = `REGB_DDRC_CH0_ZQCTL2_ADDR;
   localparam REGB_DDRC_CH0_ZQSTAT_ADDR = `REGB_DDRC_CH0_ZQSTAT_ADDR;
   localparam REGB_DDRC_CH0_DQSOSCRUNTIME_ADDR = `REGB_DDRC_CH0_DQSOSCRUNTIME_ADDR;
   localparam REGB_DDRC_CH0_DQSOSCSTAT0_ADDR = `REGB_DDRC_CH0_DQSOSCSTAT0_ADDR;
   localparam REGB_DDRC_CH0_DQSOSCCFG0_ADDR = `REGB_DDRC_CH0_DQSOSCCFG0_ADDR;
   localparam REGB_DDRC_CH0_SCHED0_ADDR = `REGB_DDRC_CH0_SCHED0_ADDR;
   localparam REGB_DDRC_CH0_SCHED1_ADDR = `REGB_DDRC_CH0_SCHED1_ADDR;
   localparam REGB_DDRC_CH0_SCHED3_ADDR = `REGB_DDRC_CH0_SCHED3_ADDR;
   localparam REGB_DDRC_CH0_SCHED4_ADDR = `REGB_DDRC_CH0_SCHED4_ADDR;
   localparam REGB_DDRC_CH0_SCHED5_ADDR = `REGB_DDRC_CH0_SCHED5_ADDR;
   localparam REGB_DDRC_CH0_HWFFCCTL_ADDR = `REGB_DDRC_CH0_HWFFCCTL_ADDR;
   localparam REGB_DDRC_CH0_HWFFCSTAT_ADDR = `REGB_DDRC_CH0_HWFFCSTAT_ADDR;
   localparam REGB_DDRC_CH0_DFILPCFG0_ADDR = `REGB_DDRC_CH0_DFILPCFG0_ADDR;
   localparam REGB_DDRC_CH0_DFIUPD0_ADDR = `REGB_DDRC_CH0_DFIUPD0_ADDR;
   localparam REGB_DDRC_CH0_DFIMISC_ADDR = `REGB_DDRC_CH0_DFIMISC_ADDR;
   localparam REGB_DDRC_CH0_DFISTAT_ADDR = `REGB_DDRC_CH0_DFISTAT_ADDR;
   localparam REGB_DDRC_CH0_DFIPHYMSTR_ADDR = `REGB_DDRC_CH0_DFIPHYMSTR_ADDR;
   localparam REGB_DDRC_CH0_POISONCFG_ADDR = `REGB_DDRC_CH0_POISONCFG_ADDR;
   localparam REGB_DDRC_CH0_POISONSTAT_ADDR = `REGB_DDRC_CH0_POISONSTAT_ADDR;
   localparam REGB_DDRC_CH0_ECCCFG0_ADDR = `REGB_DDRC_CH0_ECCCFG0_ADDR;
   localparam REGB_DDRC_CH0_ECCCFG1_ADDR = `REGB_DDRC_CH0_ECCCFG1_ADDR;
   localparam REGB_DDRC_CH0_ECCSTAT_ADDR = `REGB_DDRC_CH0_ECCSTAT_ADDR;
   localparam REGB_DDRC_CH0_ECCCTL_ADDR = `REGB_DDRC_CH0_ECCCTL_ADDR;
   localparam REGB_DDRC_CH0_ECCERRCNT_ADDR = `REGB_DDRC_CH0_ECCERRCNT_ADDR;
   localparam REGB_DDRC_CH0_ECCCADDR0_ADDR = `REGB_DDRC_CH0_ECCCADDR0_ADDR;
   localparam REGB_DDRC_CH0_ECCCADDR1_ADDR = `REGB_DDRC_CH0_ECCCADDR1_ADDR;
   localparam REGB_DDRC_CH0_ECCCSYN0_ADDR = `REGB_DDRC_CH0_ECCCSYN0_ADDR;
   localparam REGB_DDRC_CH0_ECCCSYN1_ADDR = `REGB_DDRC_CH0_ECCCSYN1_ADDR;
   localparam REGB_DDRC_CH0_ECCCSYN2_ADDR = `REGB_DDRC_CH0_ECCCSYN2_ADDR;
   localparam REGB_DDRC_CH0_ECCBITMASK0_ADDR = `REGB_DDRC_CH0_ECCBITMASK0_ADDR;
   localparam REGB_DDRC_CH0_ECCBITMASK1_ADDR = `REGB_DDRC_CH0_ECCBITMASK1_ADDR;
   localparam REGB_DDRC_CH0_ECCBITMASK2_ADDR = `REGB_DDRC_CH0_ECCBITMASK2_ADDR;
   localparam REGB_DDRC_CH0_ECCUADDR0_ADDR = `REGB_DDRC_CH0_ECCUADDR0_ADDR;
   localparam REGB_DDRC_CH0_ECCUADDR1_ADDR = `REGB_DDRC_CH0_ECCUADDR1_ADDR;
   localparam REGB_DDRC_CH0_ECCUSYN0_ADDR = `REGB_DDRC_CH0_ECCUSYN0_ADDR;
   localparam REGB_DDRC_CH0_ECCUSYN1_ADDR = `REGB_DDRC_CH0_ECCUSYN1_ADDR;
   localparam REGB_DDRC_CH0_ECCUSYN2_ADDR = `REGB_DDRC_CH0_ECCUSYN2_ADDR;
   localparam REGB_DDRC_CH0_ECCPOISONADDR0_ADDR = `REGB_DDRC_CH0_ECCPOISONADDR0_ADDR;
   localparam REGB_DDRC_CH0_ECCPOISONADDR1_ADDR = `REGB_DDRC_CH0_ECCPOISONADDR1_ADDR;
   localparam REGB_DDRC_CH0_ECCPOISONPAT0_ADDR = `REGB_DDRC_CH0_ECCPOISONPAT0_ADDR;
   localparam REGB_DDRC_CH0_ECCPOISONPAT2_ADDR = `REGB_DDRC_CH0_ECCPOISONPAT2_ADDR;
   localparam REGB_DDRC_CH0_ECCAPSTAT_ADDR = `REGB_DDRC_CH0_ECCAPSTAT_ADDR;
   localparam REGB_DDRC_CH0_LNKECCCTL1_ADDR = `REGB_DDRC_CH0_LNKECCCTL1_ADDR;
   localparam REGB_DDRC_CH0_LNKECCPOISONCTL0_ADDR = `REGB_DDRC_CH0_LNKECCPOISONCTL0_ADDR;
   localparam REGB_DDRC_CH0_LNKECCPOISONSTAT_ADDR = `REGB_DDRC_CH0_LNKECCPOISONSTAT_ADDR;
   localparam REGB_DDRC_CH0_LNKECCINDEX_ADDR = `REGB_DDRC_CH0_LNKECCINDEX_ADDR;
   localparam REGB_DDRC_CH0_LNKECCERRCNT0_ADDR = `REGB_DDRC_CH0_LNKECCERRCNT0_ADDR;
   localparam REGB_DDRC_CH0_LNKECCERRSTAT_ADDR = `REGB_DDRC_CH0_LNKECCERRSTAT_ADDR;
   localparam REGB_DDRC_CH0_LNKECCCADDR0_ADDR = `REGB_DDRC_CH0_LNKECCCADDR0_ADDR;
   localparam REGB_DDRC_CH0_LNKECCCADDR1_ADDR = `REGB_DDRC_CH0_LNKECCCADDR1_ADDR;
   localparam REGB_DDRC_CH0_LNKECCUADDR0_ADDR = `REGB_DDRC_CH0_LNKECCUADDR0_ADDR;
   localparam REGB_DDRC_CH0_LNKECCUADDR1_ADDR = `REGB_DDRC_CH0_LNKECCUADDR1_ADDR;
   localparam REGB_DDRC_CH0_OPCTRL0_ADDR = `REGB_DDRC_CH0_OPCTRL0_ADDR;
   localparam REGB_DDRC_CH0_OPCTRL1_ADDR = `REGB_DDRC_CH0_OPCTRL1_ADDR;
   localparam REGB_DDRC_CH0_OPCTRLCAM_ADDR = `REGB_DDRC_CH0_OPCTRLCAM_ADDR;
   localparam REGB_DDRC_CH0_OPCTRLCMD_ADDR = `REGB_DDRC_CH0_OPCTRLCMD_ADDR;
   localparam REGB_DDRC_CH0_OPCTRLSTAT_ADDR = `REGB_DDRC_CH0_OPCTRLSTAT_ADDR;
   localparam REGB_DDRC_CH0_OPCTRLCAM1_ADDR = `REGB_DDRC_CH0_OPCTRLCAM1_ADDR;
   localparam REGB_DDRC_CH0_OPREFCTRL0_ADDR = `REGB_DDRC_CH0_OPREFCTRL0_ADDR;
   localparam REGB_DDRC_CH0_OPREFSTAT0_ADDR = `REGB_DDRC_CH0_OPREFSTAT0_ADDR;
   localparam REGB_DDRC_CH0_SWCTL_ADDR = `REGB_DDRC_CH0_SWCTL_ADDR;
   localparam REGB_DDRC_CH0_SWSTAT_ADDR = `REGB_DDRC_CH0_SWSTAT_ADDR;
   localparam REGB_DDRC_CH0_RANKCTL_ADDR = `REGB_DDRC_CH0_RANKCTL_ADDR;
   localparam REGB_DDRC_CH0_DBICTL_ADDR = `REGB_DDRC_CH0_DBICTL_ADDR;
   localparam REGB_DDRC_CH0_ODTMAP_ADDR = `REGB_DDRC_CH0_ODTMAP_ADDR;
   localparam REGB_DDRC_CH0_DATACTL0_ADDR = `REGB_DDRC_CH0_DATACTL0_ADDR;
   localparam REGB_DDRC_CH0_SWCTLSTATIC_ADDR = `REGB_DDRC_CH0_SWCTLSTATIC_ADDR;
   localparam REGB_DDRC_CH0_CGCTL_ADDR = `REGB_DDRC_CH0_CGCTL_ADDR;
   localparam REGB_DDRC_CH0_INITTMG0_ADDR = `REGB_DDRC_CH0_INITTMG0_ADDR;
   localparam REGB_DDRC_CH0_PPT2CTRL0_ADDR = `REGB_DDRC_CH0_PPT2CTRL0_ADDR;
   localparam REGB_DDRC_CH0_PPT2STAT0_ADDR = `REGB_DDRC_CH0_PPT2STAT0_ADDR;
   localparam REGB_DDRC_CH0_DDRCTL_VER_NUMBER_ADDR = `REGB_DDRC_CH0_DDRCTL_VER_NUMBER_ADDR;
   localparam REGB_DDRC_CH0_DDRCTL_VER_TYPE_ADDR = `REGB_DDRC_CH0_DDRCTL_VER_TYPE_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP1_ADDR = `REGB_ADDR_MAP0_ADDRMAP1_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP3_ADDR = `REGB_ADDR_MAP0_ADDRMAP3_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP4_ADDR = `REGB_ADDR_MAP0_ADDRMAP4_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP5_ADDR = `REGB_ADDR_MAP0_ADDRMAP5_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP6_ADDR = `REGB_ADDR_MAP0_ADDRMAP6_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP7_ADDR = `REGB_ADDR_MAP0_ADDRMAP7_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP8_ADDR = `REGB_ADDR_MAP0_ADDRMAP8_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP9_ADDR = `REGB_ADDR_MAP0_ADDRMAP9_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP10_ADDR = `REGB_ADDR_MAP0_ADDRMAP10_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP11_ADDR = `REGB_ADDR_MAP0_ADDRMAP11_ADDR;
   localparam REGB_ADDR_MAP0_ADDRMAP12_ADDR = `REGB_ADDR_MAP0_ADDRMAP12_ADDR;
   localparam REGB_ARB_PORT0_PCCFG_ADDR = `REGB_ARB_PORT0_PCCFG_ADDR;
   localparam REGB_ARB_PORT0_PCFGR_ADDR = `REGB_ARB_PORT0_PCFGR_ADDR;
   localparam REGB_ARB_PORT0_PCFGW_ADDR = `REGB_ARB_PORT0_PCFGW_ADDR;
   localparam REGB_ARB_PORT0_PCTRL_ADDR = `REGB_ARB_PORT0_PCTRL_ADDR;
   localparam REGB_ARB_PORT0_PCFGQOS0_ADDR = `REGB_ARB_PORT0_PCFGQOS0_ADDR;
   localparam REGB_ARB_PORT0_PCFGQOS1_ADDR = `REGB_ARB_PORT0_PCFGQOS1_ADDR;
   localparam REGB_ARB_PORT0_PCFGWQOS0_ADDR = `REGB_ARB_PORT0_PCFGWQOS0_ADDR;
   localparam REGB_ARB_PORT0_PCFGWQOS1_ADDR = `REGB_ARB_PORT0_PCFGWQOS1_ADDR;
   localparam REGB_ARB_PORT0_SBRCTL_ADDR = `REGB_ARB_PORT0_SBRCTL_ADDR;
   localparam REGB_ARB_PORT0_SBRSTAT_ADDR = `REGB_ARB_PORT0_SBRSTAT_ADDR;
   localparam REGB_ARB_PORT0_SBRWDATA0_ADDR = `REGB_ARB_PORT0_SBRWDATA0_ADDR;
   localparam REGB_ARB_PORT0_SBRSTART0_ADDR = `REGB_ARB_PORT0_SBRSTART0_ADDR;
   localparam REGB_ARB_PORT0_SBRSTART1_ADDR = `REGB_ARB_PORT0_SBRSTART1_ADDR;
   localparam REGB_ARB_PORT0_SBRRANGE0_ADDR = `REGB_ARB_PORT0_SBRRANGE0_ADDR;
   localparam REGB_ARB_PORT0_SBRRANGE1_ADDR = `REGB_ARB_PORT0_SBRRANGE1_ADDR;
   localparam REGB_ARB_PORT0_PSTAT_ADDR = `REGB_ARB_PORT0_PSTAT_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG0_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG0_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG1_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG1_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG2_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG2_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG3_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG3_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG4_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG4_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG5_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG5_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG6_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG6_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG7_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG7_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG9_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG9_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG12_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG12_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG13_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG13_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG14_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG14_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG17_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG17_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG23_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG23_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG24_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG24_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG25_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG25_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG30_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG30_ADDR;
   localparam REGB_FREQ0_CH0_DRAMSET1TMG32_ADDR = `REGB_FREQ0_CH0_DRAMSET1TMG32_ADDR;
   localparam REGB_FREQ0_CH0_INITMR0_ADDR = `REGB_FREQ0_CH0_INITMR0_ADDR;
   localparam REGB_FREQ0_CH0_INITMR1_ADDR = `REGB_FREQ0_CH0_INITMR1_ADDR;
   localparam REGB_FREQ0_CH0_INITMR2_ADDR = `REGB_FREQ0_CH0_INITMR2_ADDR;
   localparam REGB_FREQ0_CH0_INITMR3_ADDR = `REGB_FREQ0_CH0_INITMR3_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG0_ADDR = `REGB_FREQ0_CH0_DFITMG0_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG1_ADDR = `REGB_FREQ0_CH0_DFITMG1_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG2_ADDR = `REGB_FREQ0_CH0_DFITMG2_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG4_ADDR = `REGB_FREQ0_CH0_DFITMG4_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG5_ADDR = `REGB_FREQ0_CH0_DFITMG5_ADDR;
   localparam REGB_FREQ0_CH0_DFITMG6_ADDR = `REGB_FREQ0_CH0_DFITMG6_ADDR;
   localparam REGB_FREQ0_CH0_DFILPTMG0_ADDR = `REGB_FREQ0_CH0_DFILPTMG0_ADDR;
   localparam REGB_FREQ0_CH0_DFILPTMG1_ADDR = `REGB_FREQ0_CH0_DFILPTMG1_ADDR;
   localparam REGB_FREQ0_CH0_DFIUPDTMG0_ADDR = `REGB_FREQ0_CH0_DFIUPDTMG0_ADDR;
   localparam REGB_FREQ0_CH0_DFIUPDTMG1_ADDR = `REGB_FREQ0_CH0_DFIUPDTMG1_ADDR;
   localparam REGB_FREQ0_CH0_DFIUPDTMG2_ADDR = `REGB_FREQ0_CH0_DFIUPDTMG2_ADDR;
   localparam REGB_FREQ0_CH0_DFIUPDTMG3_ADDR = `REGB_FREQ0_CH0_DFIUPDTMG3_ADDR;
   localparam REGB_FREQ0_CH0_RFSHSET1TMG0_ADDR = `REGB_FREQ0_CH0_RFSHSET1TMG0_ADDR;
   localparam REGB_FREQ0_CH0_RFSHSET1TMG1_ADDR = `REGB_FREQ0_CH0_RFSHSET1TMG1_ADDR;
   localparam REGB_FREQ0_CH0_RFSHSET1TMG2_ADDR = `REGB_FREQ0_CH0_RFSHSET1TMG2_ADDR;
   localparam REGB_FREQ0_CH0_RFSHSET1TMG3_ADDR = `REGB_FREQ0_CH0_RFSHSET1TMG3_ADDR;
   localparam REGB_FREQ0_CH0_RFSHSET1TMG4_ADDR = `REGB_FREQ0_CH0_RFSHSET1TMG4_ADDR;
   localparam REGB_FREQ0_CH0_RFMSET1TMG0_ADDR = `REGB_FREQ0_CH0_RFMSET1TMG0_ADDR;
   localparam REGB_FREQ0_CH0_ZQSET1TMG0_ADDR = `REGB_FREQ0_CH0_ZQSET1TMG0_ADDR;
   localparam REGB_FREQ0_CH0_ZQSET1TMG1_ADDR = `REGB_FREQ0_CH0_ZQSET1TMG1_ADDR;
   localparam REGB_FREQ0_CH0_ZQSET1TMG2_ADDR = `REGB_FREQ0_CH0_ZQSET1TMG2_ADDR;
   localparam REGB_FREQ0_CH0_DQSOSCCTL0_ADDR = `REGB_FREQ0_CH0_DQSOSCCTL0_ADDR;
   localparam REGB_FREQ0_CH0_DERATEINT_ADDR = `REGB_FREQ0_CH0_DERATEINT_ADDR;
   localparam REGB_FREQ0_CH0_DERATEVAL0_ADDR = `REGB_FREQ0_CH0_DERATEVAL0_ADDR;
   localparam REGB_FREQ0_CH0_DERATEVAL1_ADDR = `REGB_FREQ0_CH0_DERATEVAL1_ADDR;
   localparam REGB_FREQ0_CH0_HWLPTMG0_ADDR = `REGB_FREQ0_CH0_HWLPTMG0_ADDR;
   localparam REGB_FREQ0_CH0_DVFSCTL0_ADDR = `REGB_FREQ0_CH0_DVFSCTL0_ADDR;
   localparam REGB_FREQ0_CH0_SCHEDTMG0_ADDR = `REGB_FREQ0_CH0_SCHEDTMG0_ADDR;
   localparam REGB_FREQ0_CH0_PERFHPR1_ADDR = `REGB_FREQ0_CH0_PERFHPR1_ADDR;
   localparam REGB_FREQ0_CH0_PERFLPR1_ADDR = `REGB_FREQ0_CH0_PERFLPR1_ADDR;
   localparam REGB_FREQ0_CH0_PERFWR1_ADDR = `REGB_FREQ0_CH0_PERFWR1_ADDR;
   localparam REGB_FREQ0_CH0_TMGCFG_ADDR = `REGB_FREQ0_CH0_TMGCFG_ADDR;
   localparam REGB_FREQ0_CH0_RANKTMG0_ADDR = `REGB_FREQ0_CH0_RANKTMG0_ADDR;
   localparam REGB_FREQ0_CH0_RANKTMG1_ADDR = `REGB_FREQ0_CH0_RANKTMG1_ADDR;
   localparam REGB_FREQ0_CH0_PWRTMG_ADDR = `REGB_FREQ0_CH0_PWRTMG_ADDR;
   localparam REGB_FREQ0_CH0_DDR4PPRTMG0_ADDR = `REGB_FREQ0_CH0_DDR4PPRTMG0_ADDR;
   localparam REGB_FREQ0_CH0_DDR4PPRTMG1_ADDR = `REGB_FREQ0_CH0_DDR4PPRTMG1_ADDR;
   localparam REGB_FREQ0_CH0_LNKECCCTL0_ADDR = `REGB_FREQ0_CH0_LNKECCCTL0_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG0_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG0_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG1_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG1_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG2_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG2_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG3_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG3_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG4_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG4_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG5_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG5_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG6_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG6_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG7_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG7_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG9_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG9_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG12_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG12_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG13_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG13_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG14_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG14_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG17_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG17_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG23_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG23_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG24_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG24_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG25_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG25_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG30_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG30_ADDR;
   localparam REGB_FREQ1_CH0_DRAMSET1TMG32_ADDR = `REGB_FREQ1_CH0_DRAMSET1TMG32_ADDR;
   localparam REGB_FREQ1_CH0_INITMR0_ADDR = `REGB_FREQ1_CH0_INITMR0_ADDR;
   localparam REGB_FREQ1_CH0_INITMR1_ADDR = `REGB_FREQ1_CH0_INITMR1_ADDR;
   localparam REGB_FREQ1_CH0_INITMR2_ADDR = `REGB_FREQ1_CH0_INITMR2_ADDR;
   localparam REGB_FREQ1_CH0_INITMR3_ADDR = `REGB_FREQ1_CH0_INITMR3_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG0_ADDR = `REGB_FREQ1_CH0_DFITMG0_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG1_ADDR = `REGB_FREQ1_CH0_DFITMG1_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG2_ADDR = `REGB_FREQ1_CH0_DFITMG2_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG4_ADDR = `REGB_FREQ1_CH0_DFITMG4_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG5_ADDR = `REGB_FREQ1_CH0_DFITMG5_ADDR;
   localparam REGB_FREQ1_CH0_DFITMG6_ADDR = `REGB_FREQ1_CH0_DFITMG6_ADDR;
   localparam REGB_FREQ1_CH0_DFIUPDTMG1_ADDR = `REGB_FREQ1_CH0_DFIUPDTMG1_ADDR;
   localparam REGB_FREQ1_CH0_DFIUPDTMG2_ADDR = `REGB_FREQ1_CH0_DFIUPDTMG2_ADDR;
   localparam REGB_FREQ1_CH0_DFIUPDTMG3_ADDR = `REGB_FREQ1_CH0_DFIUPDTMG3_ADDR;
   localparam REGB_FREQ1_CH0_RFSHSET1TMG0_ADDR = `REGB_FREQ1_CH0_RFSHSET1TMG0_ADDR;
   localparam REGB_FREQ1_CH0_RFSHSET1TMG1_ADDR = `REGB_FREQ1_CH0_RFSHSET1TMG1_ADDR;
   localparam REGB_FREQ1_CH0_RFSHSET1TMG2_ADDR = `REGB_FREQ1_CH0_RFSHSET1TMG2_ADDR;
   localparam REGB_FREQ1_CH0_RFSHSET1TMG3_ADDR = `REGB_FREQ1_CH0_RFSHSET1TMG3_ADDR;
   localparam REGB_FREQ1_CH0_RFSHSET1TMG4_ADDR = `REGB_FREQ1_CH0_RFSHSET1TMG4_ADDR;
   localparam REGB_FREQ1_CH0_RFMSET1TMG0_ADDR = `REGB_FREQ1_CH0_RFMSET1TMG0_ADDR;
   localparam REGB_FREQ1_CH0_ZQSET1TMG0_ADDR = `REGB_FREQ1_CH0_ZQSET1TMG0_ADDR;
   localparam REGB_FREQ1_CH0_ZQSET1TMG1_ADDR = `REGB_FREQ1_CH0_ZQSET1TMG1_ADDR;
   localparam REGB_FREQ1_CH0_ZQSET1TMG2_ADDR = `REGB_FREQ1_CH0_ZQSET1TMG2_ADDR;
   localparam REGB_FREQ1_CH0_DQSOSCCTL0_ADDR = `REGB_FREQ1_CH0_DQSOSCCTL0_ADDR;
   localparam REGB_FREQ1_CH0_DERATEINT_ADDR = `REGB_FREQ1_CH0_DERATEINT_ADDR;
   localparam REGB_FREQ1_CH0_DERATEVAL0_ADDR = `REGB_FREQ1_CH0_DERATEVAL0_ADDR;
   localparam REGB_FREQ1_CH0_DERATEVAL1_ADDR = `REGB_FREQ1_CH0_DERATEVAL1_ADDR;
   localparam REGB_FREQ1_CH0_HWLPTMG0_ADDR = `REGB_FREQ1_CH0_HWLPTMG0_ADDR;
   localparam REGB_FREQ1_CH0_DVFSCTL0_ADDR = `REGB_FREQ1_CH0_DVFSCTL0_ADDR;
   localparam REGB_FREQ1_CH0_SCHEDTMG0_ADDR = `REGB_FREQ1_CH0_SCHEDTMG0_ADDR;
   localparam REGB_FREQ1_CH0_PERFHPR1_ADDR = `REGB_FREQ1_CH0_PERFHPR1_ADDR;
   localparam REGB_FREQ1_CH0_PERFLPR1_ADDR = `REGB_FREQ1_CH0_PERFLPR1_ADDR;
   localparam REGB_FREQ1_CH0_PERFWR1_ADDR = `REGB_FREQ1_CH0_PERFWR1_ADDR;
   localparam REGB_FREQ1_CH0_TMGCFG_ADDR = `REGB_FREQ1_CH0_TMGCFG_ADDR;
   localparam REGB_FREQ1_CH0_RANKTMG0_ADDR = `REGB_FREQ1_CH0_RANKTMG0_ADDR;
   localparam REGB_FREQ1_CH0_RANKTMG1_ADDR = `REGB_FREQ1_CH0_RANKTMG1_ADDR;
   localparam REGB_FREQ1_CH0_PWRTMG_ADDR = `REGB_FREQ1_CH0_PWRTMG_ADDR;
   localparam REGB_FREQ1_CH0_DDR4PPRTMG0_ADDR = `REGB_FREQ1_CH0_DDR4PPRTMG0_ADDR;
   localparam REGB_FREQ1_CH0_DDR4PPRTMG1_ADDR = `REGB_FREQ1_CH0_DDR4PPRTMG1_ADDR;
   localparam REGB_FREQ1_CH0_LNKECCCTL0_ADDR = `REGB_FREQ1_CH0_LNKECCCTL0_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG0_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG0_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG1_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG1_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG2_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG2_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG3_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG3_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG4_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG4_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG5_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG5_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG6_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG6_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG7_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG7_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG9_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG9_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG12_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG12_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG13_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG13_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG14_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG14_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG17_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG17_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG23_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG23_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG24_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG24_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG25_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG25_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG30_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG30_ADDR;
   localparam REGB_FREQ2_CH0_DRAMSET1TMG32_ADDR = `REGB_FREQ2_CH0_DRAMSET1TMG32_ADDR;
   localparam REGB_FREQ2_CH0_INITMR0_ADDR = `REGB_FREQ2_CH0_INITMR0_ADDR;
   localparam REGB_FREQ2_CH0_INITMR1_ADDR = `REGB_FREQ2_CH0_INITMR1_ADDR;
   localparam REGB_FREQ2_CH0_INITMR2_ADDR = `REGB_FREQ2_CH0_INITMR2_ADDR;
   localparam REGB_FREQ2_CH0_INITMR3_ADDR = `REGB_FREQ2_CH0_INITMR3_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG0_ADDR = `REGB_FREQ2_CH0_DFITMG0_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG1_ADDR = `REGB_FREQ2_CH0_DFITMG1_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG2_ADDR = `REGB_FREQ2_CH0_DFITMG2_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG4_ADDR = `REGB_FREQ2_CH0_DFITMG4_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG5_ADDR = `REGB_FREQ2_CH0_DFITMG5_ADDR;
   localparam REGB_FREQ2_CH0_DFITMG6_ADDR = `REGB_FREQ2_CH0_DFITMG6_ADDR;
   localparam REGB_FREQ2_CH0_DFIUPDTMG1_ADDR = `REGB_FREQ2_CH0_DFIUPDTMG1_ADDR;
   localparam REGB_FREQ2_CH0_DFIUPDTMG2_ADDR = `REGB_FREQ2_CH0_DFIUPDTMG2_ADDR;
   localparam REGB_FREQ2_CH0_DFIUPDTMG3_ADDR = `REGB_FREQ2_CH0_DFIUPDTMG3_ADDR;
   localparam REGB_FREQ2_CH0_RFSHSET1TMG0_ADDR = `REGB_FREQ2_CH0_RFSHSET1TMG0_ADDR;
   localparam REGB_FREQ2_CH0_RFSHSET1TMG1_ADDR = `REGB_FREQ2_CH0_RFSHSET1TMG1_ADDR;
   localparam REGB_FREQ2_CH0_RFSHSET1TMG2_ADDR = `REGB_FREQ2_CH0_RFSHSET1TMG2_ADDR;
   localparam REGB_FREQ2_CH0_RFSHSET1TMG3_ADDR = `REGB_FREQ2_CH0_RFSHSET1TMG3_ADDR;
   localparam REGB_FREQ2_CH0_RFSHSET1TMG4_ADDR = `REGB_FREQ2_CH0_RFSHSET1TMG4_ADDR;
   localparam REGB_FREQ2_CH0_RFMSET1TMG0_ADDR = `REGB_FREQ2_CH0_RFMSET1TMG0_ADDR;
   localparam REGB_FREQ2_CH0_ZQSET1TMG0_ADDR = `REGB_FREQ2_CH0_ZQSET1TMG0_ADDR;
   localparam REGB_FREQ2_CH0_ZQSET1TMG1_ADDR = `REGB_FREQ2_CH0_ZQSET1TMG1_ADDR;
   localparam REGB_FREQ2_CH0_ZQSET1TMG2_ADDR = `REGB_FREQ2_CH0_ZQSET1TMG2_ADDR;
   localparam REGB_FREQ2_CH0_DQSOSCCTL0_ADDR = `REGB_FREQ2_CH0_DQSOSCCTL0_ADDR;
   localparam REGB_FREQ2_CH0_DERATEINT_ADDR = `REGB_FREQ2_CH0_DERATEINT_ADDR;
   localparam REGB_FREQ2_CH0_DERATEVAL0_ADDR = `REGB_FREQ2_CH0_DERATEVAL0_ADDR;
   localparam REGB_FREQ2_CH0_DERATEVAL1_ADDR = `REGB_FREQ2_CH0_DERATEVAL1_ADDR;
   localparam REGB_FREQ2_CH0_HWLPTMG0_ADDR = `REGB_FREQ2_CH0_HWLPTMG0_ADDR;
   localparam REGB_FREQ2_CH0_DVFSCTL0_ADDR = `REGB_FREQ2_CH0_DVFSCTL0_ADDR;
   localparam REGB_FREQ2_CH0_SCHEDTMG0_ADDR = `REGB_FREQ2_CH0_SCHEDTMG0_ADDR;
   localparam REGB_FREQ2_CH0_PERFHPR1_ADDR = `REGB_FREQ2_CH0_PERFHPR1_ADDR;
   localparam REGB_FREQ2_CH0_PERFLPR1_ADDR = `REGB_FREQ2_CH0_PERFLPR1_ADDR;
   localparam REGB_FREQ2_CH0_PERFWR1_ADDR = `REGB_FREQ2_CH0_PERFWR1_ADDR;
   localparam REGB_FREQ2_CH0_TMGCFG_ADDR = `REGB_FREQ2_CH0_TMGCFG_ADDR;
   localparam REGB_FREQ2_CH0_RANKTMG0_ADDR = `REGB_FREQ2_CH0_RANKTMG0_ADDR;
   localparam REGB_FREQ2_CH0_RANKTMG1_ADDR = `REGB_FREQ2_CH0_RANKTMG1_ADDR;
   localparam REGB_FREQ2_CH0_PWRTMG_ADDR = `REGB_FREQ2_CH0_PWRTMG_ADDR;
   localparam REGB_FREQ2_CH0_DDR4PPRTMG0_ADDR = `REGB_FREQ2_CH0_DDR4PPRTMG0_ADDR;
   localparam REGB_FREQ2_CH0_DDR4PPRTMG1_ADDR = `REGB_FREQ2_CH0_DDR4PPRTMG1_ADDR;
   localparam REGB_FREQ2_CH0_LNKECCCTL0_ADDR = `REGB_FREQ2_CH0_LNKECCCTL0_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG0_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG0_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG1_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG1_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG2_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG2_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG3_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG3_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG4_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG4_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG5_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG5_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG6_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG6_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG7_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG7_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG9_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG9_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG12_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG12_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG13_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG13_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG14_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG14_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG17_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG17_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG23_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG23_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG24_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG24_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG25_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG25_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG30_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG30_ADDR;
   localparam REGB_FREQ3_CH0_DRAMSET1TMG32_ADDR = `REGB_FREQ3_CH0_DRAMSET1TMG32_ADDR;
   localparam REGB_FREQ3_CH0_INITMR0_ADDR = `REGB_FREQ3_CH0_INITMR0_ADDR;
   localparam REGB_FREQ3_CH0_INITMR1_ADDR = `REGB_FREQ3_CH0_INITMR1_ADDR;
   localparam REGB_FREQ3_CH0_INITMR2_ADDR = `REGB_FREQ3_CH0_INITMR2_ADDR;
   localparam REGB_FREQ3_CH0_INITMR3_ADDR = `REGB_FREQ3_CH0_INITMR3_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG0_ADDR = `REGB_FREQ3_CH0_DFITMG0_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG1_ADDR = `REGB_FREQ3_CH0_DFITMG1_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG2_ADDR = `REGB_FREQ3_CH0_DFITMG2_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG4_ADDR = `REGB_FREQ3_CH0_DFITMG4_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG5_ADDR = `REGB_FREQ3_CH0_DFITMG5_ADDR;
   localparam REGB_FREQ3_CH0_DFITMG6_ADDR = `REGB_FREQ3_CH0_DFITMG6_ADDR;
   localparam REGB_FREQ3_CH0_DFIUPDTMG1_ADDR = `REGB_FREQ3_CH0_DFIUPDTMG1_ADDR;
   localparam REGB_FREQ3_CH0_DFIUPDTMG2_ADDR = `REGB_FREQ3_CH0_DFIUPDTMG2_ADDR;
   localparam REGB_FREQ3_CH0_DFIUPDTMG3_ADDR = `REGB_FREQ3_CH0_DFIUPDTMG3_ADDR;
   localparam REGB_FREQ3_CH0_RFSHSET1TMG0_ADDR = `REGB_FREQ3_CH0_RFSHSET1TMG0_ADDR;
   localparam REGB_FREQ3_CH0_RFSHSET1TMG1_ADDR = `REGB_FREQ3_CH0_RFSHSET1TMG1_ADDR;
   localparam REGB_FREQ3_CH0_RFSHSET1TMG2_ADDR = `REGB_FREQ3_CH0_RFSHSET1TMG2_ADDR;
   localparam REGB_FREQ3_CH0_RFSHSET1TMG3_ADDR = `REGB_FREQ3_CH0_RFSHSET1TMG3_ADDR;
   localparam REGB_FREQ3_CH0_RFSHSET1TMG4_ADDR = `REGB_FREQ3_CH0_RFSHSET1TMG4_ADDR;
   localparam REGB_FREQ3_CH0_RFMSET1TMG0_ADDR = `REGB_FREQ3_CH0_RFMSET1TMG0_ADDR;
   localparam REGB_FREQ3_CH0_ZQSET1TMG0_ADDR = `REGB_FREQ3_CH0_ZQSET1TMG0_ADDR;
   localparam REGB_FREQ3_CH0_ZQSET1TMG1_ADDR = `REGB_FREQ3_CH0_ZQSET1TMG1_ADDR;
   localparam REGB_FREQ3_CH0_ZQSET1TMG2_ADDR = `REGB_FREQ3_CH0_ZQSET1TMG2_ADDR;
   localparam REGB_FREQ3_CH0_DQSOSCCTL0_ADDR = `REGB_FREQ3_CH0_DQSOSCCTL0_ADDR;
   localparam REGB_FREQ3_CH0_DERATEINT_ADDR = `REGB_FREQ3_CH0_DERATEINT_ADDR;
   localparam REGB_FREQ3_CH0_DERATEVAL0_ADDR = `REGB_FREQ3_CH0_DERATEVAL0_ADDR;
   localparam REGB_FREQ3_CH0_DERATEVAL1_ADDR = `REGB_FREQ3_CH0_DERATEVAL1_ADDR;
   localparam REGB_FREQ3_CH0_HWLPTMG0_ADDR = `REGB_FREQ3_CH0_HWLPTMG0_ADDR;
   localparam REGB_FREQ3_CH0_DVFSCTL0_ADDR = `REGB_FREQ3_CH0_DVFSCTL0_ADDR;
   localparam REGB_FREQ3_CH0_SCHEDTMG0_ADDR = `REGB_FREQ3_CH0_SCHEDTMG0_ADDR;
   localparam REGB_FREQ3_CH0_PERFHPR1_ADDR = `REGB_FREQ3_CH0_PERFHPR1_ADDR;
   localparam REGB_FREQ3_CH0_PERFLPR1_ADDR = `REGB_FREQ3_CH0_PERFLPR1_ADDR;
   localparam REGB_FREQ3_CH0_PERFWR1_ADDR = `REGB_FREQ3_CH0_PERFWR1_ADDR;
   localparam REGB_FREQ3_CH0_TMGCFG_ADDR = `REGB_FREQ3_CH0_TMGCFG_ADDR;
   localparam REGB_FREQ3_CH0_RANKTMG0_ADDR = `REGB_FREQ3_CH0_RANKTMG0_ADDR;
   localparam REGB_FREQ3_CH0_RANKTMG1_ADDR = `REGB_FREQ3_CH0_RANKTMG1_ADDR;
   localparam REGB_FREQ3_CH0_PWRTMG_ADDR = `REGB_FREQ3_CH0_PWRTMG_ADDR;
   localparam REGB_FREQ3_CH0_DDR4PPRTMG0_ADDR = `REGB_FREQ3_CH0_DDR4PPRTMG0_ADDR;
   localparam REGB_FREQ3_CH0_DDR4PPRTMG1_ADDR = `REGB_FREQ3_CH0_DDR4PPRTMG1_ADDR;
   localparam REGB_FREQ3_CH0_LNKECCCTL0_ADDR = `REGB_FREQ3_CH0_LNKECCCTL0_ADDR;


   logic [SELWIDTH-1:0]             onehotsel;
   logic                            addr_mapped; // To indicate out of range address
   reg [REG_AW-1:0]                 reg_addr;
   reg [REG_WIDTH
                  -1:0]  rfm_data_decoded;
   logic [$bits(rfm_data_decoded) -1:0]  rfm_data_decoded_next;
   reg                              invalid_access;

 always_ff @(posedge pclk or negedge presetn) begin : sample_pclk_paddr_PROC
      if (~presetn) begin
         reg_addr <= {REG_AW{1'b0}};
      end else begin
         if(psel) begin
            // -- Register address
            // -- Strip off bits [1:0] which are embedded into byte enables
            reg_addr <= paddr[APB_AW-1:$clog2(APB_DW/8)];
         end
      end
   end

   // -- Write Address Decoding ----
   always_comb begin : rwselect_combo_PROC
      rwselect = {RWSELWIDTH{1'b0}};
      if(reg_addr==REGB_DDRC_CH0_MSTR0_ADDR[REG_AW-1:0]) begin
         rwselect[0] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_MSTR2_ADDR[REG_AW-1:0]) begin
         rwselect[2] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_MSTR4_ADDR[REG_AW-1:0]) begin
         rwselect[4] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_MRCTRL0_ADDR[REG_AW-1:0]) begin
         rwselect[5] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_MRCTRL1_ADDR[REG_AW-1:0]) begin
         rwselect[6] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATECTL0_ADDR[REG_AW-1:0]) begin
         rwselect[8] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATECTL1_ADDR[REG_AW-1:0]) begin
         rwselect[9] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATECTL2_ADDR[REG_AW-1:0]) begin
         rwselect[10] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATECTL5_ADDR[REG_AW-1:0]) begin
         rwselect[13] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATECTL6_ADDR[REG_AW-1:0]) begin
         rwselect[14] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DERATEDBGCTL_ADDR[REG_AW-1:0]) begin
         rwselect[16] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_PWRCTL_ADDR[REG_AW-1:0]) begin
         rwselect[17] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_HWLPCTL_ADDR[REG_AW-1:0]) begin
         rwselect[18] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_CLKGATECTL_ADDR[REG_AW-1:0]) begin
         rwselect[20] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RFSHMOD0_ADDR[REG_AW-1:0]) begin
         rwselect[21] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RFSHCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[23] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RFMMOD0_ADDR[REG_AW-1:0]) begin
         rwselect[24] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RFMMOD1_ADDR[REG_AW-1:0]) begin
         rwselect[25] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RFMCTL_ADDR[REG_AW-1:0]) begin
         rwselect[26] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ZQCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[27] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ZQCTL1_ADDR[REG_AW-1:0]) begin
         rwselect[28] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ZQCTL2_ADDR[REG_AW-1:0]) begin
         rwselect[29] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DQSOSCRUNTIME_ADDR[REG_AW-1:0]) begin
         rwselect[30] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DQSOSCCFG0_ADDR[REG_AW-1:0]) begin
         rwselect[31] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SCHED0_ADDR[REG_AW-1:0]) begin
         rwselect[33] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SCHED1_ADDR[REG_AW-1:0]) begin
         rwselect[34] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SCHED3_ADDR[REG_AW-1:0]) begin
         rwselect[36] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SCHED4_ADDR[REG_AW-1:0]) begin
         rwselect[37] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SCHED5_ADDR[REG_AW-1:0]) begin
         rwselect[38] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_HWFFCCTL_ADDR[REG_AW-1:0]) begin
         rwselect[39] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DFILPCFG0_ADDR[REG_AW-1:0]) begin
         rwselect[48] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DFIUPD0_ADDR[REG_AW-1:0]) begin
         rwselect[49] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DFIMISC_ADDR[REG_AW-1:0]) begin
         rwselect[51] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DFIPHYMSTR_ADDR[REG_AW-1:0]) begin
         rwselect[52] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_POISONCFG_ADDR[REG_AW-1:0]) begin
         rwselect[57] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCCFG0_ADDR[REG_AW-1:0]) begin
         rwselect[58] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCCFG1_ADDR[REG_AW-1:0]) begin
         rwselect[59] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCCTL_ADDR[REG_AW-1:0]) begin
         rwselect[60] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCPOISONADDR0_ADDR[REG_AW-1:0]) begin
         rwselect[61] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCPOISONADDR1_ADDR[REG_AW-1:0]) begin
         rwselect[62] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCPOISONPAT0_ADDR[REG_AW-1:0]) begin
         rwselect[64] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ECCPOISONPAT2_ADDR[REG_AW-1:0]) begin
         rwselect[66] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_LNKECCCTL1_ADDR[REG_AW-1:0]) begin
         rwselect[84] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_LNKECCPOISONCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[85] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_LNKECCINDEX_ADDR[REG_AW-1:0]) begin
         rwselect[86] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_OPCTRL0_ADDR[REG_AW-1:0]) begin
         rwselect[129] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_OPCTRL1_ADDR[REG_AW-1:0]) begin
         rwselect[130] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_OPCTRLCMD_ADDR[REG_AW-1:0]) begin
         rwselect[131] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_OPREFCTRL0_ADDR[REG_AW-1:0]) begin
         rwselect[132] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SWCTL_ADDR[REG_AW-1:0]) begin
         rwselect[136] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_RANKCTL_ADDR[REG_AW-1:0]) begin
         rwselect[139] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DBICTL_ADDR[REG_AW-1:0]) begin
         rwselect[140] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_ODTMAP_ADDR[REG_AW-1:0]) begin
         rwselect[141] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_DATACTL0_ADDR[REG_AW-1:0]) begin
         rwselect[142] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_SWCTLSTATIC_ADDR[REG_AW-1:0]) begin
         rwselect[143] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_CGCTL_ADDR[REG_AW-1:0]) begin
         rwselect[144] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_INITTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[145] = 1'b1;
      end
      if(reg_addr==REGB_DDRC_CH0_PPT2CTRL0_ADDR[REG_AW-1:0]) begin
         rwselect[150] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP1_ADDR[REG_AW-1:0]) begin
         rwselect[236] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP3_ADDR[REG_AW-1:0]) begin
         rwselect[238] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP4_ADDR[REG_AW-1:0]) begin
         rwselect[239] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP5_ADDR[REG_AW-1:0]) begin
         rwselect[240] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP6_ADDR[REG_AW-1:0]) begin
         rwselect[241] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP7_ADDR[REG_AW-1:0]) begin
         rwselect[242] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP8_ADDR[REG_AW-1:0]) begin
         rwselect[243] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP9_ADDR[REG_AW-1:0]) begin
         rwselect[244] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP10_ADDR[REG_AW-1:0]) begin
         rwselect[245] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP11_ADDR[REG_AW-1:0]) begin
         rwselect[246] = 1'b1;
      end
      if(reg_addr==REGB_ADDR_MAP0_ADDRMAP12_ADDR[REG_AW-1:0]) begin
         rwselect[247] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCCFG_ADDR[REG_AW-1:0]) begin
         rwselect[261] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGR_ADDR[REG_AW-1:0]) begin
         rwselect[262] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGW_ADDR[REG_AW-1:0]) begin
         rwselect[263] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCTRL_ADDR[REG_AW-1:0]) begin
         rwselect[296] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGQOS0_ADDR[REG_AW-1:0]) begin
         rwselect[297] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGQOS1_ADDR[REG_AW-1:0]) begin
         rwselect[298] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGWQOS0_ADDR[REG_AW-1:0]) begin
         rwselect[299] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_PCFGWQOS1_ADDR[REG_AW-1:0]) begin
         rwselect[300] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRCTL_ADDR[REG_AW-1:0]) begin
         rwselect[309] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRWDATA0_ADDR[REG_AW-1:0]) begin
         rwselect[310] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRSTART0_ADDR[REG_AW-1:0]) begin
         rwselect[312] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRSTART1_ADDR[REG_AW-1:0]) begin
         rwselect[313] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRRANGE0_ADDR[REG_AW-1:0]) begin
         rwselect[314] = 1'b1;
      end
      if(reg_addr==REGB_ARB_PORT0_SBRRANGE1_ADDR[REG_AW-1:0]) begin
         rwselect[315] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1487] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1488] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1489] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1490] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1491] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin
         rwselect[1492] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin
         rwselect[1493] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin
         rwselect[1494] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin
         rwselect[1496] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin
         rwselect[1499] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin
         rwselect[1500] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin
         rwselect[1501] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin
         rwselect[1504] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin
         rwselect[1509] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin
         rwselect[1510] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin
         rwselect[1511] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin
         rwselect[1516] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin
         rwselect[1518] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_INITMR0_ADDR[REG_AW-1:0]) begin
         rwselect[1549] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_INITMR1_ADDR[REG_AW-1:0]) begin
         rwselect[1550] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_INITMR2_ADDR[REG_AW-1:0]) begin
         rwselect[1551] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_INITMR3_ADDR[REG_AW-1:0]) begin
         rwselect[1552] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1553] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1554] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1555] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1557] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin
         rwselect[1558] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin
         rwselect[1559] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFILPTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1561] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFILPTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1562] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFIUPDTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1563] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1564] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1566] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1567] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1568] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1569] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1570] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1571] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1572] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1582] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1593] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1594] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1595] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1604] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin
         rwselect[1605] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin
         rwselect[1606] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin
         rwselect[1607] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1608] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1609] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1610] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin
         rwselect[1611] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin
         rwselect[1612] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin
         rwselect[1613] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin
         rwselect[1614] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1615] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1616] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin
         rwselect[1617] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1623] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1624] = 1'b1;
      end
      if(reg_addr==REGB_FREQ0_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1625] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1759] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1760] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1761] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1762] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1763] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin
         rwselect[1764] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin
         rwselect[1765] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin
         rwselect[1766] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin
         rwselect[1768] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin
         rwselect[1771] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin
         rwselect[1772] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin
         rwselect[1773] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin
         rwselect[1776] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin
         rwselect[1781] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin
         rwselect[1782] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin
         rwselect[1783] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin
         rwselect[1788] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin
         rwselect[1790] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_INITMR0_ADDR[REG_AW-1:0]) begin
         rwselect[1821] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_INITMR1_ADDR[REG_AW-1:0]) begin
         rwselect[1822] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_INITMR2_ADDR[REG_AW-1:0]) begin
         rwselect[1823] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_INITMR3_ADDR[REG_AW-1:0]) begin
         rwselect[1824] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1825] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1826] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1827] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1829] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin
         rwselect[1830] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin
         rwselect[1831] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1833] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1834] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1835] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1836] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1837] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1838] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[1839] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[1840] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1850] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1861] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1862] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[1863] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1872] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin
         rwselect[1873] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin
         rwselect[1874] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin
         rwselect[1875] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1876] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1877] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1878] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin
         rwselect[1879] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin
         rwselect[1880] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin
         rwselect[1881] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin
         rwselect[1882] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1883] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1884] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin
         rwselect[1885] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[1891] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[1892] = 1'b1;
      end
      if(reg_addr==REGB_FREQ1_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[1893] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2027] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2028] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2029] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2030] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2031] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin
         rwselect[2032] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin
         rwselect[2033] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin
         rwselect[2034] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin
         rwselect[2036] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin
         rwselect[2039] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin
         rwselect[2040] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin
         rwselect[2041] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin
         rwselect[2044] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin
         rwselect[2049] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin
         rwselect[2050] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin
         rwselect[2051] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin
         rwselect[2056] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin
         rwselect[2058] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_INITMR0_ADDR[REG_AW-1:0]) begin
         rwselect[2089] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_INITMR1_ADDR[REG_AW-1:0]) begin
         rwselect[2090] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_INITMR2_ADDR[REG_AW-1:0]) begin
         rwselect[2091] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_INITMR3_ADDR[REG_AW-1:0]) begin
         rwselect[2092] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2093] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2094] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2095] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2097] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin
         rwselect[2098] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin
         rwselect[2099] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2101] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2102] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2103] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2104] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2105] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2106] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2107] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2108] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2118] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2129] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2130] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2131] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2140] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin
         rwselect[2141] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin
         rwselect[2142] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin
         rwselect[2143] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2144] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2145] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2146] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin
         rwselect[2147] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin
         rwselect[2148] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin
         rwselect[2149] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin
         rwselect[2150] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2151] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2152] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin
         rwselect[2153] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2159] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2160] = 1'b1;
      end
      if(reg_addr==REGB_FREQ2_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2161] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2295] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2296] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2297] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2298] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2299] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin
         rwselect[2300] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin
         rwselect[2301] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin
         rwselect[2302] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin
         rwselect[2304] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin
         rwselect[2307] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin
         rwselect[2308] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin
         rwselect[2309] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin
         rwselect[2312] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin
         rwselect[2317] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin
         rwselect[2318] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin
         rwselect[2319] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin
         rwselect[2324] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin
         rwselect[2326] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_INITMR0_ADDR[REG_AW-1:0]) begin
         rwselect[2357] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_INITMR1_ADDR[REG_AW-1:0]) begin
         rwselect[2358] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_INITMR2_ADDR[REG_AW-1:0]) begin
         rwselect[2359] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_INITMR3_ADDR[REG_AW-1:0]) begin
         rwselect[2360] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2361] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2362] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2363] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2365] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin
         rwselect[2366] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin
         rwselect[2367] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2369] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2370] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2371] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2372] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2373] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2374] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin
         rwselect[2375] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin
         rwselect[2376] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2386] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2397] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2398] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin
         rwselect[2399] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2408] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin
         rwselect[2409] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin
         rwselect[2410] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin
         rwselect[2411] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2412] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2413] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2414] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin
         rwselect[2415] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin
         rwselect[2416] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin
         rwselect[2417] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin
         rwselect[2418] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2419] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2420] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin
         rwselect[2421] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin
         rwselect[2427] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin
         rwselect[2428] = 1'b1;
      end
      if(reg_addr==REGB_FREQ3_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin
         rwselect[2429] = 1'b1;
      end

   end

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
   property apb_rwselect_legal;
      @(posedge pclk) disable iff(!presetn)
      $onehot0(rwselect);
   endproperty : apb_rwselect_legal
   a_apb_rwselect_legal :  assert property (apb_rwselect_legal) else 
     $display("%0t ERROR: RW register selector is one hot.",$realtime);
`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON
   // -- Read Address Decoding ----
   // The incoming binary address is decoded to onehot.
   // Individual bits of the one hot address are used
   // to select the respective register in the map
   always_comb begin : onehotsel_combo_PROC
      onehotsel = {SELWIDTH{1'b0}};
      addr_mapped = 1'b0;
         if (reg_addr==REGB_DDRC_CH0_MSTR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[0] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MSTR2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MSTR4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[4] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_STAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[5] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MRCTRL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[8] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MRCTRL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[9] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MRSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[11] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MRRDATA0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[12] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_MRRDATA1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[13] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATECTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[14] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATECTL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[15] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATECTL2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[16] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATECTL5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[19] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATECTL6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[20] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATESTAT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[22] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATEDBGCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[24] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DERATEDBGSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[25] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_PWRCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[26] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_HWLPCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[27] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_CLKGATECTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[29] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFSHMOD0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[30] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFSHCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[32] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFMMOD0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[33] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFMMOD1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[34] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFMCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[35] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RFMSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[36] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ZQCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[37] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ZQCTL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[38] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ZQCTL2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[39] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ZQSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[40] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DQSOSCRUNTIME_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[41] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DQSOSCSTAT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[42] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DQSOSCCFG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[43] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SCHED0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[45] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SCHED1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[46] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SCHED3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[48] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SCHED4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[49] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SCHED5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[50] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_HWFFCCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[51] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_HWFFCSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[52] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DFILPCFG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[62] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DFIUPD0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[63] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DFIMISC_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[65] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DFISTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[66] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DFIPHYMSTR_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[67] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_POISONCFG_ADDR[REG_AW-1:0]) begin 
            onehotsel[77] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_POISONSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[78] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCFG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[79] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCFG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[80] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[81] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCTL_ADDR[REG_AW-1:0]) begin 
            onehotsel[82] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCERRCNT_ADDR[REG_AW-1:0]) begin 
            onehotsel[83] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCADDR0_ADDR[REG_AW-1:0]) begin 
            onehotsel[84] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCADDR1_ADDR[REG_AW-1:0]) begin 
            onehotsel[85] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCSYN0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[86] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCSYN1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[87] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCCSYN2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[88] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCBITMASK0_ADDR[REG_AW-1:0]) begin 
            onehotsel[89] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCBITMASK1_ADDR[REG_AW-1:0]) begin 
            onehotsel[90] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCBITMASK2_ADDR[REG_AW-1:0]) begin 
            onehotsel[91] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCUADDR0_ADDR[REG_AW-1:0]) begin 
            onehotsel[92] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCUADDR1_ADDR[REG_AW-1:0]) begin 
            onehotsel[93] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCUSYN0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[94] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCUSYN1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[95] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCUSYN2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[96] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCPOISONADDR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[97] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCPOISONADDR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[98] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCPOISONPAT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[101] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCPOISONPAT2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[103] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ECCAPSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[104] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCCTL1_ADDR[REG_AW-1:0]) begin 
            onehotsel[161] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCPOISONCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[162] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCPOISONSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[163] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCINDEX_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[164] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCERRCNT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[165] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCERRSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[166] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCCADDR0_ADDR[REG_AW-1:0]) begin 
            onehotsel[175] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCCADDR1_ADDR[REG_AW-1:0]) begin 
            onehotsel[176] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCUADDR0_ADDR[REG_AW-1:0]) begin 
            onehotsel[177] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_LNKECCUADDR1_ADDR[REG_AW-1:0]) begin 
            onehotsel[178] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[234] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[235] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRLCAM_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[236] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRLCMD_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[237] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRLSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[238] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPCTRLCAM1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[239] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPREFCTRL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[240] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_OPREFSTAT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[242] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SWCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[249] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SWSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[250] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_RANKCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[253] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DBICTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[254] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_ODTMAP_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[256] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DATACTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[257] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_SWCTLSTATIC_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[258] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_CGCTL_ADDR[REG_AW-1:0]) begin 
            onehotsel[259] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_INITTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[260] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_PPT2CTRL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[285] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_PPT2STAT0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[286] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DDRCTL_VER_NUMBER_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[289] = 1'b1;
         end
         if (reg_addr==REGB_DDRC_CH0_DDRCTL_VER_TYPE_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[290] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[495] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[497] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[498] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[499] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[500] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP7_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[501] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP8_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[502] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP9_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[503] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP10_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[504] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP11_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[505] = 1'b1;
         end
         if (reg_addr==REGB_ADDR_MAP0_ADDRMAP12_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[506] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCCFG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[521] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGR_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[522] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGW_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[523] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCTRL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[556] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGQOS0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[557] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGQOS1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[558] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGWQOS0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[559] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PCFGWQOS1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[560] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRCTL_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[569] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRSTAT_ADDR[REG_AW-1:0]) begin 
            onehotsel[570] = 1'b1;
            addr_mapped = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRWDATA0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[571] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRSTART0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[573] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRSTART1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[574] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRRANGE0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[575] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_SBRRANGE1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[576] = 1'b1;
         end
         if (reg_addr==REGB_ARB_PORT0_PSTAT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[582] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1929] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1930] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1931] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1932] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1933] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1934] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1935] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1936] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1938] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1941] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1942] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1943] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1946] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1951] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1952] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1953] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1958] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1960] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_INITMR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1991] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_INITMR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1992] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_INITMR2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1993] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_INITMR3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1994] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1995] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1996] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1997] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[1999] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2000] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2001] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFILPTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2003] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFILPTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2004] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFIUPDTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2005] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2006] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2008] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2009] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2010] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2011] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2012] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2013] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2014] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2024] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2035] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2036] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2037] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2046] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2047] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2048] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2049] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2050] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2051] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2052] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2053] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2054] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2055] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2056] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2057] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2058] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2059] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2065] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2066] = 1'b1;
         end
         if (reg_addr==REGB_FREQ0_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2067] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2201] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2202] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2203] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2204] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2205] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2206] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2207] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2208] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2210] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2213] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2214] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2215] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2218] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2223] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2224] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2225] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2230] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2232] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_INITMR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2263] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_INITMR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2264] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_INITMR2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2265] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_INITMR3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2266] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2267] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2268] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2269] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2271] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2272] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2273] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2275] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2276] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2277] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2278] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2279] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2280] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2281] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2282] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2292] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2303] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2304] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2305] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2314] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2315] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2316] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2317] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2318] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2319] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2320] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2321] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2322] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2323] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2324] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2325] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2326] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2327] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2333] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2334] = 1'b1;
         end
         if (reg_addr==REGB_FREQ1_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2335] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2469] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2470] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2471] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2472] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2473] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2474] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2475] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2476] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2478] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2481] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2482] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2483] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2486] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2491] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2492] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2493] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2498] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2500] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_INITMR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2531] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_INITMR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2532] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_INITMR2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2533] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_INITMR3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2534] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2535] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2536] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2537] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2539] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2540] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2541] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2543] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2544] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2545] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2546] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2547] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2548] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2549] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2550] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2560] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2571] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2572] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2573] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2582] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2583] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2584] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2585] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2586] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2587] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2588] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2589] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2590] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2591] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2592] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2593] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2594] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2595] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2601] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2602] = 1'b1;
         end
         if (reg_addr==REGB_FREQ2_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2603] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2737] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2738] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2739] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2740] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2741] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2742] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2743] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG7_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2744] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG9_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2746] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG12_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2749] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG13_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2750] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG14_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2751] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG17_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2754] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG23_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2759] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG24_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2760] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG25_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2761] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG30_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2766] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DRAMSET1TMG32_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2768] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_INITMR0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2799] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_INITMR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2800] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_INITMR2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2801] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_INITMR3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2802] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2803] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2804] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2805] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2807] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG5_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2808] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFITMG6_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2809] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFIUPDTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2811] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFIUPDTMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2812] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DFIUPDTMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2813] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2814] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2815] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2816] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG3_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2817] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFSHSET1TMG4_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2818] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RFMSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2828] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_ZQSET1TMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2839] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_ZQSET1TMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2840] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_ZQSET1TMG2_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2841] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DQSOSCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2850] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DERATEINT_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2851] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DERATEVAL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2852] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DERATEVAL1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2853] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_HWLPTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2854] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DVFSCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2855] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_SCHEDTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2856] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_PERFHPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2857] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_PERFLPR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2858] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_PERFWR1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2859] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_TMGCFG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2860] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RANKTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2861] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_RANKTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2862] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_PWRTMG_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2863] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DDR4PPRTMG0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2869] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_DDR4PPRTMG1_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2870] = 1'b1;
         end
         if (reg_addr==REGB_FREQ3_CH0_LNKECCCTL0_ADDR[REG_AW-1:0]) begin 
            addr_mapped = 1'b1;
            onehotsel[2871] = 1'b1;
         end

   end
 
   // --- Multiplex the output data based on selects ---   
   always_comb begin : select_data_combo_PROC
      case (onehotsel)
         {5952'b0,1'b1} : rfm_data_decoded_next = r0_mstr0; // 0 
         {5950'b0,1'b1,2'b0} : rfm_data_decoded_next = r2_mstr2; // 2 
         {5948'b0,1'b1,4'b0} : rfm_data_decoded_next = r4_mstr4; // 4 
         {5947'b0,1'b1,5'b0} : rfm_data_decoded_next = r5_stat; // 5 
         {5944'b0,1'b1,8'b0} : rfm_data_decoded_next = r8_mrctrl0; // 8 
         {5943'b0,1'b1,9'b0} : rfm_data_decoded_next = r9_mrctrl1; // 9 
         {5941'b0,1'b1,11'b0} : rfm_data_decoded_next = r11_mrstat ; // 11 
         {5940'b0,1'b1,12'b0} : rfm_data_decoded_next = r12_mrrdata0 ; // 12 
         {5939'b0,1'b1,13'b0} : rfm_data_decoded_next = r13_mrrdata1 ; // 13 
         {5938'b0,1'b1,14'b0} : rfm_data_decoded_next = r14_deratectl0; // 14 
         {5937'b0,1'b1,15'b0} : rfm_data_decoded_next = r15_deratectl1; // 15 
         {5936'b0,1'b1,16'b0} : rfm_data_decoded_next = r16_deratectl2; // 16 
         {5933'b0,1'b1,19'b0} : rfm_data_decoded_next = r19_deratectl5; // 19 
         {5932'b0,1'b1,20'b0} : rfm_data_decoded_next = r20_deratectl6; // 20 
         {5930'b0,1'b1,22'b0} : rfm_data_decoded_next = r22_deratestat0 ; // 22 
         {5928'b0,1'b1,24'b0} : rfm_data_decoded_next = r24_deratedbgctl; // 24 
         {5927'b0,1'b1,25'b0} : rfm_data_decoded_next = r25_deratedbgstat ; // 25 
         {5926'b0,1'b1,26'b0} : rfm_data_decoded_next = r26_pwrctl; // 26 
         {5925'b0,1'b1,27'b0} : rfm_data_decoded_next = r27_hwlpctl; // 27 
         {5923'b0,1'b1,29'b0} : rfm_data_decoded_next = r29_clkgatectl; // 29 
         {5922'b0,1'b1,30'b0} : rfm_data_decoded_next = r30_rfshmod0; // 30 
         {5920'b0,1'b1,32'b0} : rfm_data_decoded_next = r32_rfshctl0; // 32 
         {5919'b0,1'b1,33'b0} : rfm_data_decoded_next = r33_rfmmod0; // 33 
         {5918'b0,1'b1,34'b0} : rfm_data_decoded_next = r34_rfmmod1; // 34 
         {5917'b0,1'b1,35'b0} : rfm_data_decoded_next = r35_rfmctl; // 35 
         {5916'b0,1'b1,36'b0} : rfm_data_decoded_next = r36_rfmstat ; // 36 
         {5915'b0,1'b1,37'b0} : rfm_data_decoded_next = r37_zqctl0; // 37 
         {5914'b0,1'b1,38'b0} : rfm_data_decoded_next = r38_zqctl1; // 38 
         {5913'b0,1'b1,39'b0} : rfm_data_decoded_next = r39_zqctl2; // 39 
         {5912'b0,1'b1,40'b0} : rfm_data_decoded_next = r40_zqstat ; // 40 
         {5911'b0,1'b1,41'b0} : rfm_data_decoded_next = r41_dqsoscruntime; // 41 
         {5910'b0,1'b1,42'b0} : rfm_data_decoded_next = r42_dqsoscstat0; // 42 
         {5909'b0,1'b1,43'b0} : rfm_data_decoded_next = r43_dqsosccfg0; // 43 
         {5907'b0,1'b1,45'b0} : rfm_data_decoded_next = r45_sched0; // 45 
         {5906'b0,1'b1,46'b0} : rfm_data_decoded_next = r46_sched1; // 46 
         {5904'b0,1'b1,48'b0} : rfm_data_decoded_next = r48_sched3; // 48 
         {5903'b0,1'b1,49'b0} : rfm_data_decoded_next = r49_sched4; // 49 
         {5902'b0,1'b1,50'b0} : rfm_data_decoded_next = r50_sched5; // 50 
         {5901'b0,1'b1,51'b0} : rfm_data_decoded_next = r51_hwffcctl; // 51 
         {5900'b0,1'b1,52'b0} : rfm_data_decoded_next = r52_hwffcstat ; // 52 
         {5890'b0,1'b1,62'b0} : rfm_data_decoded_next = r62_dfilpcfg0; // 62 
         {5889'b0,1'b1,63'b0} : rfm_data_decoded_next = r63_dfiupd0; // 63 
         {5887'b0,1'b1,65'b0} : rfm_data_decoded_next = r65_dfimisc; // 65 
         {5886'b0,1'b1,66'b0} : rfm_data_decoded_next = r66_dfistat ; // 66 
         {5885'b0,1'b1,67'b0} : rfm_data_decoded_next = r67_dfiphymstr; // 67 
         {5875'b0,1'b1,77'b0} : rfm_data_decoded_next = r77_poisoncfg; // 77 
         {5874'b0,1'b1,78'b0} : rfm_data_decoded_next = r78_poisonstat ; // 78 
         {5873'b0,1'b1,79'b0} : rfm_data_decoded_next = r79_ecccfg0; // 79 
         {5872'b0,1'b1,80'b0} : rfm_data_decoded_next = r80_ecccfg1; // 80 
         {5871'b0,1'b1,81'b0} : rfm_data_decoded_next = r81_eccstat ; // 81 
         {5870'b0,1'b1,82'b0} : rfm_data_decoded_next = r82_eccctl; // 82 
         {5869'b0,1'b1,83'b0} : rfm_data_decoded_next = r83_eccerrcnt ; // 83 
         {5868'b0,1'b1,84'b0} : rfm_data_decoded_next = r84_ecccaddr0 ; // 84 
         {5867'b0,1'b1,85'b0} : rfm_data_decoded_next = r85_ecccaddr1 ; // 85 
         {5866'b0,1'b1,86'b0} : rfm_data_decoded_next = r86_ecccsyn0 ; // 86 
         {5865'b0,1'b1,87'b0} : rfm_data_decoded_next = r87_ecccsyn1 ; // 87 
         {5864'b0,1'b1,88'b0} : rfm_data_decoded_next = r88_ecccsyn2 ; // 88 
         {5863'b0,1'b1,89'b0} : rfm_data_decoded_next = r89_eccbitmask0 ; // 89 
         {5862'b0,1'b1,90'b0} : rfm_data_decoded_next = r90_eccbitmask1 ; // 90 
         {5861'b0,1'b1,91'b0} : rfm_data_decoded_next = r91_eccbitmask2 ; // 91 
         {5860'b0,1'b1,92'b0} : rfm_data_decoded_next = r92_eccuaddr0 ; // 92 
         {5859'b0,1'b1,93'b0} : rfm_data_decoded_next = r93_eccuaddr1 ; // 93 
         {5858'b0,1'b1,94'b0} : rfm_data_decoded_next = r94_eccusyn0 ; // 94 
         {5857'b0,1'b1,95'b0} : rfm_data_decoded_next = r95_eccusyn1 ; // 95 
         {5856'b0,1'b1,96'b0} : rfm_data_decoded_next = r96_eccusyn2 ; // 96 
         {5855'b0,1'b1,97'b0} : rfm_data_decoded_next = r97_eccpoisonaddr0; // 97 
         {5854'b0,1'b1,98'b0} : rfm_data_decoded_next = r98_eccpoisonaddr1; // 98 
         {5851'b0,1'b1,101'b0} : rfm_data_decoded_next = r101_eccpoisonpat0; // 101 
         {5849'b0,1'b1,103'b0} : rfm_data_decoded_next = r103_eccpoisonpat2; // 103 
         {5848'b0,1'b1,104'b0} : rfm_data_decoded_next = r104_eccapstat ; // 104 
         {5791'b0,1'b1,161'b0} : rfm_data_decoded_next = r161_lnkeccctl1; // 161 
         {5790'b0,1'b1,162'b0} : rfm_data_decoded_next = r162_lnkeccpoisonctl0; // 162 
         {5789'b0,1'b1,163'b0} : rfm_data_decoded_next = r163_lnkeccpoisonstat ; // 163 
         {5788'b0,1'b1,164'b0} : rfm_data_decoded_next = r164_lnkeccindex; // 164 
         {5787'b0,1'b1,165'b0} : rfm_data_decoded_next = r165_lnkeccerrcnt0 ; // 165 
         {5786'b0,1'b1,166'b0} : rfm_data_decoded_next = r166_lnkeccerrstat ; // 166 
         {5777'b0,1'b1,175'b0} : rfm_data_decoded_next = r175_lnkecccaddr0 ; // 175 
         {5776'b0,1'b1,176'b0} : rfm_data_decoded_next = r176_lnkecccaddr1 ; // 176 
         {5775'b0,1'b1,177'b0} : rfm_data_decoded_next = r177_lnkeccuaddr0 ; // 177 
         {5774'b0,1'b1,178'b0} : rfm_data_decoded_next = r178_lnkeccuaddr1 ; // 178 
         {5718'b0,1'b1,234'b0} : rfm_data_decoded_next = r234_opctrl0; // 234 
         {5717'b0,1'b1,235'b0} : rfm_data_decoded_next = r235_opctrl1; // 235 
         {5716'b0,1'b1,236'b0} : rfm_data_decoded_next = r236_opctrlcam ; // 236 
         {5715'b0,1'b1,237'b0} : rfm_data_decoded_next = r237_opctrlcmd; // 237 
         {5714'b0,1'b1,238'b0} : rfm_data_decoded_next = r238_opctrlstat ; // 238 
         {5713'b0,1'b1,239'b0} : rfm_data_decoded_next = r239_opctrlcam1 ; // 239 
         {5712'b0,1'b1,240'b0} : rfm_data_decoded_next = r240_oprefctrl0; // 240 
         {5710'b0,1'b1,242'b0} : rfm_data_decoded_next = r242_oprefstat0 ; // 242 
         {5703'b0,1'b1,249'b0} : rfm_data_decoded_next = r249_swctl; // 249 
         {5702'b0,1'b1,250'b0} : rfm_data_decoded_next = r250_swstat ; // 250 
         {5699'b0,1'b1,253'b0} : rfm_data_decoded_next = r253_rankctl; // 253 
         {5698'b0,1'b1,254'b0} : rfm_data_decoded_next = r254_dbictl; // 254 
         {5696'b0,1'b1,256'b0} : rfm_data_decoded_next = r256_odtmap; // 256 
         {5695'b0,1'b1,257'b0} : rfm_data_decoded_next = r257_datactl0; // 257 
         {5694'b0,1'b1,258'b0} : rfm_data_decoded_next = r258_swctlstatic; // 258 
         {5693'b0,1'b1,259'b0} : rfm_data_decoded_next = r259_cgctl; // 259 
         {5692'b0,1'b1,260'b0} : rfm_data_decoded_next = r260_inittmg0; // 260 
         {5667'b0,1'b1,285'b0} : rfm_data_decoded_next = r285_ppt2ctrl0; // 285 
         {5666'b0,1'b1,286'b0} : rfm_data_decoded_next = r286_ppt2stat0 ; // 286 
         {5663'b0,1'b1,289'b0} : rfm_data_decoded_next = r289_ddrctl_ver_number ; // 289 
         {5662'b0,1'b1,290'b0} : rfm_data_decoded_next = r290_ddrctl_ver_type ; // 290 
         {5457'b0,1'b1,495'b0} : rfm_data_decoded_next = r495_addrmap1_map0; // 495 
         {5455'b0,1'b1,497'b0} : rfm_data_decoded_next = r497_addrmap3_map0; // 497 
         {5454'b0,1'b1,498'b0} : rfm_data_decoded_next = r498_addrmap4_map0; // 498 
         {5453'b0,1'b1,499'b0} : rfm_data_decoded_next = r499_addrmap5_map0; // 499 
         {5452'b0,1'b1,500'b0} : rfm_data_decoded_next = r500_addrmap6_map0; // 500 
         {5451'b0,1'b1,501'b0} : rfm_data_decoded_next = r501_addrmap7_map0; // 501 
         {5450'b0,1'b1,502'b0} : rfm_data_decoded_next = r502_addrmap8_map0; // 502 
         {5449'b0,1'b1,503'b0} : rfm_data_decoded_next = r503_addrmap9_map0; // 503 
         {5448'b0,1'b1,504'b0} : rfm_data_decoded_next = r504_addrmap10_map0; // 504 
         {5447'b0,1'b1,505'b0} : rfm_data_decoded_next = r505_addrmap11_map0; // 505 
         {5446'b0,1'b1,506'b0} : rfm_data_decoded_next = r506_addrmap12_map0; // 506 
         {5431'b0,1'b1,521'b0} : rfm_data_decoded_next = r521_pccfg_port0; // 521 
         {5430'b0,1'b1,522'b0} : rfm_data_decoded_next = r522_pcfgr_port0; // 522 
         {5429'b0,1'b1,523'b0} : rfm_data_decoded_next = r523_pcfgw_port0; // 523 
         {5396'b0,1'b1,556'b0} : rfm_data_decoded_next = r556_pctrl_port0; // 556 
         {5395'b0,1'b1,557'b0} : rfm_data_decoded_next = r557_pcfgqos0_port0; // 557 
         {5394'b0,1'b1,558'b0} : rfm_data_decoded_next = r558_pcfgqos1_port0; // 558 
         {5393'b0,1'b1,559'b0} : rfm_data_decoded_next = r559_pcfgwqos0_port0; // 559 
         {5392'b0,1'b1,560'b0} : rfm_data_decoded_next = r560_pcfgwqos1_port0; // 560 
         {5383'b0,1'b1,569'b0} : rfm_data_decoded_next = r569_sbrctl_port0; // 569 
         {5382'b0,1'b1,570'b0} : rfm_data_decoded_next = r570_sbrstat_port0 ; // 570 
         {5381'b0,1'b1,571'b0} : rfm_data_decoded_next = r571_sbrwdata0_port0; // 571 
         {5379'b0,1'b1,573'b0} : rfm_data_decoded_next = r573_sbrstart0_port0; // 573 
         {5378'b0,1'b1,574'b0} : rfm_data_decoded_next = r574_sbrstart1_port0; // 574 
         {5377'b0,1'b1,575'b0} : rfm_data_decoded_next = r575_sbrrange0_port0; // 575 
         {5376'b0,1'b1,576'b0} : rfm_data_decoded_next = r576_sbrrange1_port0; // 576 
         {5370'b0,1'b1,582'b0} : rfm_data_decoded_next = r582_pstat_port0 ; // 582 
         {4023'b0,1'b1,1929'b0} : rfm_data_decoded_next = r1929_dramset1tmg0_freq0; // 1929 
         {4022'b0,1'b1,1930'b0} : rfm_data_decoded_next = r1930_dramset1tmg1_freq0; // 1930 
         {4021'b0,1'b1,1931'b0} : rfm_data_decoded_next = r1931_dramset1tmg2_freq0; // 1931 
         {4020'b0,1'b1,1932'b0} : rfm_data_decoded_next = r1932_dramset1tmg3_freq0; // 1932 
         {4019'b0,1'b1,1933'b0} : rfm_data_decoded_next = r1933_dramset1tmg4_freq0; // 1933 
         {4018'b0,1'b1,1934'b0} : rfm_data_decoded_next = r1934_dramset1tmg5_freq0; // 1934 
         {4017'b0,1'b1,1935'b0} : rfm_data_decoded_next = r1935_dramset1tmg6_freq0; // 1935 
         {4016'b0,1'b1,1936'b0} : rfm_data_decoded_next = r1936_dramset1tmg7_freq0; // 1936 
         {4014'b0,1'b1,1938'b0} : rfm_data_decoded_next = r1938_dramset1tmg9_freq0; // 1938 
         {4011'b0,1'b1,1941'b0} : rfm_data_decoded_next = r1941_dramset1tmg12_freq0; // 1941 
         {4010'b0,1'b1,1942'b0} : rfm_data_decoded_next = r1942_dramset1tmg13_freq0; // 1942 
         {4009'b0,1'b1,1943'b0} : rfm_data_decoded_next = r1943_dramset1tmg14_freq0; // 1943 
         {4006'b0,1'b1,1946'b0} : rfm_data_decoded_next = r1946_dramset1tmg17_freq0; // 1946 
         {4001'b0,1'b1,1951'b0} : rfm_data_decoded_next = r1951_dramset1tmg23_freq0; // 1951 
         {4000'b0,1'b1,1952'b0} : rfm_data_decoded_next = r1952_dramset1tmg24_freq0; // 1952 
         {3999'b0,1'b1,1953'b0} : rfm_data_decoded_next = r1953_dramset1tmg25_freq0; // 1953 
         {3994'b0,1'b1,1958'b0} : rfm_data_decoded_next = r1958_dramset1tmg30_freq0; // 1958 
         {3992'b0,1'b1,1960'b0} : rfm_data_decoded_next = r1960_dramset1tmg32_freq0; // 1960 
         {3961'b0,1'b1,1991'b0} : rfm_data_decoded_next = r1991_initmr0_freq0; // 1991 
         {3960'b0,1'b1,1992'b0} : rfm_data_decoded_next = r1992_initmr1_freq0; // 1992 
         {3959'b0,1'b1,1993'b0} : rfm_data_decoded_next = r1993_initmr2_freq0; // 1993 
         {3958'b0,1'b1,1994'b0} : rfm_data_decoded_next = r1994_initmr3_freq0; // 1994 
         {3957'b0,1'b1,1995'b0} : rfm_data_decoded_next = r1995_dfitmg0_freq0; // 1995 
         {3956'b0,1'b1,1996'b0} : rfm_data_decoded_next = r1996_dfitmg1_freq0; // 1996 
         {3955'b0,1'b1,1997'b0} : rfm_data_decoded_next = r1997_dfitmg2_freq0; // 1997 
         {3953'b0,1'b1,1999'b0} : rfm_data_decoded_next = r1999_dfitmg4_freq0; // 1999 
         {3952'b0,1'b1,2000'b0} : rfm_data_decoded_next = r2000_dfitmg5_freq0; // 2000 
         {3951'b0,1'b1,2001'b0} : rfm_data_decoded_next = r2001_dfitmg6_freq0; // 2001 
         {3949'b0,1'b1,2003'b0} : rfm_data_decoded_next = r2003_dfilptmg0_freq0; // 2003 
         {3948'b0,1'b1,2004'b0} : rfm_data_decoded_next = r2004_dfilptmg1_freq0; // 2004 
         {3947'b0,1'b1,2005'b0} : rfm_data_decoded_next = r2005_dfiupdtmg0_freq0; // 2005 
         {3946'b0,1'b1,2006'b0} : rfm_data_decoded_next = r2006_dfiupdtmg1_freq0; // 2006 
         {3944'b0,1'b1,2008'b0} : rfm_data_decoded_next = r2008_dfiupdtmg2_freq0; // 2008 
         {3943'b0,1'b1,2009'b0} : rfm_data_decoded_next = r2009_dfiupdtmg3_freq0; // 2009 
         {3942'b0,1'b1,2010'b0} : rfm_data_decoded_next = r2010_rfshset1tmg0_freq0; // 2010 
         {3941'b0,1'b1,2011'b0} : rfm_data_decoded_next = r2011_rfshset1tmg1_freq0; // 2011 
         {3940'b0,1'b1,2012'b0} : rfm_data_decoded_next = r2012_rfshset1tmg2_freq0; // 2012 
         {3939'b0,1'b1,2013'b0} : rfm_data_decoded_next = r2013_rfshset1tmg3_freq0; // 2013 
         {3938'b0,1'b1,2014'b0} : rfm_data_decoded_next = r2014_rfshset1tmg4_freq0; // 2014 
         {3928'b0,1'b1,2024'b0} : rfm_data_decoded_next = r2024_rfmset1tmg0_freq0; // 2024 
         {3917'b0,1'b1,2035'b0} : rfm_data_decoded_next = r2035_zqset1tmg0_freq0; // 2035 
         {3916'b0,1'b1,2036'b0} : rfm_data_decoded_next = r2036_zqset1tmg1_freq0; // 2036 
         {3915'b0,1'b1,2037'b0} : rfm_data_decoded_next = r2037_zqset1tmg2_freq0; // 2037 
         {3906'b0,1'b1,2046'b0} : rfm_data_decoded_next = r2046_dqsoscctl0_freq0; // 2046 
         {3905'b0,1'b1,2047'b0} : rfm_data_decoded_next = r2047_derateint_freq0; // 2047 
         {3904'b0,1'b1,2048'b0} : rfm_data_decoded_next = r2048_derateval0_freq0; // 2048 
         {3903'b0,1'b1,2049'b0} : rfm_data_decoded_next = r2049_derateval1_freq0; // 2049 
         {3902'b0,1'b1,2050'b0} : rfm_data_decoded_next = r2050_hwlptmg0_freq0; // 2050 
         {3901'b0,1'b1,2051'b0} : rfm_data_decoded_next = r2051_dvfsctl0_freq0; // 2051 
         {3900'b0,1'b1,2052'b0} : rfm_data_decoded_next = r2052_schedtmg0_freq0; // 2052 
         {3899'b0,1'b1,2053'b0} : rfm_data_decoded_next = r2053_perfhpr1_freq0; // 2053 
         {3898'b0,1'b1,2054'b0} : rfm_data_decoded_next = r2054_perflpr1_freq0; // 2054 
         {3897'b0,1'b1,2055'b0} : rfm_data_decoded_next = r2055_perfwr1_freq0; // 2055 
         {3896'b0,1'b1,2056'b0} : rfm_data_decoded_next = r2056_tmgcfg_freq0; // 2056 
         {3895'b0,1'b1,2057'b0} : rfm_data_decoded_next = r2057_ranktmg0_freq0; // 2057 
         {3894'b0,1'b1,2058'b0} : rfm_data_decoded_next = r2058_ranktmg1_freq0; // 2058 
         {3893'b0,1'b1,2059'b0} : rfm_data_decoded_next = r2059_pwrtmg_freq0; // 2059 
         {3887'b0,1'b1,2065'b0} : rfm_data_decoded_next = r2065_ddr4pprtmg0_freq0; // 2065 
         {3886'b0,1'b1,2066'b0} : rfm_data_decoded_next = r2066_ddr4pprtmg1_freq0; // 2066 
         {3885'b0,1'b1,2067'b0} : rfm_data_decoded_next = r2067_lnkeccctl0_freq0; // 2067 
         {3751'b0,1'b1,2201'b0} : rfm_data_decoded_next = r2201_dramset1tmg0_freq1; // 2201 
         {3750'b0,1'b1,2202'b0} : rfm_data_decoded_next = r2202_dramset1tmg1_freq1; // 2202 
         {3749'b0,1'b1,2203'b0} : rfm_data_decoded_next = r2203_dramset1tmg2_freq1; // 2203 
         {3748'b0,1'b1,2204'b0} : rfm_data_decoded_next = r2204_dramset1tmg3_freq1; // 2204 
         {3747'b0,1'b1,2205'b0} : rfm_data_decoded_next = r2205_dramset1tmg4_freq1; // 2205 
         {3746'b0,1'b1,2206'b0} : rfm_data_decoded_next = r2206_dramset1tmg5_freq1; // 2206 
         {3745'b0,1'b1,2207'b0} : rfm_data_decoded_next = r2207_dramset1tmg6_freq1; // 2207 
         {3744'b0,1'b1,2208'b0} : rfm_data_decoded_next = r2208_dramset1tmg7_freq1; // 2208 
         {3742'b0,1'b1,2210'b0} : rfm_data_decoded_next = r2210_dramset1tmg9_freq1; // 2210 
         {3739'b0,1'b1,2213'b0} : rfm_data_decoded_next = r2213_dramset1tmg12_freq1; // 2213 
         {3738'b0,1'b1,2214'b0} : rfm_data_decoded_next = r2214_dramset1tmg13_freq1; // 2214 
         {3737'b0,1'b1,2215'b0} : rfm_data_decoded_next = r2215_dramset1tmg14_freq1; // 2215 
         {3734'b0,1'b1,2218'b0} : rfm_data_decoded_next = r2218_dramset1tmg17_freq1; // 2218 
         {3729'b0,1'b1,2223'b0} : rfm_data_decoded_next = r2223_dramset1tmg23_freq1; // 2223 
         {3728'b0,1'b1,2224'b0} : rfm_data_decoded_next = r2224_dramset1tmg24_freq1; // 2224 
         {3727'b0,1'b1,2225'b0} : rfm_data_decoded_next = r2225_dramset1tmg25_freq1; // 2225 
         {3722'b0,1'b1,2230'b0} : rfm_data_decoded_next = r2230_dramset1tmg30_freq1; // 2230 
         {3720'b0,1'b1,2232'b0} : rfm_data_decoded_next = r2232_dramset1tmg32_freq1; // 2232 
         {3689'b0,1'b1,2263'b0} : rfm_data_decoded_next = r2263_initmr0_freq1; // 2263 
         {3688'b0,1'b1,2264'b0} : rfm_data_decoded_next = r2264_initmr1_freq1; // 2264 
         {3687'b0,1'b1,2265'b0} : rfm_data_decoded_next = r2265_initmr2_freq1; // 2265 
         {3686'b0,1'b1,2266'b0} : rfm_data_decoded_next = r2266_initmr3_freq1; // 2266 
         {3685'b0,1'b1,2267'b0} : rfm_data_decoded_next = r2267_dfitmg0_freq1; // 2267 
         {3684'b0,1'b1,2268'b0} : rfm_data_decoded_next = r2268_dfitmg1_freq1; // 2268 
         {3683'b0,1'b1,2269'b0} : rfm_data_decoded_next = r2269_dfitmg2_freq1; // 2269 
         {3681'b0,1'b1,2271'b0} : rfm_data_decoded_next = r2271_dfitmg4_freq1; // 2271 
         {3680'b0,1'b1,2272'b0} : rfm_data_decoded_next = r2272_dfitmg5_freq1; // 2272 
         {3679'b0,1'b1,2273'b0} : rfm_data_decoded_next = r2273_dfitmg6_freq1; // 2273 
         {3677'b0,1'b1,2275'b0} : rfm_data_decoded_next = r2275_dfiupdtmg1_freq1; // 2275 
         {3676'b0,1'b1,2276'b0} : rfm_data_decoded_next = r2276_dfiupdtmg2_freq1; // 2276 
         {3675'b0,1'b1,2277'b0} : rfm_data_decoded_next = r2277_dfiupdtmg3_freq1; // 2277 
         {3674'b0,1'b1,2278'b0} : rfm_data_decoded_next = r2278_rfshset1tmg0_freq1; // 2278 
         {3673'b0,1'b1,2279'b0} : rfm_data_decoded_next = r2279_rfshset1tmg1_freq1; // 2279 
         {3672'b0,1'b1,2280'b0} : rfm_data_decoded_next = r2280_rfshset1tmg2_freq1; // 2280 
         {3671'b0,1'b1,2281'b0} : rfm_data_decoded_next = r2281_rfshset1tmg3_freq1; // 2281 
         {3670'b0,1'b1,2282'b0} : rfm_data_decoded_next = r2282_rfshset1tmg4_freq1; // 2282 
         {3660'b0,1'b1,2292'b0} : rfm_data_decoded_next = r2292_rfmset1tmg0_freq1; // 2292 
         {3649'b0,1'b1,2303'b0} : rfm_data_decoded_next = r2303_zqset1tmg0_freq1; // 2303 
         {3648'b0,1'b1,2304'b0} : rfm_data_decoded_next = r2304_zqset1tmg1_freq1; // 2304 
         {3647'b0,1'b1,2305'b0} : rfm_data_decoded_next = r2305_zqset1tmg2_freq1; // 2305 
         {3638'b0,1'b1,2314'b0} : rfm_data_decoded_next = r2314_dqsoscctl0_freq1; // 2314 
         {3637'b0,1'b1,2315'b0} : rfm_data_decoded_next = r2315_derateint_freq1; // 2315 
         {3636'b0,1'b1,2316'b0} : rfm_data_decoded_next = r2316_derateval0_freq1; // 2316 
         {3635'b0,1'b1,2317'b0} : rfm_data_decoded_next = r2317_derateval1_freq1; // 2317 
         {3634'b0,1'b1,2318'b0} : rfm_data_decoded_next = r2318_hwlptmg0_freq1; // 2318 
         {3633'b0,1'b1,2319'b0} : rfm_data_decoded_next = r2319_dvfsctl0_freq1; // 2319 
         {3632'b0,1'b1,2320'b0} : rfm_data_decoded_next = r2320_schedtmg0_freq1; // 2320 
         {3631'b0,1'b1,2321'b0} : rfm_data_decoded_next = r2321_perfhpr1_freq1; // 2321 
         {3630'b0,1'b1,2322'b0} : rfm_data_decoded_next = r2322_perflpr1_freq1; // 2322 
         {3629'b0,1'b1,2323'b0} : rfm_data_decoded_next = r2323_perfwr1_freq1; // 2323 
         {3628'b0,1'b1,2324'b0} : rfm_data_decoded_next = r2324_tmgcfg_freq1; // 2324 
         {3627'b0,1'b1,2325'b0} : rfm_data_decoded_next = r2325_ranktmg0_freq1; // 2325 
         {3626'b0,1'b1,2326'b0} : rfm_data_decoded_next = r2326_ranktmg1_freq1; // 2326 
         {3625'b0,1'b1,2327'b0} : rfm_data_decoded_next = r2327_pwrtmg_freq1; // 2327 
         {3619'b0,1'b1,2333'b0} : rfm_data_decoded_next = r2333_ddr4pprtmg0_freq1; // 2333 
         {3618'b0,1'b1,2334'b0} : rfm_data_decoded_next = r2334_ddr4pprtmg1_freq1; // 2334 
         {3617'b0,1'b1,2335'b0} : rfm_data_decoded_next = r2335_lnkeccctl0_freq1; // 2335 
         {3483'b0,1'b1,2469'b0} : rfm_data_decoded_next = r2469_dramset1tmg0_freq2; // 2469 
         {3482'b0,1'b1,2470'b0} : rfm_data_decoded_next = r2470_dramset1tmg1_freq2; // 2470 
         {3481'b0,1'b1,2471'b0} : rfm_data_decoded_next = r2471_dramset1tmg2_freq2; // 2471 
         {3480'b0,1'b1,2472'b0} : rfm_data_decoded_next = r2472_dramset1tmg3_freq2; // 2472 
         {3479'b0,1'b1,2473'b0} : rfm_data_decoded_next = r2473_dramset1tmg4_freq2; // 2473 
         {3478'b0,1'b1,2474'b0} : rfm_data_decoded_next = r2474_dramset1tmg5_freq2; // 2474 
         {3477'b0,1'b1,2475'b0} : rfm_data_decoded_next = r2475_dramset1tmg6_freq2; // 2475 
         {3476'b0,1'b1,2476'b0} : rfm_data_decoded_next = r2476_dramset1tmg7_freq2; // 2476 
         {3474'b0,1'b1,2478'b0} : rfm_data_decoded_next = r2478_dramset1tmg9_freq2; // 2478 
         {3471'b0,1'b1,2481'b0} : rfm_data_decoded_next = r2481_dramset1tmg12_freq2; // 2481 
         {3470'b0,1'b1,2482'b0} : rfm_data_decoded_next = r2482_dramset1tmg13_freq2; // 2482 
         {3469'b0,1'b1,2483'b0} : rfm_data_decoded_next = r2483_dramset1tmg14_freq2; // 2483 
         {3466'b0,1'b1,2486'b0} : rfm_data_decoded_next = r2486_dramset1tmg17_freq2; // 2486 
         {3461'b0,1'b1,2491'b0} : rfm_data_decoded_next = r2491_dramset1tmg23_freq2; // 2491 
         {3460'b0,1'b1,2492'b0} : rfm_data_decoded_next = r2492_dramset1tmg24_freq2; // 2492 
         {3459'b0,1'b1,2493'b0} : rfm_data_decoded_next = r2493_dramset1tmg25_freq2; // 2493 
         {3454'b0,1'b1,2498'b0} : rfm_data_decoded_next = r2498_dramset1tmg30_freq2; // 2498 
         {3452'b0,1'b1,2500'b0} : rfm_data_decoded_next = r2500_dramset1tmg32_freq2; // 2500 
         {3421'b0,1'b1,2531'b0} : rfm_data_decoded_next = r2531_initmr0_freq2; // 2531 
         {3420'b0,1'b1,2532'b0} : rfm_data_decoded_next = r2532_initmr1_freq2; // 2532 
         {3419'b0,1'b1,2533'b0} : rfm_data_decoded_next = r2533_initmr2_freq2; // 2533 
         {3418'b0,1'b1,2534'b0} : rfm_data_decoded_next = r2534_initmr3_freq2; // 2534 
         {3417'b0,1'b1,2535'b0} : rfm_data_decoded_next = r2535_dfitmg0_freq2; // 2535 
         {3416'b0,1'b1,2536'b0} : rfm_data_decoded_next = r2536_dfitmg1_freq2; // 2536 
         {3415'b0,1'b1,2537'b0} : rfm_data_decoded_next = r2537_dfitmg2_freq2; // 2537 
         {3413'b0,1'b1,2539'b0} : rfm_data_decoded_next = r2539_dfitmg4_freq2; // 2539 
         {3412'b0,1'b1,2540'b0} : rfm_data_decoded_next = r2540_dfitmg5_freq2; // 2540 
         {3411'b0,1'b1,2541'b0} : rfm_data_decoded_next = r2541_dfitmg6_freq2; // 2541 
         {3409'b0,1'b1,2543'b0} : rfm_data_decoded_next = r2543_dfiupdtmg1_freq2; // 2543 
         {3408'b0,1'b1,2544'b0} : rfm_data_decoded_next = r2544_dfiupdtmg2_freq2; // 2544 
         {3407'b0,1'b1,2545'b0} : rfm_data_decoded_next = r2545_dfiupdtmg3_freq2; // 2545 
         {3406'b0,1'b1,2546'b0} : rfm_data_decoded_next = r2546_rfshset1tmg0_freq2; // 2546 
         {3405'b0,1'b1,2547'b0} : rfm_data_decoded_next = r2547_rfshset1tmg1_freq2; // 2547 
         {3404'b0,1'b1,2548'b0} : rfm_data_decoded_next = r2548_rfshset1tmg2_freq2; // 2548 
         {3403'b0,1'b1,2549'b0} : rfm_data_decoded_next = r2549_rfshset1tmg3_freq2; // 2549 
         {3402'b0,1'b1,2550'b0} : rfm_data_decoded_next = r2550_rfshset1tmg4_freq2; // 2550 
         {3392'b0,1'b1,2560'b0} : rfm_data_decoded_next = r2560_rfmset1tmg0_freq2; // 2560 
         {3381'b0,1'b1,2571'b0} : rfm_data_decoded_next = r2571_zqset1tmg0_freq2; // 2571 
         {3380'b0,1'b1,2572'b0} : rfm_data_decoded_next = r2572_zqset1tmg1_freq2; // 2572 
         {3379'b0,1'b1,2573'b0} : rfm_data_decoded_next = r2573_zqset1tmg2_freq2; // 2573 
         {3370'b0,1'b1,2582'b0} : rfm_data_decoded_next = r2582_dqsoscctl0_freq2; // 2582 
         {3369'b0,1'b1,2583'b0} : rfm_data_decoded_next = r2583_derateint_freq2; // 2583 
         {3368'b0,1'b1,2584'b0} : rfm_data_decoded_next = r2584_derateval0_freq2; // 2584 
         {3367'b0,1'b1,2585'b0} : rfm_data_decoded_next = r2585_derateval1_freq2; // 2585 
         {3366'b0,1'b1,2586'b0} : rfm_data_decoded_next = r2586_hwlptmg0_freq2; // 2586 
         {3365'b0,1'b1,2587'b0} : rfm_data_decoded_next = r2587_dvfsctl0_freq2; // 2587 
         {3364'b0,1'b1,2588'b0} : rfm_data_decoded_next = r2588_schedtmg0_freq2; // 2588 
         {3363'b0,1'b1,2589'b0} : rfm_data_decoded_next = r2589_perfhpr1_freq2; // 2589 
         {3362'b0,1'b1,2590'b0} : rfm_data_decoded_next = r2590_perflpr1_freq2; // 2590 
         {3361'b0,1'b1,2591'b0} : rfm_data_decoded_next = r2591_perfwr1_freq2; // 2591 
         {3360'b0,1'b1,2592'b0} : rfm_data_decoded_next = r2592_tmgcfg_freq2; // 2592 
         {3359'b0,1'b1,2593'b0} : rfm_data_decoded_next = r2593_ranktmg0_freq2; // 2593 
         {3358'b0,1'b1,2594'b0} : rfm_data_decoded_next = r2594_ranktmg1_freq2; // 2594 
         {3357'b0,1'b1,2595'b0} : rfm_data_decoded_next = r2595_pwrtmg_freq2; // 2595 
         {3351'b0,1'b1,2601'b0} : rfm_data_decoded_next = r2601_ddr4pprtmg0_freq2; // 2601 
         {3350'b0,1'b1,2602'b0} : rfm_data_decoded_next = r2602_ddr4pprtmg1_freq2; // 2602 
         {3349'b0,1'b1,2603'b0} : rfm_data_decoded_next = r2603_lnkeccctl0_freq2; // 2603 
         {3215'b0,1'b1,2737'b0} : rfm_data_decoded_next = r2737_dramset1tmg0_freq3; // 2737 
         {3214'b0,1'b1,2738'b0} : rfm_data_decoded_next = r2738_dramset1tmg1_freq3; // 2738 
         {3213'b0,1'b1,2739'b0} : rfm_data_decoded_next = r2739_dramset1tmg2_freq3; // 2739 
         {3212'b0,1'b1,2740'b0} : rfm_data_decoded_next = r2740_dramset1tmg3_freq3; // 2740 
         {3211'b0,1'b1,2741'b0} : rfm_data_decoded_next = r2741_dramset1tmg4_freq3; // 2741 
         {3210'b0,1'b1,2742'b0} : rfm_data_decoded_next = r2742_dramset1tmg5_freq3; // 2742 
         {3209'b0,1'b1,2743'b0} : rfm_data_decoded_next = r2743_dramset1tmg6_freq3; // 2743 
         {3208'b0,1'b1,2744'b0} : rfm_data_decoded_next = r2744_dramset1tmg7_freq3; // 2744 
         {3206'b0,1'b1,2746'b0} : rfm_data_decoded_next = r2746_dramset1tmg9_freq3; // 2746 
         {3203'b0,1'b1,2749'b0} : rfm_data_decoded_next = r2749_dramset1tmg12_freq3; // 2749 
         {3202'b0,1'b1,2750'b0} : rfm_data_decoded_next = r2750_dramset1tmg13_freq3; // 2750 
         {3201'b0,1'b1,2751'b0} : rfm_data_decoded_next = r2751_dramset1tmg14_freq3; // 2751 
         {3198'b0,1'b1,2754'b0} : rfm_data_decoded_next = r2754_dramset1tmg17_freq3; // 2754 
         {3193'b0,1'b1,2759'b0} : rfm_data_decoded_next = r2759_dramset1tmg23_freq3; // 2759 
         {3192'b0,1'b1,2760'b0} : rfm_data_decoded_next = r2760_dramset1tmg24_freq3; // 2760 
         {3191'b0,1'b1,2761'b0} : rfm_data_decoded_next = r2761_dramset1tmg25_freq3; // 2761 
         {3186'b0,1'b1,2766'b0} : rfm_data_decoded_next = r2766_dramset1tmg30_freq3; // 2766 
         {3184'b0,1'b1,2768'b0} : rfm_data_decoded_next = r2768_dramset1tmg32_freq3; // 2768 
         {3153'b0,1'b1,2799'b0} : rfm_data_decoded_next = r2799_initmr0_freq3; // 2799 
         {3152'b0,1'b1,2800'b0} : rfm_data_decoded_next = r2800_initmr1_freq3; // 2800 
         {3151'b0,1'b1,2801'b0} : rfm_data_decoded_next = r2801_initmr2_freq3; // 2801 
         {3150'b0,1'b1,2802'b0} : rfm_data_decoded_next = r2802_initmr3_freq3; // 2802 
         {3149'b0,1'b1,2803'b0} : rfm_data_decoded_next = r2803_dfitmg0_freq3; // 2803 
         {3148'b0,1'b1,2804'b0} : rfm_data_decoded_next = r2804_dfitmg1_freq3; // 2804 
         {3147'b0,1'b1,2805'b0} : rfm_data_decoded_next = r2805_dfitmg2_freq3; // 2805 
         {3145'b0,1'b1,2807'b0} : rfm_data_decoded_next = r2807_dfitmg4_freq3; // 2807 
         {3144'b0,1'b1,2808'b0} : rfm_data_decoded_next = r2808_dfitmg5_freq3; // 2808 
         {3143'b0,1'b1,2809'b0} : rfm_data_decoded_next = r2809_dfitmg6_freq3; // 2809 
         {3141'b0,1'b1,2811'b0} : rfm_data_decoded_next = r2811_dfiupdtmg1_freq3; // 2811 
         {3140'b0,1'b1,2812'b0} : rfm_data_decoded_next = r2812_dfiupdtmg2_freq3; // 2812 
         {3139'b0,1'b1,2813'b0} : rfm_data_decoded_next = r2813_dfiupdtmg3_freq3; // 2813 
         {3138'b0,1'b1,2814'b0} : rfm_data_decoded_next = r2814_rfshset1tmg0_freq3; // 2814 
         {3137'b0,1'b1,2815'b0} : rfm_data_decoded_next = r2815_rfshset1tmg1_freq3; // 2815 
         {3136'b0,1'b1,2816'b0} : rfm_data_decoded_next = r2816_rfshset1tmg2_freq3; // 2816 
         {3135'b0,1'b1,2817'b0} : rfm_data_decoded_next = r2817_rfshset1tmg3_freq3; // 2817 
         {3134'b0,1'b1,2818'b0} : rfm_data_decoded_next = r2818_rfshset1tmg4_freq3; // 2818 
         {3124'b0,1'b1,2828'b0} : rfm_data_decoded_next = r2828_rfmset1tmg0_freq3; // 2828 
         {3113'b0,1'b1,2839'b0} : rfm_data_decoded_next = r2839_zqset1tmg0_freq3; // 2839 
         {3112'b0,1'b1,2840'b0} : rfm_data_decoded_next = r2840_zqset1tmg1_freq3; // 2840 
         {3111'b0,1'b1,2841'b0} : rfm_data_decoded_next = r2841_zqset1tmg2_freq3; // 2841 
         {3102'b0,1'b1,2850'b0} : rfm_data_decoded_next = r2850_dqsoscctl0_freq3; // 2850 
         {3101'b0,1'b1,2851'b0} : rfm_data_decoded_next = r2851_derateint_freq3; // 2851 
         {3100'b0,1'b1,2852'b0} : rfm_data_decoded_next = r2852_derateval0_freq3; // 2852 
         {3099'b0,1'b1,2853'b0} : rfm_data_decoded_next = r2853_derateval1_freq3; // 2853 
         {3098'b0,1'b1,2854'b0} : rfm_data_decoded_next = r2854_hwlptmg0_freq3; // 2854 
         {3097'b0,1'b1,2855'b0} : rfm_data_decoded_next = r2855_dvfsctl0_freq3; // 2855 
         {3096'b0,1'b1,2856'b0} : rfm_data_decoded_next = r2856_schedtmg0_freq3; // 2856 
         {3095'b0,1'b1,2857'b0} : rfm_data_decoded_next = r2857_perfhpr1_freq3; // 2857 
         {3094'b0,1'b1,2858'b0} : rfm_data_decoded_next = r2858_perflpr1_freq3; // 2858 
         {3093'b0,1'b1,2859'b0} : rfm_data_decoded_next = r2859_perfwr1_freq3; // 2859 
         {3092'b0,1'b1,2860'b0} : rfm_data_decoded_next = r2860_tmgcfg_freq3; // 2860 
         {3091'b0,1'b1,2861'b0} : rfm_data_decoded_next = r2861_ranktmg0_freq3; // 2861 
         {3090'b0,1'b1,2862'b0} : rfm_data_decoded_next = r2862_ranktmg1_freq3; // 2862 
         {3089'b0,1'b1,2863'b0} : rfm_data_decoded_next = r2863_pwrtmg_freq3; // 2863 
         {3083'b0,1'b1,2869'b0} : rfm_data_decoded_next = r2869_ddr4pprtmg0_freq3; // 2869 
         {3082'b0,1'b1,2870'b0} : rfm_data_decoded_next = r2870_ddr4pprtmg1_freq3; // 2870 
         {3081'b0,1'b1,2871'b0} : rfm_data_decoded_next = r2871_lnkeccctl0_freq3; // 2871 

        default : rfm_data_decoded_next = rfm_data_decoded;
      endcase 
   end  

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
   property apb_onehotsel_legal;
      @(posedge pclk) disable iff(!presetn)
      $onehot0(onehotsel);
   endproperty : apb_onehotsel_legal
   a_apb_onehotsel_legal :  assert property (apb_onehotsel_legal) else 
     $display("%0t ERROR: register selector is one hot.",$realtime);
     
`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

   always @(posedge pclk or negedge presetn) begin : sample_pclk_rdata_PROC
      if (~presetn) begin
         rfm_data_decoded <= {($bits(rfm_data_decoded)){1'b0}};
      end else begin
        if(apb_slv_ns==ADDRDECODE && (~pwrite)) begin
            rfm_data_decoded <=  rfm_data_decoded_next;
         end else if (apb_slv_ns==SAMPLERDY && (~pwrite) && invalid_access) begin
            rfm_data_decoded <=  REG_WIDTH'(0);
         end
      end
   end

   assign prdata[APB_DW-1:0] = rfm_data_decoded[REG_WIDTH-1:0];
    
   // pslverr set whein sync with pready, asserted when 
   // [1] address out of range in sync with pready
   // [2] NS read access to Trustzone register  
   always @ (posedge pclk or negedge presetn) begin : sample_pclk_err_PROC
      if (~presetn) begin
         invalid_access <= 1'b0;
         pslverr   <= 1'b0;
      end else begin
         if(apb_slv_ns==IDLE) begin
            invalid_access <= 1'b0;
         end else if(apb_slv_ns==ADDRDECODE) begin
            if(~(|onehotsel)) begin
               invalid_access <= 1'b1;
            end
         end         
         pslverr <= (invalid_access && apb_slv_ns==SAMPLERDY) ? 1'b1 : 1'b0;
      end 
   end

endmodule
