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
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


#include "dwc_ddrctl_cinit_kconfig_headers.h"
#include "dwc_ddrctl_cinit_SPD.h"
#include "dwc_ddrctl_cinit_spd_struct.h"

#include "dwc_ddrctl_cinit_set_kconfig_spd_jedec.h"

#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)

static void dwc_ddrctl_cinit_set_kconfig_ddr5_cas_latency_supported(void)
{
    SPD_aux.DDR5.cas_latency_supported = 0;
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_20
    SPD_aux.DDR5.cas_latency_supported |= (1 << 0);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_20 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_22
    SPD_aux.DDR5.cas_latency_supported |= (1 << 1);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_22 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_24
    SPD_aux.DDR5.cas_latency_supported |= (1 << 2);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_24 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_26
    SPD_aux.DDR5.cas_latency_supported |= (1 << 3);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_26 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_28
    SPD_aux.DDR5.cas_latency_supported |= (1 << 4);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_28 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_30
    SPD_aux.DDR5.cas_latency_supported |= (1 << 5);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_30 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_32
    SPD_aux.DDR5.cas_latency_supported |= (1 << 6);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_32 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_34
    SPD_aux.DDR5.cas_latency_supported |= (1 << 7);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_34 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_36
    SPD_aux.DDR5.cas_latency_supported |= (1 << 8);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_36 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_38
    SPD_aux.DDR5.cas_latency_supported |= (1 << 9);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_38 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_40
    SPD_aux.DDR5.cas_latency_supported |= (1 << 10);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_40 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_42
    SPD_aux.DDR5.cas_latency_supported |= (1 << 11);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_42 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_44
    SPD_aux.DDR5.cas_latency_supported |= (1 << 12);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_44 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_46
    SPD_aux.DDR5.cas_latency_supported |= (1 << 13);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_46 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_48
    SPD_aux.DDR5.cas_latency_supported |= (1 << 14);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_48 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_50
    SPD_aux.DDR5.cas_latency_supported |= (1 << 15);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_50 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_52
    SPD_aux.DDR5.cas_latency_supported |= (1 << 16);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_52 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_54
    SPD_aux.DDR5.cas_latency_supported |= (1 << 17);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_54 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_56
    SPD_aux.DDR5.cas_latency_supported |= (1 << 18);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_56 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_58
    SPD_aux.DDR5.cas_latency_supported |= (1 << 19);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_58 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_60
    SPD_aux.DDR5.cas_latency_supported |= (1 << 20);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_60 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_62
    SPD_aux.DDR5.cas_latency_supported |= (1 << 21);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_62 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_64
    SPD_aux.DDR5.cas_latency_supported |= (1 << 22);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_64 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_66
    SPD_aux.DDR5.cas_latency_supported |= (1 << 23);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_66 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_68
    SPD_aux.DDR5.cas_latency_supported |= (1 << 24);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_68 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_70
    SPD_aux.DDR5.cas_latency_supported |= (1 << 25);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_70 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_72
    SPD_aux.DDR5.cas_latency_supported |= (1 << 26);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_72 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_74
    SPD_aux.DDR5.cas_latency_supported |= (1 << 27);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_74 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_76
    SPD_aux.DDR5.cas_latency_supported |= (1 << 28);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_76 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_78
    SPD_aux.DDR5.cas_latency_supported |= (1 << 29);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_78 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_80
    SPD_aux.DDR5.cas_latency_supported |= (1 << 30);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_80 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_82
    SPD_aux.DDR5.cas_latency_supported |= (1 << 31);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_82 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_84
    SPD_aux.DDR5.cas_latency_supported |= (1 << 32);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_84 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_86
    SPD_aux.DDR5.cas_latency_supported |= (1 << 33);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_86 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_88
    SPD_aux.DDR5.cas_latency_supported |= (1 << 34);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_88 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_90
    SPD_aux.DDR5.cas_latency_supported |= (1 << 35);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_90 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_92
    SPD_aux.DDR5.cas_latency_supported |= (1 << 36);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_92 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_94
    SPD_aux.DDR5.cas_latency_supported |= (1 << 37);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_94 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_96
    SPD_aux.DDR5.cas_latency_supported |= (1 << 38);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_96 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_98
    SPD_aux.DDR5.cas_latency_supported |= (1 << 39);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_CAS_LATENCY_SUPPORT_RANGE_CL_98 */

    SNPS_LOG("CAS latency supported 0x%lx", SPD_aux.DDR5.cas_latency_supported);
}
#endif // defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)


/**
 * @brief Function to set the memory module configuration based on the direct user input
 * 
 */
void cinit_kconfig_mem_expert_ddr5_cfg(void)
{
#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)
    SPD_aux.DDR5.tRCmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRC_MIN;
    SNPS_LOG("SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) is %u ps", SPD_aux.DDR5.tRCmin_ps);
    SPD_aux.DDR5.tCKAVGmin = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TCK_MIN;
    SNPS_LOG("SDRAM Minimum Cycle Time (tCKAVGmin) is %u ps", SPD_aux.DDR5.tCKAVGmin);
    SPD_aux.DDR5.tCKAVGmax = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TCK_MAX;
    SNPS_LOG("SDRAM Maximum Cycle Time (tCKAVGmax) is %u ps", SPD_aux.DDR5.tCKAVGmax);
    SPD_aux.DDR5.tAAmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TAA_MIN;
    SNPS_LOG("SDRAM Minimum CAS Latency Time (tAAmin) is %u ps", SPD_aux.DDR5.tAAmin_ps);
    SPD_aux.DDR5.tWRmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TWR_MIN;
    SNPS_LOG("SDRAM Minimum Write Recovery Time (tWRmin) is %u ps", SPD_aux.DDR5.tWRmin_ps);
    SPD_aux.DDR5.tRASmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRAS_MIN;
    SNPS_LOG("SDRAM Minimum Active to Precharge Delay Time (tRASmin) is %u ps", SPD_aux.DDR5.tRASmin_ps);
    SPD_aux.DDR5.tRCDmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRCD_MIN;
    SNPS_LOG("SDRAM Minimum RAS to CAS Delay Time (tRCDmin) is %u ps", SPD_aux.DDR5.tRCDmin_ps);
    SPD_aux.DDR5.tRPmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRP_MIN;
    SNPS_LOG("SDRAM Minimum Row Precharge Delay Time (tRPmin) is %u ps", SPD_aux.DDR5.tRPmin_ps);
    SPD_aux.DDR5.tRFC1_slr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFC1_SLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) is %u ns", SPD_aux.DDR5.tRFC1_slr_min_ns);
    SPD_aux.DDR5.tRFC2_slr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFC2_SLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) is %u ns", SPD_aux.DDR5.tRFC2_slr_min_ns);
    SPD_aux.DDR5.tRFCsb_slr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFCSB_SLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min) is %u ns", SPD_aux.DDR5.tRFCsb_slr_min_ns);
    SPD_aux.DDR5.tRFC1_dlr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFC1_DLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) is %u ns", SPD_aux.DDR5.tRFC1_dlr_min_ns);
    SPD_aux.DDR5.tRFC2_dlr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFC2_DLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC2_dlr min) is %u ns", SPD_aux.DDR5.tRFC2_dlr_min_ns);
    SPD_aux.DDR5.tRFCsb_dlr_min_ns = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR5_TRFCSB_DLR_MIN;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) is %u ns", SPD_aux.DDR5.tRFCsb_dlr_min_ns);

    dwc_ddrctl_cinit_set_kconfig_ddr5_cas_latency_supported();

#endif // defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR5)
}


/**
 * @brief Function to set the memory module configuration based on the direct user input
 * 
 */
void cinit_kconfig_mem_expert_ddr4_cfg(void)
{
#if defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4)
    SPD_aux.DDR4.cas_latency_supported = 0;
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_7
    SPD_aux.DDR4.cas_latency_supported |= (1 << 7);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_7 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_8
    SPD_aux.DDR4.cas_latency_supported |= (1 << 8);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_8 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_9
    SPD_aux.DDR4.cas_latency_supported |= (1 << 9);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_9 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_10
    SPD_aux.DDR4.cas_latency_supported |= (1 << 10);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_10 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_11
    SPD_aux.DDR4.cas_latency_supported |= (1 << 11);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_11 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_12
    SPD_aux.DDR4.cas_latency_supported |= (1 << 12);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_12 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_13
    SPD_aux.DDR4.cas_latency_supported |= (1 << 13);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_13 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_14
    SPD_aux.DDR4.cas_latency_supported |= (1 << 14);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_14 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_15
    SPD_aux.DDR4.cas_latency_supported |= (1 << 15);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_15 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_16
    SPD_aux.DDR4.cas_latency_supported |= (1 << 16);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_16 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_17
    SPD_aux.DDR4.cas_latency_supported |= (1 << 17);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_17 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_18
    SPD_aux.DDR4.cas_latency_supported |= (1 << 18);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_18 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_19
    SPD_aux.DDR4.cas_latency_supported |= (1 << 19);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_19 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_20
    SPD_aux.DDR4.cas_latency_supported |= (1 << 20);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_20 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_21
    SPD_aux.DDR4.cas_latency_supported |= (1 << 21);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_21 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_22
    SPD_aux.DDR4.cas_latency_supported |= (1 << 22);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_22 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_23
    SPD_aux.DDR4.cas_latency_supported |= (1 << 23);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_23 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_24
    SPD_aux.DDR4.cas_latency_supported |= (1 << 24);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_24 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_25
    SPD_aux.DDR4.cas_latency_supported |= (1 << 25);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_25 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_26
    SPD_aux.DDR4.cas_latency_supported |= (1 << 26);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_26 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_27
    SPD_aux.DDR4.cas_latency_supported |= (1 << 27);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_27 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_28
    SPD_aux.DDR4.cas_latency_supported |= (1 << 28);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_28 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_29
    SPD_aux.DDR4.cas_latency_supported |= (1 << 29);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_29 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_30
    SPD_aux.DDR4.cas_latency_supported |= (1 << 30);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_30 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_31
    SPD_aux.DDR4.cas_latency_supported |= (1 << 31);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_31 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_32
    SPD_aux.DDR4.cas_latency_supported |= (1 << 32);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_32 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_33
    SPD_aux.DDR4.cas_latency_supported |= (1 << 33);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_33 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_34
    SPD_aux.DDR4.cas_latency_supported |= (1 << 34);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_34 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_35
    SPD_aux.DDR4.cas_latency_supported |= (1 << 35);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_35 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_36
    SPD_aux.DDR4.cas_latency_supported |= (1 << 36);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_36 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_37
    SPD_aux.DDR4.cas_latency_supported |= (1 << 37);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_37 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_38
    SPD_aux.DDR4.cas_latency_supported |= (1 << 38);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_38 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_39
    SPD_aux.DDR4.cas_latency_supported |= (1 << 39);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_39 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_40
    SPD_aux.DDR4.cas_latency_supported |= (1 << 40);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_40 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_41
    SPD_aux.DDR4.cas_latency_supported |= (1 << 41);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_41 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_42
    SPD_aux.DDR4.cas_latency_supported |= (1 << 42);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_42 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_43
    SPD_aux.DDR4.cas_latency_supported |= (1 << 43);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_43 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_44
    SPD_aux.DDR4.cas_latency_supported |= (1 << 44);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_44 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_45
    SPD_aux.DDR4.cas_latency_supported |= (1 << 45);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_45 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_46
    SPD_aux.DDR4.cas_latency_supported |= (1 << 46);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_46 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_47
    SPD_aux.DDR4.cas_latency_supported |= (1 << 47);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_47 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_48
    SPD_aux.DDR4.cas_latency_supported |= (1 << 48);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_48 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_49
    SPD_aux.DDR4.cas_latency_supported |= (1 << 49);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_49 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_50
    SPD_aux.DDR4.cas_latency_supported |= (1 << 50);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_50 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_51
    SPD_aux.DDR4.cas_latency_supported |= (1 << 51);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_51 */
#ifdef DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_52
    SPD_aux.DDR4.cas_latency_supported |= (1 << 52);
#endif /* DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_CAS_LATENCY_SUPPORT_RANGE_CL_52 */

    SNPS_LOG("CAS latencies supported are 0x%.16x", SPD_aux.DDR4.cas_latency_supported);

    SPD_aux.DDR4.tCKAVGmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TCK_MIN;
    SNPS_LOG("SDRAM Minimum Cycle Time (tCKAVGmin) %u", SPD_aux.DDR4.tCKAVGmin_ps);

    SPD_aux.DDR4.tCKAVGmax_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TCK_MAX;
    SNPS_LOG("SDRAM Maximum Cycle Time (tCKAVGmax) %u", SPD_aux.DDR4.tCKAVGmax_ps);

    SPD_aux.DDR4.tAAmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TAA_MIN;
    SNPS_LOG("Minimum CAS Latency Time %u", SPD_aux.DDR4.tAAmin_ps);

    SPD_aux.DDR4.tRCDmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRCD_MIN;
    SNPS_LOG("Minimum RAS to CAS Delay Time %u", SPD_aux.DDR4.tRCDmin_ps);

    SPD_aux.DDR4.tRPmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRP_MIN;
    SNPS_LOG("Minimum Row Precharge Delay Time (tRPmin) %u", SPD_aux.DDR4.tRPmin_ps);

    SPD_aux.DDR4.tRASmin_ps =  DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRAS_MIN;
    SNPS_LOG("Minimum Active to Precharge Delay Time (tRASmin) = %u", SPD_aux.DDR4.tRASmin_ps);

    SPD_aux.DDR4.tRCmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRC_MIN;
    SNPS_LOG("Minimum Active to Active/Refresh Delay Time (tRCmin) %u", SPD_aux.DDR4.tRCmin_ps);

    SPD_aux.DDR4.tRFC1min_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRFC1_MIN;
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC1min) %u", SPD_aux.DDR4.tRFC1min_ps);

    SPD_aux.DDR4.tRFC2min_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRFC2_MIN;
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC2min) %u", SPD_aux.DDR4.tRFC2min_ps);

    SPD_aux.DDR4.tRFC4min_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRFC4_MIN;
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC4min) %u", SPD_aux.DDR4.tRFC4min_ps);

    SPD_aux.DDR4.tFAWmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TFAW_MIN;
    SNPS_LOG("Minimum Four Activate Window Delay Time (tFAWmin) %u", SPD_aux.DDR4.tFAWmin_ps);

    SPD_aux.DDR4.tRRD_Smin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRRD_S_MIN;
    SNPS_LOG("Minimum Activate to Activate Delay Time (tRRD_Smin), Different Bank Group %u", SPD_aux.DDR4.tRRD_Smin_ps);

    SPD_aux.DDR4.tRRD_Lmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TRRD_L_MIN;
    SNPS_LOG("Minimum Activate to Activate Delay Time (tRRD_Lmin), Same Bank Group %u", SPD_aux.DDR4.tRRD_Lmin_ps);

    SPD_aux.DDR4.tWRmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TWR_MIN;
    SNPS_LOG("tWRmin_ps = %u", SPD_aux.DDR4.tWRmin_ps);

    SPD_aux.DDR4.tWTR_Smin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TWTR_S_MIN;
    SNPS_LOG("tWTR_Smin_ps = %u", SPD_aux.DDR4.tWTR_Smin_ps);

    SPD_aux.DDR4.tWTR_Lmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TWTR_L_MIN;
    SNPS_LOG("tWTR_Lmin_ps = %u", SPD_aux.DDR4.tWTR_Lmin_ps);

    SPD_aux.DDR4.tCCD_Lmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TCCD_L_MIN;
    SNPS_LOG("Minimum CAS to CAS Delay Time (tCCD_Lmin), Same Bank Group %u", SPD_aux.DDR4.tCCD_Lmin_ps);

    SPD_aux.DDR4.tFAWmin_ps = DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC_DDR4_TFAW_MIN;
    SNPS_LOG("Minimum Four Activate Window Delay Time (tFAWmin) %u", SPD_aux.DDR4.tFAWmin_ps);
#endif // defined(DWC_DDRCTL_CINIT_SPD_STATIC_JEDEC) && defined(DWC_DDRCTL_CINIT_SDRAM_PROTOCOL_DDR4)
}
