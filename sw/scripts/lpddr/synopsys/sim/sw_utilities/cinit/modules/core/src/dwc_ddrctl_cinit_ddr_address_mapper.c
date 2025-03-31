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


#include "dwc_ddrctl_cinit.h"

/** @brief method to supply a default/fixed address map if none is provided.
 * This is only used in CPU_DPI mode.
 * @param am address map number (0 or 1)
 * @note This method is based on original umctl2 SW library.
 * @note hif[2:0]=3'b000 always
 * @ingroup SwSeqCommonGrp
 */
void dwc_ddrctl_cinit_ddr_address_mapper(uint32_t am)
{
    SNPS_TRACE("Enter");
    uint32_t hif_addr = 3;
    uint32_t first_row_bit;
    uint32_t first_cs_bit;
#ifdef UMCTL2_CID_EN
    uint32_t first_cid_bit;
#endif
    uint32_t first_bg_bit;
    uint32_t first_bank_bit;
    uint32_t total_address_bits;
    uint32_t sdram_capacity_mbits_sel;
    
    bool inline_ecc;

    if ((IS_LPDDR4 || IS_LPDDR5) && STATIC.ecc_mode == 4)
        inline_ecc = true;
    else
        inline_ecc = false;

    if (CFG->spdData_m.address_mode[am]==ADDRESS_MODE_REGISTER_FIELD){
        SNPS_LOG("Default address map configured using references to register fields by user.");
        return;
    }

    //c3-c9
    STATIC.addrmap_col_b3[am] = 0;
    hif_addr++;
    STATIC.addrmap_col_b4[am] = 0;
    hif_addr++;
    STATIC.addrmap_col_b5[am] = 0;
    hif_addr++;
    STATIC.addrmap_col_b6[am] = 0;
    hif_addr++;
    if (!inline_ecc) {
        SNPS_LOG("inline_ecc is false ", NULL);
        STATIC.addrmap_col_b7[am] = 0;
        hif_addr++;
        STATIC.addrmap_col_b8[am] = 0;
        hif_addr++;
        STATIC.addrmap_col_b9[am] = 0;
        hif_addr++;
        if (DRAM_CAW(am) > 10) {
            STATIC.addrmap_col_b10[am] = 0;
            hif_addr++;
        } else {
            STATIC.addrmap_col_b10[am] = 31;// unused
        }
    }
    first_bg_bit = hif_addr - 3; // internal base 3
    SNPS_LOG("DRAM_BGW(%d) = %u", am, DRAM_BGW(am));
    SNPS_LOG("DRAM_BAW(%d) = %u", am, DRAM_BAW(am));
    SNPS_LOG("DRAM_RAW(%d) = %u", am, DRAM_RAW(am));
    SNPS_LOG("DRAM_CAW(%d) = %u", am, DRAM_CAW(am));
#ifdef UMCTL2_CID_EN
    SNPS_LOG("CID_WIDTH(%d) = %u", am, CID_WIDTH(am));
#endif

    SNPS_LOG("first_bg_bit = %u", first_bg_bit);
    if (DRAM_BGW(am) > 0) {
        STATIC.addrmap_bg_b0[am] = first_bg_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bg_b0[am] = 63;// unused
    }
    if (DRAM_BGW(am) > 1) {
        STATIC.addrmap_bg_b1[am] = first_bg_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bg_b1[am] = 63;// unused
    }

    //bg2 for DDR5 only
    if (DRAM_BGW(am) > 2) {
        STATIC.addrmap_bg_b2[am] = first_bg_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bg_b2[am] = 63;// unused
    }

    first_bank_bit = hif_addr - 3; // internal base 3
    SNPS_LOG("first_bank_bit  = %u", first_bank_bit);
    //b0
    if (DRAM_BAW(am) > 0) {
        STATIC.addrmap_bank_b0[am] = first_bank_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bank_b0[am] = 63;
    }

    //b1
    if (DRAM_BAW(am) > 1) {
        STATIC.addrmap_bank_b1[am] = first_bank_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bank_b1[am] = 63;
    }
    //b2 LPDDR4/5 only
#ifdef DDRCTL_LPDDR
    if (DRAM_BAW(am) > 2) {
        STATIC.addrmap_bank_b2[am] = first_bank_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_bank_b2[am] = 63;
    }
#else
    STATIC.addrmap_bank_b2[am] = 63;
#endif // DDRCTL_LPDDR

    first_row_bit = hif_addr - 6; // internal base 6
    SNPS_LOG("first_row_bit = %u", first_row_bit);
    //r0-r11
    STATIC.addrmap_row_b0[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b1[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b2[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b3[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b4[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b5[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b6[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b7[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b8[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b9[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b10[am] = first_row_bit;
    hif_addr++;
    STATIC.addrmap_row_b11[am] = first_row_bit;
    hif_addr++;
    //r12
    if (DRAM_RAW(am) > 12) {
        STATIC.addrmap_row_b12[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b12[am] = first_row_bit;
    }

    //r13
    if (DRAM_RAW(am) > 13) {
        STATIC.addrmap_row_b13[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b13[am] = first_row_bit;
    }

    //r14
    if (DRAM_RAW(am) > 14) {
        STATIC.addrmap_row_b14[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b14[am] = 31;
    }

    //r15
    if (DRAM_RAW(am) > 15) {
        STATIC.addrmap_row_b15[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b15[am] = 31;
    }

    //r16
    if (DRAM_RAW(am) > 16) {
        STATIC.addrmap_row_b16[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b16[am] = 31;
    }

    //r17
    if (DRAM_RAW(am) > 17) {
        STATIC.addrmap_row_b17[am] = first_row_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_row_b17[am] = 31;
    }

    first_cs_bit = hif_addr - 6; // internal base 6
    SNPS_LOG("first_cs_bit = %u", first_cs_bit);
    //cs0 next
    if (SPD.num_ranks > 1) {
        STATIC.addrmap_cs_bit0[am] = first_cs_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cs_bit0[am] = 63;
    }

    //cs1 next
    if (SPD.num_ranks > 3) {
        STATIC.addrmap_cs_bit1[am] = first_cs_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cs_bit1[am] = 63;
    }
    //cs2 next
    if (SPD.num_ranks > 4) {
        STATIC.addrmap_cs_bit2[am] = first_cs_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cs_bit2[am] = 63;
    }

#ifdef UMCTL2_CID_EN
    first_cid_bit = hif_addr - 4; // internal base 4
    //cid0 next
    if (CID_WIDTH(am) > 0) {
        STATIC.addrmap_cid_b0[am] = first_cid_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cid_b0[am] = 63;
    }

    //cid1 next
    if (CID_WIDTH(am) > 1) {
        STATIC.addrmap_cid_b1[am] = first_cid_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cid_b1[am] = 63;
    }
    //cid2 next
    if (CID_WIDTH(am) > 2) {
        STATIC.addrmap_cid_b2[am] = first_cid_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cid_b2[am] = 63;
    }
    //cid3
    if (CID_WIDTH(am) > 3) {
        STATIC.addrmap_cid_b3[am] = first_cid_bit;
        hif_addr++;
    } else {
        STATIC.addrmap_cid_b3[am] = 63;
    }
#else
    STATIC.addrmap_cid_b0[am] = 63;
    STATIC.addrmap_cid_b1[am] = 63;
    STATIC.addrmap_cid_b2[am] = 63;
    STATIC.addrmap_cid_b3[am] = 63;
#endif // UMCTL2_CID_EN
#ifdef UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1
    if (IS_DDR4)
        STATIC.addrmap_dch_bit0 = 63;
    else
        STATIC.addrmap_dch_bit0 = hif_addr - 3; // internal base 3
#else
        STATIC.addrmap_dch_bit0 = 63;
#endif // UMCTL2_DATA_CHANNEL_INTERLEAVE_EN_1

    if (inline_ecc) {
        // if inline ecc is enabled then the highest 3 columns bits
        // must map to the highest hif address bits
        uint32_t high_col_bits;

        high_col_bits = hif_addr - 7;
        SNPS_LOG("inline_ecc is true high_col_bits=%u", high_col_bits);
        STATIC.addrmap_col_b7[am] = high_col_bits;
        hif_addr++;
        STATIC.addrmap_col_b8[am] = high_col_bits;
        hif_addr++;
        STATIC.addrmap_col_b9[am] = high_col_bits;
        hif_addr++;
        if (DRAM_CAW(am) > 10) {
            STATIC.addrmap_col_b10[am] = high_col_bits;
            hif_addr++;
        } else {
            STATIC.addrmap_col_b10[am] = 31;// unused
        }
    }

#ifdef THEREIS_SAR
#if UMCTL2_A_NSAR > 0
    // Simplest SAR implementation possible
    // The base addresses must be specified such that they are in the ascending order
    // (SARBASE0 < SARBASE1 < SARBASE2 < SARBASE3) and such that regions do not overlap
    STATIC.nblocks[0] = 1;
    STATIC.base_addr[0] = 0;
    for(uint32_t ii = 1; ii < UMCTL2_A_NSAR; ii++) {
        STATIC.nblocks[ii] = 1;
        STATIC.base_addr[ii] = STATIC.base_addr[ii-1] + STATIC.nblocks[ii-1]+1;
    }
#endif // UMCTL2_A_NSAR > 0
#endif // THEREIS_SAR

#ifdef DDRCTL_LPDDR_MIXED_PKG
    sdram_capacity_mbits_sel = (STATIC.lpddr_mixed_pkg_en) ? SPD.sdram_capacity_mbits_lp45_mp[0] : SPD.sdram_capacity_mbits[0];
#else
    sdram_capacity_mbits_sel = SPD.sdram_capacity_mbits[0];
#endif /* DDRCTL_LPDDR_MIXED_PKG */

    // debug print only
    uint32_t num_ranks=0, num_lranks=0;
    switch (STATIC.active_ranks) {
        case 0:
	    num_ranks=0;
	    break;
        case 1:
	    num_ranks=1;
	    break;
        case 3:
	    num_ranks=2;
	    break;
	case 15:
	    num_ranks=4;
	    break;
    }

    switch (STATIC.active_logical_ranks) {
        case 0:
	    num_lranks=0;
	    break;
        case 1:
	    num_lranks=2;
	    break;
        case 2:
	    num_lranks=4;
	    break;
        case 3:
	    num_lranks=8;
	    break;
    }

    SPD.total_address_bits = DRAM_RAW(am) + DRAM_BAW(am) + DRAM_BGW(am) + DRAM_CAW(am) + (uint64_t) log2(num_ranks) + (uint64_t) log2(num_lranks);
    SNPS_LOG("hif_addr = %u, SPD.total_address_bits = %u", hif_addr, SPD.total_address_bits);

    /// - Take care of Non-binary memories
    if (IS_LPDDR5 && (sdram_capacity_mbits_sel == 3072)) {
	    if (SPD.sdram_width_bits[0] == 8)
		    STATIC.nonbinary_device_density = 2; // row[14:13]
	    else
		    STATIC.nonbinary_device_density = 1; // row[13:12]
    }
    else if ((IS_LPDDR5 && sdram_capacity_mbits_sel == 6144) ||
	     (IS_LPDDR4 && sdram_capacity_mbits_sel == 3072)) {
	    if (SPD.sdram_width_bits[0] == 8)
		    STATIC.nonbinary_device_density = 3; // row[15:14]
	    else
		    STATIC.nonbinary_device_density = 2; // row[14:13]
    }
    else if ((IS_LPDDR5 && sdram_capacity_mbits_sel == 12288) ||
	     (IS_LPDDR4 && sdram_capacity_mbits_sel == 6144)) {
	    if (SPD.sdram_width_bits[0] == 8)
		    STATIC.nonbinary_device_density = 4; // row[16:15]
	    else
		    STATIC.nonbinary_device_density = 3; // row[15:14]
    }
    else if ((IS_LPDDR5 && sdram_capacity_mbits_sel == 24576) ||
	     (IS_LPDDR4 && sdram_capacity_mbits_sel == 12288)) {
	    if (SPD.sdram_width_bits[0] == 8)
		    STATIC.nonbinary_device_density = 5; // row[17:16]
	    else
		    STATIC.nonbinary_device_density = 4; // row[16:15]
    }
    else if (IS_DDR5 && SPD.sdram_capacity_mbits[0] == 24576) {
	    STATIC.nonbinary_device_density = 4; // row[16:15]
    }
    SNPS_LOG("nonbinary_device_density = %u", STATIC.nonbinary_device_density);
    SNPS_TRACE("Leaving");
}

