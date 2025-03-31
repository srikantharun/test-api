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


#include "dwc_ddrctl_cinit_SPD.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_util.h"
#include "jedec/cinit_ddr_speedbins.h"

SPD_DDR_t SPD_ddr;
SPD_aux_t SPD_aux;

#ifdef DDRCTL_DDR

#ifdef DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC

SPD_DDR4_t *pSPD4;
SPD_DDR5_t *pSPD5;

/**
 * @brief Function to calculate CRC on SPD "count" size.
 */
static inline uint16_t spd_calc_crc16(uint8_t *ptr, uint16_t count)
{
    uint16_t crc, i;

    crc = 0;
    count -= 2; // Remove crc value

    while (count-- > 0) {
        crc = crc ^ ((uint16_t)*ptr++ << 8);
        for (i = 0; i < 8; ++i) {
            if (crc & 0x8000)
                crc = (crc << 1) ^ 0x1021;
            else
                crc = crc << 1;
        }
    }
    return (crc & 0xFFFF);
}

/**
 * @brief Function to get CRC value from SPD at position count.
 */
static inline uint16_t spd_read_crc16(uint8_t *ptr, uint16_t count)
{
    uint16_t crc;

    crc = ptr[count - 1];
    crc <<= 8;
    crc |= ptr[count - 2];

    return crc;
}

/**
 * @brief Function to compare calculated crc against read CRC.
 */
static inline bool dwc_ddrctl_cinit_verify_crc(uint8_t * spd_data, uint16_t start_addr, uint16_t size)
{
    bool rslt;
    uint16_t calc_crc;
    uint16_t read_crc;

    read_crc = spd_read_crc16(&(spd_data[start_addr]), size);
    calc_crc = spd_calc_crc16(&(spd_data[start_addr]), size);

    rslt = read_crc == calc_crc;

    SNPS_LOG("CRC check: start %u size %lu => CRC16 = 0x%.8x, 0x%.8x, %s",
             start_addr, size, calc_crc, read_crc, (rslt == true) ? "PASS" : "FAIL");

    return rslt;
}

/**
 * @brief Function to verify all CRC in the range of SPD used bytes.
 */
static inline bool dwc_ddrctl_cinit_SPD_CRC(uint8_t * spd_data, uint16_t size)
{
    SNPS_TRACE("Entering");
    SNPS_LOG("size = %u", size);
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        switch (size) {
        case 128:
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 0, 128))
                return false;
            break;
        case 256:
        case 384:
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 0, 128))
                return false;
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 128, 128))
                return false;
            SNPS_LOG("Ended CRC", NULL);
            break;
        case 512:
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 0, 128))
                return false;
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 128, 128))
                return false;
            if (!dwc_ddrctl_cinit_verify_crc(spd_data, 0, 512))
                return false;
            break;
        default:
            SNPS_ERROR("Invalid option -  SPD used bytes", NULL);
            return false;
        }
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        if (!dwc_ddrctl_cinit_verify_crc(spd_data, 0, 512))
            return false;
    }
#endif  /* CINIT_DDR5 */
    SNPS_TRACE("Leaving");
    return true;
}

/*************** DDR4 Functions ****************************/

#endif /* DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC */

/**
 * @brief Decode CAS latency high and low range into a simple bitfield
 */
uint64_t decode_spd_cas_latency_ddr4(uint32_t encoded_cas_latencies_supported)
{
    uint64_t cas_latencies_supported;
    // Decoding the CAS latency block based on specification:
    // SPD Annex L, Serial Presence Detect (SPD) for DDR4 SDRAM Modules, Release 4 section 8.1.21

    // get data only
    cas_latencies_supported = encoded_cas_latencies_supported & 0x7FFFFFFF;

    // bit 31 is the range selection high/low
    // shift values based on high/low range bit
    if ((encoded_cas_latencies_supported >> 31) == 1){
        cas_latencies_supported = cas_latencies_supported << 23;
    } else {
        cas_latencies_supported = cas_latencies_supported << 7;
    }

    return cas_latencies_supported;
}

#if DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC

/**
 * @brief Function to read the DDR4 sdram_capacity.
 * read Bank groups bits and Bank address bits in DDR4
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_B4(void)
{
    SNPS_TRACE("Entering");

    // SDRAM capacity
    switch (pSPD4->sdram_density_banks & 0x0F) {
    case 0:
        SPD_aux.sdram_capacity_mbits[0] = 256;        // 256 Mb
        break;
    case 1:
        SPD_aux.sdram_capacity_mbits[0] = 512;        // 512 Mb
        break;
    case 2:
        SPD_aux.sdram_capacity_mbits[0] = 1024;        // 1 Gb
        break;
    case 3:
        SPD_aux.sdram_capacity_mbits[0] = 2048;        // 2 Gb
        break;
    case 4:
        SPD_aux.sdram_capacity_mbits[0] = 4096;        // 4 Gb
        break;
    case 5:
        SPD_aux.sdram_capacity_mbits[0] = 8192;        // 8 Gb
        break;
    case 6:
        SPD_aux.sdram_capacity_mbits[0] = 16384;    // 16 Gb
        break;
    case 7:
        SPD_aux.sdram_capacity_mbits[0] = 32768;    // 32 Gb
        break;
    case 8:
        SPD_aux.sdram_capacity_mbits[0] = 12288;    // 12 Gb
        break;
    case 9:
        SPD_aux.sdram_capacity_mbits[0] = 24576;    // 24 Gb
        break;
    default:
        SNPS_ERROR("Invalid option - Total SDRAM capacity per DIMM", NULL);
        return false;
    }
    SNPS_LOG("SPD.sdram_capacity_mbits[0] = %u", SPD_aux.sdram_capacity_mbits[0]);

    // Bank groups bits
    switch ((pSPD4->sdram_density_banks >> 6) & 0x3) {
    case 0:
        SPD_aux.dram_bgw[0] = 0;            // No bank groups bits
        break;
    case 1:
        SPD_aux.dram_bgw[0] = 1;            // 2 bank groups bits
        break;
    case 2:
        SPD_aux.dram_bgw[0] = 2;            // 4 bank groups bits
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM bank group bits", NULL);
        return false;
    }
    SNPS_LOG("SDRAM bank group bits %u", SPD_aux.dram_bgw[0] * 2);

    // Bank address bits
    switch ((pSPD4->sdram_density_banks >> 4) & 0x3) {
    case 0:
        SPD_aux.dram_baw[0] = 2;            // 4 banks address bits
        SNPS_LOG("SPD.dram_baw[0] = %u / 4 banks", SPD_aux.dram_baw[0]);
        break;
    case 1:
        SPD_aux.dram_baw[0] = 3;            // 8 banks address bits
        SNPS_LOG("SPD.dram_baw[0] = %u / 8 banks", SPD_aux.dram_baw[0]);
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM bank address bits", NULL);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief Function to read the DDR4 Column address bits.
 * read DDR4 Row address bits.
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_B5(void)
{
    SNPS_TRACE("Entering");
    // SDRAM column address bits
    switch (pSPD4->sdram_addressing & 0x07) {
    case 0:
        SPD_aux.dram_caw[0] = 9;    // 9 columns address bits
        break;
    case 1:
        SPD_aux.dram_caw[0] = 10;    // 10 columns address bits
        break;
    case 2:
        SPD_aux.dram_caw[0] = 11;    // 11 columns address bits
        break;
    case 3:
        SPD_aux.dram_caw[0] = 12;    // 12 columns address bits
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM column address bits", NULL);
        return false;
    }
    SNPS_LOG("%u columns address bits", SPD_aux.dram_caw[0]);

    // SDRAM row address bits
    switch ((pSPD4->sdram_addressing >> 3) & 0x07) {
    case 0:
        SPD_aux.dram_raw[0] = 12;            // 12 rows address bits
        break;
    case 1:
        SPD_aux.dram_raw[0] = 13;            // 13 rows address bits
        break;
    case 2:
        SPD_aux.dram_raw[0] = 14;            // 14 rows address bits
        break;
    case 3:
        SPD_aux.dram_raw[0] = 15;            // 15 rows address bits
        break;
    case 4:
        SPD_aux.dram_raw[0] = 16;            // 16 rows address bits
        break;
    case 5:
        SPD_aux.dram_raw[0] = 17;            // 17 rows address bits
        break;
    case 6:
        SPD_aux.dram_raw[0] = 18;            // 18 rows address bits
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM row address bits", NULL);
        return false;
    }
    SNPS_LOG("%u rows address bits", SPD_aux.dram_raw[0]);

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * Byte 6 (0x006): Primary SDRAM Package Type
 * @brief Function to read the DDR4 cid_widht
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_B6(void)
{
    SNPS_TRACE("Entering");

    // SDRAM package Type
    switch (pSPD4->primary_sdram_package_type) {
    case 0:
        SPD_aux.cid_width[0] = 0;    // Non-3DS
        SNPS_LOG("NON-3Ds for CID WIDTH %u", SPD_aux.cid_width[0]);
        break;
    case 0x92:
        SPD_aux.cid_width[0] = 1;    // 2H-3DS non-monolithic 2 dies 3DS
        SNPS_LOG("2H-3Ds for CID WIDTH %u", SPD_aux.cid_width[0]);
        break;
    case 0xB2:
        SPD_aux.cid_width[0] = 2;    // 4H-3DS non-monolithic 4 dies 3DS
        SNPS_LOG("4H-3Ds for CID WIDTH %u", SPD_aux.cid_width[0]);
        break;
    default:
        SNPS_ERROR("Invalid option - Die Per Package not supported 0x%x", pSPD4->primary_sdram_package_type);
        return false;
    }

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * Byte 12 (0x00C): Module Organization
 * @brief Function to read the DDR4 SDRAM device width bit
 * read num_ranks_per_dimm
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_B0C(void)
{
    SNPS_TRACE("Entering");

    // SDRAM device width bits
    switch (pSPD4->module_organization & 0x07) {
    case 0:
        SPD_aux.sdram_width_bits[0] = 4;    // 4 bits width
        break;
    case 1:
        SPD_aux.sdram_width_bits[0] = 8;    // 8 bits width
        break;
    case 2:
        SPD_aux.sdram_width_bits[0] = 16;    // 16 bits width
        break;
    case 3:
        SPD_aux.sdram_width_bits[0] = 32;    // 32 bits width
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM device width", NULL);
        return false;
    }
    SNPS_LOG("SDRAM device width %u", SPD_aux.sdram_width_bits[0]);

    switch ((pSPD4->module_organization >> 3) & 0x7) {
    case 0:
    case 1:
    case 3:
    case 7:
        SPD_aux.num_ranks_per_dimm = ((pSPD4->module_organization >> 3) & 0x7) + 1;
        SPD_aux.num_ranks = SPD_aux.num_ranks_per_dimm * SPD.num_dimm;
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM num ranks", NULL);
        return false;
    }
    SNPS_LOG("Num ranks per dimm = %u", SPD_aux.num_ranks_per_dimm);
    SNPS_LOG("Num ranks = %u", SPD_aux.num_ranks);

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * Byte 13 (0x00D): Module Memory Bus Width
 * @brief Function to read the DDR4 Module Memory Bus Width
 * read if ECC is supported
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_B0D(void)
{
    SNPS_TRACE("Entering");
    uint8_t value;

    value = pSPD4->module_memory_bus_width & 0x7;
    switch (value) {
    case 0x0:
        SPD_aux.module_width_bits = 8;
        break;
    case 0x1:
        SPD_aux.module_width_bits = 16;
        break;
    case 0x2:
        SPD_aux.module_width_bits = 32;
        break;
    case 0x3:
        SPD_aux.module_width_bits = 64;
        break;
    default:
        SNPS_ERROR("Unsupported value : spd Byte[13] module_memory_bus_width[2:0]=%d. Supported values are [0:3]\n", value);
        return false;
    }
    SNPS_LOG("Module widht bits %u", SPD_aux.module_width_bits);

    value = (pSPD4->module_memory_bus_width >> 3) & 0x3;
    switch (value) {
    case 0x0:
        SPD_aux.ecc_supported = 0;
        break;
    case 0x1:
        SPD_aux.ecc_supported = 1;
        break;        //8bits ECC
    default:
        SNPS_ERROR("Unsupported value : spd Byte[13] module_memory_bus_width[4:3]=%d, Supported values are [0,1]\n", value);
        return false;
    }
    SNPS_LOG("ECC_supported = %u", SPD_aux.ecc_supported);

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * @brief Read minimum and maximum Cycle Time
 * byte 18 and byte 19
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_timmings_ps(void)
{
#ifdef DDRCTL_DDR
    SNPS_TRACE("Entering");
    uint32_t value;

    //Byte 17 (0x011): Timebases
    value = (pSPD4->timebases >> 2) & 0x3;
    switch (value) {
    case 0x0:
        SPD_aux.mtb_ps = 125;
        break;
    default:
        SNPS_ERROR("Unsupported value : spd Byte[17] timebases[1:0]=%d. Supported values are [0]\n", value);
        return false;
    }

    value = pSPD4->timebases & 0x3;
    switch (value) {
    case 0x0:
        SPD_aux.ftb_ps = 1;
        break;
    default:
        SNPS_ERROR("Unsupported value : spd Byte[17] timebases[3:2]=%d. Supported values are [0]\n", value);
        return false;
    }

    //Byte 18 (0x012): SDRAM Minimum Cycle Time (tCKAVGmin)
    if (pSPD4->tCKAVG_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[18] tCKAVG_min_mtb=%d. Supported range is 1:255", pSPD4->tCKAVG_min_mtb);
        return false;
    }
    SNPS_LOG("tCKAVG_min_mtb = %u", pSPD4->tCKAVG_min_mtb);
    SNPS_LOG("tCKAVG_min_ftb = %d", pSPD4->tCKAVG_min_ftb);

    SPD_aux.DDR4.tCKAVGmin_ps = (pSPD4->tCKAVG_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tCKAVG_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("SDRAM Minimum Cycle Time (tCKAVGmin) %u", SPD_aux.DDR4.tCKAVGmin_ps);

    //Byte 19 (0x013): SDRAM Maximum Cycle Time (tCKAVGmax)
    if (pSPD4->tCKAVG_max_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[19] tCKAVG_max_mtb=%u. Supported range is 1:255", pSPD4->tCKAVG_max_mtb);
        return false;
    }
    SPD_aux.DDR4.tCKAVGmax_ps = (pSPD4->tCKAVG_max_mtb * SPD_aux.mtb_ps) + (pSPD4->tCKAVG_max_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("SDRAM Maximum Cycle Time (tCKAVGmax) %u", SPD_aux.DDR4.tCKAVGmax_ps);

    SNPS_TRACE("Leaving");
    return true;
#endif /* DDRCTL_DDR */
}

/*
 * Read cas latency
 * Byte 20 (0x014): CAS Latencies Supported, First Byte
 * Byte 21 (0x015): CAS Latencies Supported, Second Byte
 * Byte 22 (0x016): CAS Latencies Supported, Third Byte
 * Byte 23 (0x017): CAS Latencies Supported, Fourth Byte
 * Byte 24 (0x018): Minimum CAS Latency Time (tAAmin)
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR4_CAS_LATENCY(void)
{
    SNPS_TRACE("Entering");

    SPD_aux.DDR4.cas_latency_supported = decode_spd_cas_latency_ddr4(pSPD4->CL_supported);
    SNPS_LOG("Cas latencies supported are 0x%.8x", SPD_aux.DDR4.cas_latency_supported);

    //Byte 24 (0x018): Minimum CAS Latency Time (tAAmin)
    if (pSPD4->tAA_min_mtb == 0) {
        SNPS_LOG("Unsupported value : spd Byte[24] tAA_min_mtb=%u. Supported range is 1:255", pSPD4->tAA_min_mtb);
        return false;
    }
    SPD_aux.DDR4.tAAmin_ps = (pSPD4->tAA_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tAA_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum CAS Latency Time %u", SPD_aux.DDR4.tAAmin_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 25 (0x019): Minimum RAS to CAS Delay Time (tRCDmin)
 * Byte 26 (0x01A): Minimum Row Precharge Delay Time (tRPmin)
 */
static inline bool dwc_ddrctl_cinit_SPD_tRCDmin_tRPmin(void)
{
    SNPS_TRACE("Entering");

    //Byte 25 (0x019): Minimum RAS to CAS Delay Time (tRCDmin)
    if (pSPD4->tRCD_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[25] tRCD_min_mtb=%u. Supported range is 1:255", pSPD4->tRCD_min_mtb);
        return false;
    }
    SPD_aux.DDR4.tRCDmin_ps = (pSPD4->tRCD_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tRCD_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum RAS to CAS Delay Time %u", SPD_aux.DDR4.tRCDmin_ps);

    //Byte 26 (0x01A): Minimum Row Precharge Delay Time (tRPmin)
    if (pSPD4->tRP_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[26] tRP_min_mtb=%u. Supported range is 1:255", pSPD4->tRP_min_mtb);
        return false;
    }
    SNPS_LOG("tRP_min_mtb = %u", pSPD4->tRP_min_mtb);
    SPD_aux.DDR4.tRPmin_ps = (pSPD4->tRP_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tRP_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum Row Precharge Delay Time (tRPmin) %u", SPD_aux.DDR4.tRPmin_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 27 (0x01B): Upper Nibbles for tRASmin and tRCmin
 * Byte 28 (0x01C): Minimum Active to Precharge Delay Time (tRASmin), Least Significant Byte
 * Byte 29 (0x01D): Minimum Active to Active/Refresh Delay Time (tRCmin), Least Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_tRASmin_tRCmin(void)
{
    SNPS_TRACE("Entering");
    uint16_t tRASmin_mtb;
    uint16_t tRCmin_mtb;

    tRASmin_mtb = ((pSPD4->tRAS_min_tRC_min_mtb_msb & 0xF) << 8) | pSPD4->tRAS_min_mtb_lsb;
    if (tRASmin_mtb == 0 || tRASmin_mtb >= 4096) {
        SNPS_ERROR("Unsupported value : spd Byte[27,28] tRASmin_mtb=%u. Supported range is 1:4095", tRASmin_mtb);
        return false;
    }
    SNPS_LOG("tRASmin_mtb = %u", tRASmin_mtb);
    SPD_aux.DDR4.tRASmin_ps =  tRASmin_mtb * SPD_aux.mtb_ps; //There is no ftb offset for tRAS_min
    SNPS_LOG("Minimum Active to Precharge Delay Time (tRASmin) = %u", SPD_aux.DDR4.tRASmin_ps);

    tRCmin_mtb = ((((pSPD4->tRAS_min_tRC_min_mtb_msb >> 4) & 0xF) << 8) | pSPD4->tRC_min_mtb_lsb);
    if (tRCmin_mtb == 0 || tRCmin_mtb >= 4096) {
        SNPS_ERROR("Unsupported value : spd Byte[27,29] tRCmin_mtb=%u. Supported range is 1:4095", tRCmin_mtb);
        return false;
    }
    SNPS_LOG("tRCmin_mtb = %u", tRCmin_mtb);
    SPD_aux.DDR4.tRCmin_ps = (tRCmin_mtb * SPD_aux.mtb_ps) + (pSPD4->tRC_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum Active to Active/Refresh Delay Time (tRCmin) %u", SPD_aux.DDR4.tRCmin_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 30 (0x01E): Minimum Refresh Recovery Delay Time (tRFC1min), LSB
 * Byte 31 (0x01F): Minimum Refresh Recovery Delay Time (tRFC1min), MSB
 * Byte 32 (0x020): Minimum Refresh Recovery Delay Time (tRFC2min), LSB
 * Byte 33 (0x021): Minimum Refresh Recovery Delay Time (tRFC2min), MSB
 * Byte 34 (0x022): Minimum Refresh Recovery Delay Time (tRFC4min), LSB
 * Byte 35 (0x023): Minimum Refresh Recovery Delay Time (tRFC4min), MSB
 */
static inline bool dwc_ddrctl_cinit_SPD_tRFC124(void)
{
    SNPS_TRACE("Entering");
    uint16_t tRFC1min_mtb;
    uint16_t tRFC2min_mtb;
    uint16_t tRFC4min_mtb;

    tRFC1min_mtb = (pSPD4->tRFC1_min_mtb_msb << 8) | pSPD4->tRFC1_min_mtb_lsb;
    if (tRFC1min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[30,31] tRFC1min_mtb=%u. Supported range is 1:65535", tRFC1min_mtb);
        return false;
    }
    SNPS_LOG("tRFC1min_mtb = %u", tRFC1min_mtb);
    SPD_aux.DDR4.tRFC1min_ps = tRFC1min_mtb * SPD_aux.mtb_ps;    //No ftb
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC1min) %u", SPD_aux.DDR4.tRFC1min_ps);

    tRFC2min_mtb = (pSPD4->tRFC2_min_mtb_msb << 8) | pSPD4->tRFC2_min_mtb_lsb;
    if (tRFC2min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[32,33] tRFC2min_mtb=%d. Supported range is 1:65535", tRFC2min_mtb);
        return false;
    }
    SNPS_LOG("tRFC2min_mtb = %u", tRFC2min_mtb);
    SPD_aux.DDR4.tRFC2min_ps = tRFC2min_mtb * SPD_aux.mtb_ps;    //No ftb
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC2min) %u", SPD_aux.DDR4.tRFC2min_ps);

    tRFC4min_mtb = (pSPD4->tRFC4_min_mtb_msb << 8) | pSPD4->tRFC4_min_mtb_lsb;
    if (tRFC4min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[34,35] tRFC4min_mtb=%u. Supported range is 1:65535", tRFC4min_mtb);
        return false;
    }
    SNPS_LOG("tRFC4min_mtb = %u", tRFC4min_mtb);
    SPD_aux.DDR4.tRFC4min_ps = tRFC4min_mtb * SPD_aux.mtb_ps;    //No ftb
    SNPS_LOG("Minimum Refresh Recovery Delay Time (tRFC4min) %u", SPD_aux.DDR4.tRFC4min_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 36 (0x024): Upper Nibble for tFAW
 * Byte 37 (0x025): Minimum Four Activate Window Delay Time (tFAWmin), Least Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_tFAWmin(void)
{
    SNPS_TRACE("Entering");
    uint16_t tFAWmin_mtb;

    tFAWmin_mtb = ((pSPD4->tFAW_min_mtb_msb & 0xF) << 8) | pSPD4->tFAW_min_mtb_lsb;
    if (tFAWmin_mtb == 0 || tFAWmin_mtb >= 4096) {
        SNPS_ERROR("Unsupported value : spd Byte[36,37] tFAWmin_mtb=%u. Supported range is 1:4095", tFAWmin_mtb);
        return false;
    }
    SNPS_LOG("tFAWmin_mtb = %u", tFAWmin_mtb);
    SPD_aux.DDR4.tFAWmin_ps = tFAWmin_mtb * SPD_aux.mtb_ps;    //No ftb
    SNPS_LOG("Minimum Four Activate Window Delay Time (tFAWmin) %u", SPD_aux.DDR4.tFAWmin_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 38 (0x026): Minimum Activate to Activate Delay Time (tRRD_Smin), Different Bank Group
 * Byte 39 (0x027): Minimum Activate to Activate Delay Time (tRRD_Lmin), Same Bank Group
 */
static inline bool dwc_ddrctl_cinit_SPD_tRRD(void)
{
    SNPS_TRACE("Entering");

    if (pSPD4->tRRD_S_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[38] tRRD_S_min_mtb=%u. Supported range is 1:255", pSPD4->tRRD_S_min_mtb);
        return false;
    }
    SNPS_LOG("tRRD_S_min_mtb = %u", pSPD4->tRRD_S_min_mtb);
    SPD_aux.DDR4.tRRD_Smin_ps = (pSPD4->tRRD_S_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tRRD_S_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum Activate to Activate Delay Time (tRRD_Smin), Different Bank Group %u", SPD_aux.DDR4.tRRD_Smin_ps);

    //Byte 39 (0x027): Minimum Activate to Activate Delay Time (tRRD_Lmin), Same Bank Group
    if (pSPD4->tRRD_L_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[39] tRRD_L_min_mtb=%u. Supported range is 1:255", pSPD4->tRRD_L_min_mtb);
        return false;
    }
    SNPS_LOG("tRRD_L_min_mtb = %u", pSPD4->tRRD_L_min_mtb);
    SPD_aux.DDR4.tRRD_Lmin_ps = (pSPD4->tRRD_L_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tRRD_L_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum Activate to Activate Delay Time (tRRD_Lmin), Same Bank Group %u", SPD_aux.DDR4.tRRD_Lmin_ps);

    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 40 (0x028): Minimum CAS to CAS Delay Time (tCCD_Lmin), Same Bank Group
 */
static inline bool dwc_ddrctl_cinit_SPD_tCCD_Lmin(void)
{
    SNPS_TRACE("Entering");

    if (pSPD4->tCCD_L_min_mtb == 0) {
        SNPS_ERROR("Unsupported value : spd Byte[40] tCCD_L_min_mtb=%d. Supported range is 1:255", pSPD4->tCCD_L_min_mtb);
        return false;
    }
    SNPS_LOG("tCCD_L_min_mtb = %u", pSPD4->tCCD_L_min_mtb);
    SPD_aux.DDR4.tCCD_Lmin_ps = (pSPD4->tCCD_L_min_mtb * SPD_aux.mtb_ps) + (pSPD4->tCCD_L_min_ftb * SPD_aux.ftb_ps);
    SNPS_LOG("Minimum CAS to CAS Delay Time (tCCD_Lmin), Same Bank Group %u", SPD_aux.DDR4.tCCD_Lmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 41 (0x029): Upper Nibble for tWRmin
 * Byte 42 (0x02A): Minimum Write Recovery Time (tWRmin)
 * Byte 41-42 not present in 1.0
 * Byte 43 (0x029): Upper Nibbles for tWTRmin
 * Byte 44 (0x02C): Minimum Write to Read Time (tWTR_Smin), Different Bank Group
 * Byte 45 (0x02D): Minimum Write to Read Time (tWTR_Lmin), Same Bank Group
 * Byte 43-45 not present in 1.0
 */
static inline bool dwc_ddrctl_cinit_SPD_tWRmin_tWTRmin(void)
{
    uint16_t tWRmin_mtb;
    uint16_t tWTR_Smin_mtb;
    uint16_t tWTR_Lmin_mtb;

    if (SPD_aux.revision < 0x11) {
        return false;
    }

    tWRmin_mtb = (pSPD4->tWR_min_mtb_msb << 8) | pSPD4->tWR_min_mtb_lsb;
    if ((tWRmin_mtb == 0) || (tWRmin_mtb >= 4096)) {
        SNPS_ERROR("Unsupported value : spd Byte[41,42] tWRmin_mtb=%u. Supported range is 1:4095", tWRmin_mtb);
        return false;
    }
    SNPS_LOG("tWRmin_mtb = %u", tWRmin_mtb);
    SPD_aux.DDR4.tWRmin_ps = tWRmin_mtb * SPD_aux.mtb_ps;    //No ftb

    SNPS_LOG("tWRmin_ps = %u", SPD_aux.DDR4.tWRmin_ps);


    tWTR_Smin_mtb = ((pSPD4->tWTR_L_min_tWTR_S_min_mtb_msb & 0xF) << 8) | pSPD4->tWTR_S_min_mtb_lsb;
    if ((tWTR_Smin_mtb == 0) || (tWTR_Smin_mtb >= 4096)) {
        SNPS_ERROR("Unsupported value : spd Byte[43,44] tWTR_Smin_mtb=%d. Supported range is 1:4095", tWTR_Smin_mtb);
        return false;
    }
    SNPS_LOG("tWTR_Smin_mtb = %u", tWTR_Smin_mtb);
    SPD_aux.DDR4.tWTR_Smin_ps = tWTR_Smin_mtb * SPD_aux.mtb_ps;    //No ftb

    SNPS_LOG("tWTR_Smin_ps = %u", SPD_aux.DDR4.tWTR_Smin_ps);


    tWTR_Lmin_mtb = (((pSPD4->tWTR_L_min_tWTR_S_min_mtb_msb >> 4) & 0xF) << 8) | pSPD4->tWTR_L_min_mtb_lsb;
    if ((tWTR_Lmin_mtb == 0) || (tWTR_Lmin_mtb >= 4096)) {
        SNPS_ERROR("Unsupported value : spd Byte[43,45] tWTR_Lmin_mtb=%d. Supported range is 1:4095", tWTR_Lmin_mtb);
        return false;
    }
    SNPS_LOG("tWTR_Lmin_mtb = %u", tWTR_Lmin_mtb);
    SPD_aux.DDR4.tWTR_Lmin_ps = tWTR_Lmin_mtb * SPD_aux.mtb_ps;    //No ftb

    SNPS_LOG("tWTR_Lmin_ps = %u", SPD_aux.DDR4.tWTR_Lmin_ps);
    return true;
}


/***************** End DDR4 Functions *********************/

/****************** DDR5 Functions *********************/

#endif /* DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC*/

/**
 * @brief Get lower supported CAS latency value for the timings
 *
 * @param spd           SPD data structure
 * @param tck_avg_ps    tCK average in picoseconds
 *
 * @return uint8_t  lower supported CAS latency or 0 if no valid values is found
 */
uint8_t ddrctl_cinit_get_ddr5_spd_cas_latency(SPD_aux_t *spd, const uint16_t tck_avg_ps)
{
    ddrctl_error_t rslt;
    ddrctl_bool_t  is_3ds;
    uint8_t        cas_latency;
    uint8_t        cas_supported;
    uint8_t        j;

    is_3ds = spd->cid_width[0] > 0 ? DDRCTL_TRUE : DDRCTL_FALSE;

    rslt = ddrctl_cinit_get_ddr5_cas_latency(tck_avg_ps, spd->DDR5.tAAmin_ps, spd->DDR5.tRCDmin_ps,
                                             spd->DDR5.tRPmin_ps, is_3ds, &cas_latency);

    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("No CAS Latency Supported");
        return 0;
    }

    SNPS_ERROR("CAS Latency Supported = %d", cas_latency);

    for (j = 0; j < 48; j++) {
        if (spd->DDR5.cas_latency_supported & (1LL << j)) {
            cas_supported = (2 * j) + 20;
            if (cas_supported >= cas_latency) {
                return cas_supported;
            }
        }
    }
    SNPS_ERROR("No CAS Latency Supported");
    return 0;
}

#ifdef DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC
/*
 * Byte 4 (0x004): First SDRAM Density and Package
 * Byte 8 (0x008): Second SDRAM Density and Package
 * Read sdram capacity and CID-Width
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_B4_B8(uint8_t sdram_num)
{
    SNPS_TRACE("Entering");
    uint8_t sdram_density_banks;

    if (sdram_num >= DWC_DDRCTL_DEV_CFG_NUM)
        return false;

    // SDRAM capacity DDR5
    if (sdram_num == 0)
        sdram_density_banks = pSPD5->sdram_density_banks;
    else
        sdram_density_banks = pSPD5->second_sdram_package_type;

    switch (pSPD5->sdram_density_banks & 0x1F) {
    case 1:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 4096;    // 4 Gb
        break;
    case 2:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 8192;    // 8 Gb
        break;
    case 3:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 12288; // 12 Gb
        break;
    case 4:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 16384; // 16 Gb
        break;
    case 5:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 24576; // 24 Gb
        break;
    case 6:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 32768; // 32 Gb
        break;
    case 7:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 49152; // 48 Gb
        break;
    case 8:
        SPD_aux.sdram_capacity_mbits[sdram_num] = 65536; // 64 Gb
        break;
    default:
        SNPS_ERROR("Invalid option - Total SDRAM capacity per DIMM", NULL);
        return false;
    }
    SNPS_LOG("SPD.sdram_capacity_mbits[%u] = %u", sdram_num, SPD_aux.sdram_capacity_mbits[sdram_num]);

    switch ((sdram_density_banks >> 5) & 0x3) {
    case 0:
        SPD_aux.cid_width[sdram_num] = 0;    // Non-3DS
        break;
    case 2:
        SPD_aux.cid_width[sdram_num] = 1;    // 2H 3DS
        break;
    case 3:
        SPD_aux.cid_width[sdram_num] = 2;    // 4H 3DS
        break;
    default:
        SNPS_ERROR("Invalid option - CID_WIDTH Invalid", NULL);
        return false;
    }
    SNPS_LOG("Cid width for Sdram package %u is %u - %uH %s", sdram_num, SPD_aux.cid_width[sdram_num], SPD_aux.cid_width[sdram_num] * 2, SPD_aux.cid_width[sdram_num] == 0 ? "Non-3DS" : "3DS");

    SNPS_TRACE("Leaving");
    return true;
}

/**
 * Byte 5 (0x005): First SDRAM Addressing
 * Byte 9 (0x009): Second SDRAM Addressing
 * @brief Function to read the DDR5 sdram_capacity.
 * read cid_widht on DDR5
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_B5_B9(uint8_t sdram_num)
{
    SNPS_TRACE("Entering");
    uint8_t sdram_addressing;

    if (sdram_num >= DWC_DDRCTL_DEV_CFG_NUM)
        return false;

    if (sdram_num == 0)
        sdram_addressing = pSPD5->sdram_addressing;
    else
        sdram_addressing = pSPD5->second_sdram_addressing;

    // SDRAM row address bits
    switch (SNPS_READ_EXPLICIT_FIELD(sdram_addressing, 0, 0x1F)) {
        case 0:
            SPD_aux.dram_raw[sdram_num] = 16;            // 16 rows address bits
            break;
        case 1:
            SPD_aux.dram_raw[sdram_num] = 17;            // 17 rows address bits
            break;
        case 2:
            SPD_aux.dram_raw[sdram_num] = 18;            // 18 rows address bits
            break;
        default:
            SNPS_ERROR("Invalid option - SDRAM-%u row address bits", sdram_num);
            return false;
    }
    SNPS_LOG("%u rows address bits for %u sdram", SPD_aux.dram_raw[sdram_num], sdram_num);
    // SDRAM column address bits
    switch (SNPS_READ_EXPLICIT_FIELD(sdram_addressing, 5, 0xE0)) {
        case 0:
            SPD_aux.dram_caw[sdram_num] = 10;    // 10 columns address bits
            break;
        case 1:
            SPD_aux.dram_caw[sdram_num] = 11;    // 10 columns address bits
            break;
        default:
            SNPS_ERROR("Invalid option - SDRAM-%u column address bits", sdram_num);
            return false;
    }
    SNPS_LOG("%u columns address bits for sdram %u", SPD_aux.dram_caw[sdram_num], sdram_num);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * Byte 6 First SDRAM I/O Width
 * Byte 0xA Second SDRAM I/O Width
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_B6_BA(uint8_t sdram_num)
{
    uint8_t sdram_width;

    if (sdram_num >= DWC_DDRCTL_DEV_CFG_NUM)
        return false;

    if (sdram_num == 0)
        sdram_width = SNPS_READ_EXPLICIT_FIELD(pSPD5->sdram_width, 5, 0xE0);
    else
        sdram_width = SNPS_READ_EXPLICIT_FIELD(pSPD5->second_sdram_width, 5, 0xE0);

    switch (sdram_width) {
        case 0:
            SPD_aux.sdram_width_bits[sdram_num] = 4;
            break;
        case 1:
            SPD_aux.sdram_width_bits[sdram_num] = 8;
            break;
        case 2:
            SPD_aux.sdram_width_bits[sdram_num] = 16;
            break;
        case 3:
            SPD_aux.sdram_width_bits[sdram_num] = 32;
            break;
        default:
            SNPS_ERROR("Invalid width for sdram-%u", sdram_num);
            return false;
    }
    SNPS_LOG("SDRAM-%u width is %u", sdram_num, SPD_aux.sdram_width_bits[sdram_num]);

    return true;
}

/*
 * Byte 7 First SDRAM Bank Groups & Banks Per Bank Group
 * Byte 11 (0x00B): Second SDRAM Bank Groups & Banks Per Bank Group
 * Read bank Groups
 * Read BAnks per bank group
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_B7_BB(uint8_t sdram_num)
{
    uint8_t banks;
    uint8_t sdram_bkg_bpbg;

    if (sdram_num >= DWC_DDRCTL_DEV_CFG_NUM)
        return false;

    if (sdram_num == 0)
        sdram_bkg_bpbg = pSPD5->sdram_bkg_bpbg;
    else
        sdram_bkg_bpbg = pSPD5->second_sdram_bkg_bpbg;

    //!<Bank address bits = banks in each Bank Group
    banks = SNPS_READ_EXPLICIT_FIELD(sdram_bkg_bpbg, 0, 0x07);
    if (banks < 3) {
        SPD_aux.dram_baw[sdram_num] = banks;
    } else {
        SNPS_ERROR("SDRAM-%u invalid number of bank address bits %u", sdram_num, (1 << banks));
        return false;
    }
    SNPS_LOG("SDRAM-%u banks address bits %u", sdram_num, (1 << SPD_aux.dram_baw[sdram_num]));

    banks = SNPS_READ_EXPLICIT_FIELD(sdram_bkg_bpbg, 5, 0xE0);
    if (banks <= 3) {
        SPD_aux.dram_bgw[sdram_num] = banks;
    } else {
        SNPS_ERROR("sdram-%u invalid number of bank group bits %u", sdram_num, (1 << banks));
        return false;
    }
    SNPS_LOG("SDRAM-%u number of bank group bits %u", sdram_num, (1 << SPD_aux.dram_bgw[sdram_num]));

    return true;
}

/*
 * byte 20 and byte 21
 * SDRAM Minimum Cycle Time
 * tCKAVGmin -> tck_ps
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tCKAVGmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tCKAVGmin = pSPD5->tCKAVGmin;
    SNPS_LOG("SDRAM Minimum Cycle Time (tCKAVGmin) %u", SPD_aux.DDR5.tCKAVGmin);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Maximum Cycle Time
 * tCKAVGmax
 * Byte 22 (0x016): Least Significant Byte
 * Byte 23 (0x017): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tCKAVGmax(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tCKAVGmax = pSPD5->tCKAVGmax;
    SNPS_LOG("SDRAM Maximum Cycle Time (tCKAVGmax) %u", SPD_aux.DDR5.tCKAVGmax);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM CAS Latencies Supported
 * Byte 24 (0x018): First Byte
 * Byte 25 (0x019): Second Byte
 * Byte 26 (0x01A): Third Byte
 * Byte 27 (0x01B): Fourth Byte
 * Byte 28 (0x01C): Fifth Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_cas_latencies_supported(void)
{
    SPD_aux.DDR5.cas_latency_supported = pSPD5->CASlatency_byte0;
    SPD_aux.DDR5.cas_latency_supported |= pSPD5->CASlatency_byte1 << 8;
    SPD_aux.DDR5.cas_latency_supported |= pSPD5->CASlatency_byte2 << 16;
    SPD_aux.DDR5.cas_latency_supported |= pSPD5->CASlatency_byte3 << 24;
    SPD_aux.DDR5.cas_latency_supported |= ((uint64_t )pSPD5->CASlatency_byte4) << 32;

    SNPS_LOG("CAs latency supported 0x%lx", SPD_aux.DDR5.cas_latency_supported);
    return true;
}

/*
 * SDRAM Minimum CAS Latency Time (tAAmin)
 * Byte 30 (0x01E): Least Significant Byte
 * Byte 31 (0x01F): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tAAmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tAAmin_ps = pSPD5->tAAmin;
    SNPS_LOG("Minimum CAS Latency Time %u", SPD_aux.DDR5.tAAmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum RAS to CAS Delay Time (tRCDmin)
 * Byte 32 (0x020): Least Significant Byte
 * Byte 33 (0x021): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tRCDmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRCDmin_ps = pSPD5->tRCDmin;
    SNPS_LOG("SDRAM Minimum RAS to CAS Delay Time (tRCDmin) %u", SPD_aux.DDR5.tRCDmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Row Precharge Delay Time (tRPmin)
 * Byte 34 (0x022): Least Significant Byte
 * Byte 35 (0x023): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tRPmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRPmin_ps = pSPD5->tRPmin;
    SNPS_LOG("SDRAM Minimum Row Precharge Delay Time (tRPmin) %u", SPD_aux.DDR5.tRPmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Active to Precharge Delay Time (tRASmin)
 * Byte 36 (0x024): Least Significant Byte
 * Byte 37 (0x025): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tRASmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRASmin_ps = pSPD5->tRASmin;
    SNPS_LOG("SDRAM Minimum Row Precharge Delay Time (tRASmin) %u", SPD_aux.DDR5.tRASmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin)
 * Byte 38 (0x026): Least Significant Byte
 * Byte 39 (0x027): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tRCmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRCmin_ps = pSPD5->tRCmin;
    SNPS_LOG("SDRAM Minimum Active to Active/Refresh Delay Time (tRCmin) %u", SPD_aux.DDR5.tRCmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Write Recovery Time (tWRmin)
 * Byte 40 (0x028): Least Significant Byte
 * Byte 41 (0x029): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tWRmin(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tWRmin_ps = pSPD5->tWRmin;
    SNPS_LOG("SDRAM Minimum Write Recovery Time (tWRmin) (tWRmin) %u", SPD_aux.DDR5.tWRmin_ps);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min)
 * tRFC1 relates to monolithic SDRAMs, tRFC1_slr to 3DS SDRAMs.
 * Byte 42 (0x02A): Least Significant Byte
 * Byte 43 (0x02B): Most Significant Byte
 * SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min)
 * Byte 44 (0x02C): Least Significant Byte
 * Byte 45 (0x02D): Most Significant Byte
 * SDRAM Minimum Refresh Recovery Delay Time (tRFCsbmin, tRFCsb_slr min)
 * Byte 46 (0x02E): Least Significant Byte
 * Byte 47 (0x02F): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_tRFC(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRFC1_slr_min_ns = pSPD5->tRFC1_slr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFC1min, tRFC1_slr min) is %u", SPD_aux.DDR5.tRFC1_slr_min_ns);

    SPD_aux.DDR5.tRFC2_slr_min_ns = pSPD5->tRFC2_slr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFC2min, tRFC2_slr min) is %u", SPD_aux.DDR5.tRFC2_slr_min_ns);

    SPD_aux.DDR5.tRFCsb_slr_min_ns = pSPD5->tRFCsb_slr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time (tRFCsb_dlr min) is %u", SPD_aux.DDR5.tRFCsb_slr_min_ns);
    SNPS_TRACE("Leaving");
    return true;
}

/*
 * SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank(tRFC1_dlr min)
 * Byte 48 (0x030): Least Significant Byte
 * Byte 49 (0x031): Most Significant Byte
 * SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank(tRFC2_dlr min)
 * Byte 50 (0x032): Least Significant Byte
 * Byte 51 (0x033): Most Significant Byte
 * SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank(tRFCsb_dlr min)
 * Byte 52 (0x034): Least Significant Byte
 * Byte 53 (0x035): Most Significant Byte
 */
static inline bool dwc_ddrctl_cinit_SPD_DDR5_trfc_dlr(void)
{
    SNPS_TRACE("Entering");
    SPD_aux.DDR5.tRFC1_dlr_min_ns = pSPD5->tRFC1_dlr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFC1_dlr min) is %u", SPD_aux.DDR5.tRFC1_dlr_min_ns);

    SPD_aux.DDR5.tRFC2_dlr_min_ns = pSPD5->tRFC2_dlr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank  (tRFC2_dlr min) is %u", SPD_aux.DDR5.tRFC2_dlr_min_ns);

    SPD_aux.DDR5.tRFCsb_dlr_min_ns = pSPD5->tRFCsb_dlr_min;
    SNPS_LOG("SDRAM Minimum Refresh Recovery Delay Time, 3DS Different Logical Rank (tRFCsb_dlr min) is %u", SPD_aux.DDR5.tRFCsb_dlr_min_ns);
    SNPS_TRACE("Leaving");
    return true;
}


/******************  End Functions DDR5 *********************/
/*
 *Number of Package Ranks per Channel byte 234 (0xEA)
 */
static inline uint32_t dwc_ddrctl_cinit_SPD_B0xEA(void)
{
    // SDRAM device width bits
    SPD_aux.num_ranks_per_dimm = SNPS_READ_EXPLICIT_FIELD(pSPD5->module_organization, 3, 0x38) + 1;
    SPD_aux.num_ranks = SPD_aux.num_ranks_per_dimm * SPD_aux.num_dimm;
    SNPS_LOG("Number of ranks per dimm is %u", SPD_aux.num_ranks_per_dimm);
    SNPS_LOG("Number of ranks is %u", SPD_aux.num_ranks);
    return 1;
}

static inline uint32_t dwc_ddrctl_cinit_SPD_B0xEB(void)
{
    switch (SNPS_READ_EXPLICIT_FIELD(pSPD5->memory_channel_bus_width, 0, 0x07)) {
    case 0:
        SPD_aux.module_width_bits = 8;
    break;
    case 1:
        SPD_aux.module_width_bits = 16;
    break;
    case 2:
        SPD_aux.module_width_bits = 32;
    break;
    case 3:
        SPD_aux.module_width_bits = 64;
    break;
    default:
        return false;
    }
    SNPS_LOG("Module memory bus width is %u", SPD_aux.module_width_bits);

    if (SNPS_READ_EXPLICIT_FIELD(pSPD5->memory_channel_bus_width, 3, 0x18) > 1) // ECC only supported on 8-bit extensions
        SPD_aux.ecc_supported = 1;
    else
        SPD_aux.ecc_supported = 0;

    SNPS_LOG("ECC is %u", SPD_aux.ecc_supported);
    SNPS_TRACE("Leaving");
    return 1;
}

ddrctl_error_t dwc_ddrctl_cinit_SPD_retrieve(void)
{
    uint16_t size;
    uint16_t addr_map_addr;
    uint8_t tmp;

    if (!dwc_ddrctl_cinit_io_i2c_config() || !dwc_ddrctl_cinit_io_i2c_enable()) {
        SNPS_ERROR("Can not initialize I2C", NULL);
        return DDRCTL_ERROR;
    }

    // Key Byte / DRAM Device Type
    if (!dwc_ddrctl_cinit_io_i2c_read(2, &tmp, 1)) {
        SNPS_ERROR("Can not read byte 2", NULL);
        goto error;
    }

    SPD_aux.use_lpddr4x = 0;
    switch (tmp) {
#ifdef DDRCTL_DDR
    case 12:
        SPD_aux.sdram_protocol = DWC_DDR4;    // DDR4
        SNPS_LOG("SDRAM Protocol is DDR4", NULL);
        break;
    case 18:
        SPD_aux.sdram_protocol = DWC_DDR5;    // DDR5
        SNPS_LOG("SDRAM Protocol is DDR5", NULL);
        break;
#endif /* DDRCTL_DDR */
    default:
        SNPS_ERROR("Invalid option -  DRAM Device Type %u", tmp);
        goto error;
    }
    // Save to CINIT SPD struct
    SPD.sdram_protocol = SPD_aux.sdram_protocol;
    SPD.use_lpddr4x = SPD_aux.use_lpddr4x;

    // At this stage we don't care if is DDR or DDR5, both shares the same byte 0 content
    if (!dwc_ddrctl_cinit_io_i2c_read(0, &tmp, 1)) {
        SNPS_ERROR("Can not read byte 0", NULL);
        goto error;
    }
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        // On DDR4 we only care for SPD bytes used
        tmp &= 0x0f;
        switch (tmp) {
        case 1:
            size = 126;
            break;
        case 2:
            size = 256;
            break;
        case 3:
            size = 384;
            break;
        case 4:
            size = 512;
            break;
        default:
            SNPS_ERROR("Invalid value on number of %u bytes", tmp);
            goto error;
        }
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        // On DDR5 we only care for SPD bytes total
        tmp >>= 4;
        tmp &= 0x07;
        switch (tmp) {
        case 1:
            size = 256;
            break;
        case 2:
            size = 512;
            break;
        case 3:
            size = 1024;
            break;
        default:
            SNPS_ERROR("Invalid value on number of %u bytes", tmp);
            goto error;
        }
    }
#endif /* CINIT_DDR5 */
    SNPS_LOG("SPD will read %u bytes", size);

    /* Read SPD revision */
    if (!dwc_ddrctl_cinit_io_i2c_read(1, &tmp, 1)) {
        SNPS_ERROR("Can not read byte 1", NULL);
        goto error;
    }

    SPD_aux.revision = tmp;

    // At this stage we don't care if is DDR or DDR5, both shares the same memory space
    if (sizeof(SPD_DDR4_t) != sizeof(SPD_DDR5_t)) {
        SNPS_ERROR("DDR4 (%u bytes) and DDR5 (%u bytes) structures have different sizes!!!", sizeof(SPD_DDR4_t), sizeof(SPD_DDR5_t));
        goto error;
    }

    if (!dwc_ddrctl_cinit_io_i2c_read(0, (uint8_t *)&SPD_ddr, min(sizeof(SPD_ddr), size))) {
        SNPS_ERROR("Can not read SPD content", NULL);
        goto error;
    }
    SNPS_LOG("Read %u bytes from SPD", min(sizeof(SPD_ddr), size));

    // At this stage we don't care if is DDR or DDR5, both shares the same memory space
    // SDRAM module type
    switch (SPD_ddr.SPD_DDR4.kb_module_type & 0xf) {
    case 1:
        SPD_aux.module_type = DWC_RDIMM; // RDIMM
        SNPS_LOG("SPD.module_type is RDIMM", NULL);
        break;
    case 2:
        SPD_aux.module_type = DWC_UDIMM; // UDIMM
        SNPS_LOG("SPD.module_type is UDIMM", NULL);
        break;
    case 4:
        SPD_aux.module_type = DWC_LRDIMM; // LRDIMM
        SNPS_LOG("SPD.module_type is LRDIMM", NULL);
        break;
    default:
        SNPS_ERROR("Invalid option - SDRAM module type", NULL);
        goto error;
    }
    SPD.module_type = SPD_aux.module_type;
#ifdef CINIT_DDR4
    if (IS_DDR4) {
        pSPD4 = &SPD_ddr.SPD_DDR4;
        // Verify CRC
        if (!dwc_ddrctl_cinit_SPD_CRC((uint8_t *)&SPD_ddr, size))
            goto error;
        // SDRAM Density and Banks
        if (!dwc_ddrctl_cinit_SPD_DDR4_B4())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_B5())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_B6())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_B0C())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_B0D())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_timmings_ps())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR4_CAS_LATENCY())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tRASmin_tRCmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tRCDmin_tRPmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tRFC124())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tFAWmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tRRD())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tCCD_Lmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_tWRmin_tWTRmin())
            goto error;

        //Byte 128-255 (according to which DDR4 module family - use kb3)
        if ((size >= 256) && (SPD_aux.module_type == DWC_UDIMM || SPD_aux.module_type == DWC_RDIMM)) {

            if (SPD_aux.module_type == DWC_UDIMM) {
                //Byte 131 (0x083) (Unbuffered): Address Mapping from Edge Connector to DRAM
                addr_map_addr = 131;
            } else {
                //Byte 136 (0x088) (Registered): Address Mapping from Register to DRAM
                addr_map_addr = 136;
            }

            if (!dwc_ddrctl_cinit_io_i2c_read(addr_map_addr, &tmp, 1)) {
                SNPS_ERROR("Can not read byte 0", NULL);
                goto error;
            }

            SPD_aux.addr_mirror = (tmp & 0x1);
            SNPS_LOG("Address mirror is %s", SPD_aux.addr_mirror == 1 ? "enable" : "disable");
        }
    }
#endif /* CINIT_DDR4 */
#ifdef CINIT_DDR5
    if (IS_DDR5) {
        pSPD5 = &SPD_ddr.SPD_DDR5;
        // Verify CRC
        if (!dwc_ddrctl_cinit_SPD_CRC((uint8_t *)&SPD_ddr, size))
            goto error;
        // SDRAM Density and Banks
        for (uint8_t i = 0; i < DWC_DDRCTL_DEV_CFG_NUM; i++) {
            if (!dwc_ddrctl_cinit_SPD_DDR5_B4_B8(i))
                goto error;
            if (!dwc_ddrctl_cinit_SPD_DDR5_B5_B9(i))
                goto error;
            if (!dwc_ddrctl_cinit_SPD_DDR5_B6_BA(i))
                goto error;
            if (!dwc_ddrctl_cinit_SPD_DDR5_B7_BB(i))
                goto error;
        }
        if (!dwc_ddrctl_cinit_SPD_DDR5_tCKAVGmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tCKAVGmax())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_cas_latencies_supported())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tAAmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tRCDmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tRPmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tRASmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tRCmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tWRmin())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_tRFC())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_DDR5_trfc_dlr())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_B0xEA())
            goto error;
        if (!dwc_ddrctl_cinit_SPD_B0xEB())
            goto error;
    }
#endif /* CINIT_DDR5 */
    if (false == dwc_ddrctl_cinit_io_i2c_disable()) {
        SNPS_WARN("i2C disable command failed\n");
    }

    SNPS_TRACE("Leaving");
    return DDRCTL_SUCCESS;

error:
    if (false == dwc_ddrctl_cinit_io_i2c_disable()) {
        SNPS_WARN("i2C disable command failed\n");
    }

    SNPS_TRACE("Leaving");
    return DDRCTL_ERROR;
}

#endif /* DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC */

#endif /* DDRCTL_DDR */
