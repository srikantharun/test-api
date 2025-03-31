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


#ifndef __DWC_DDRCTL_CINIT_PRGM_HWFFCMRW_H__
#define __DWC_DDRCTL_CINIT_PRGM_HWFFCMRW_H__

/*************************************************************************
 * TYPEDEFS for HWFFC MRW BUFFER value
 *************************************************************************/

/**
 * @brief The following union types define the encoded MRW instruction structure. Must be align with hwffcmrwbuf_encoding_s defined in gs_load_mr_hwffc_seq.sv
 */
typedef struct tag_HWFFCMRW_t {
  uint8_t data            : 8;    // [00 ... 07]
  uint8_t addr            : 8;    // [08 ... 15]  - LPDDR5 MR is 7-bit address. DDR5 already has 8-bit address. Reserve 8th bit for future use
  uint8_t interval        : 3;    // [16 ... 18]
  uint8_t tail            : 1;    // [19]
  uint8_t rank            : 2;    // [20 ... 21]
  uint16_t _padding       : 10;   // [22 ... 31]
} HWFFCMRW_t;

enum dwc_mrwbuf_interval_e {
  TB2B          = 0,  // back to back
  TMRW          = 1,
  TMRW_L        = 2,
  TVRCG_DISABLE = 4,
  TVRCG_ENABLE  = 5,
};

// The default value of VREF CA, VREF DQ[7:0] and VREF DQ[15:8] settings for MR12, 14 and 15.
#define VREF_CA_DQ_DEFAULT  0b1010000   
// The default value of DCA, DFE and DQ emphasis for MR30, 58 and 69 to 74
#define TRAINED_VALUE_DEFAULT     0

#define HWFFCMRW_PERRANK 1
#define HWFFCMRW_ALLRANK 0
#define HWFFCMRW_PERBYTE 1
#define HWFFCMRW_ALLBYTE 0

#endif /* __DWC_DDRCTL_CINIT_PRGM_HWFFCMRW_H__ */
