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
#include "dwc_ddrctl_cinit_prgm_hwffcmrw.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"


#ifdef DDRCTL_HWFFC_EXT_AND_LPDDR5X
// customer should replace VREF_CA_DQ_DEFAULT and TRAINED_VALUE_DEFAULT with real values obtained from PHY training.
static uint8_t ddrctl_lpddr5_get_mr_value (
  const lpddr5_mode_registers_t* const mr,
  const int mr_addr,
  const int byte_select
) {
  uint8_t data = 0;
  switch (mr_addr) {
  case  1:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr1.write_latency);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 3, mr->mr1.ck_mode);
    break;
  case  2:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr2.nwr);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr2.rl_nrtp);
    break;
  case  3:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 7, mr->mr3.write_dbi);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 6, mr->mr3.read_dbi);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 5, mr->mr3.wls);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 3, mr->mr3.bk_bg_org);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr3.pdds);
    break;
  case 10:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 6, mr->mr10.rdqs_pst);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr10.rdqs_pre);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 2, mr->mr10.wck_pst);
    break;
  case 11:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 7, mr->mr11.cs_odt_op);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr11.ca_odt);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 3, mr->mr11.nt_odt);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr11.dq_odt);
    break;
  case 12:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 7, byte_select);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, VREF_CA_DQ_DEFAULT);
    SNPS_DEBUG("byte_select=%0d", byte_select);
    break;
  case 14:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, VREF_CA_DQ_DEFAULT);
    break;
  case 15:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, VREF_CA_DQ_DEFAULT);
    break;
  case 17:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 6, mr->mr17.odtd);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 5, mr->mr17.odtd_ca);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr17.odtd_cs);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 3, mr->mr17.odtd_ck);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr17.soc_odt);
    break;
  case 18:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 7, mr->mr18.ckr);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 6, mr->mr18.wck2ck_leveling);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr18.wck_on);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 3, mr->mr18.wck_fm);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr18.wck_odt);
    break;
  case 19:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 2, mr->mr19.dvfsq);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr19.dvfsc);
    break;
  case 20:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 2, mr->mr20.wck_mode);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr20.rdqs);
    break;
  case 22:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 6, mr->mr22.recc);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr22.wecc);
    break;
  case 24:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 4, mr->mr24.dfequ);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr24.dfeql);
    break;
  case 30:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 41:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 5, mr->mr41.nt_dq_odt);
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, mr->mr41.pdfec);
    break;
  case 58:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 69:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 70:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 71:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 72:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 73:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 74:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, TRAINED_VALUE_DEFAULT);
    break;
  case 56:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, 0x0F); // testing purpose. value is don't care.
    break;
  case 60:
    SNPS_WRITE_EXPLICIT_FIELD_WO_MASK(data, 0, 0xF0); // testing purpose. value is don't care.
    break; // testing purpose. value is don't care.
  default:
    CINIT_ASSERT(0); // unknown MR addresses
  }
  return data;
}

static uint8_t ddrctl_lpddr5_get_mrw_interval (const int mr_addr) {
  uint8_t interval = 0;
  switch (mr_addr) {
  case 24:
  case 70:
  case 71:
  case 72:
  case 73:
  case 74: interval = TMRW_L;         break;  // DFE related registers requires tMRW_L interval to write
  case 56: interval = TVRCG_DISABLE;  break;  // testing purpose
  case 60: interval = TVRCG_ENABLE;   break;  // testing purpose
  default: interval = TMRW;           break;
  }
  return interval;
}

// HWFFCMRW_t factory
static HWFFCMRW_t get_mrw_entry (
  const lpddr5_mode_registers_t* const mr,
  const int mr_addr,
  const int rank,
  const int tail,
  const int byte_select
) {
  HWFFCMRW_t hwffcmrw = (HWFFCMRW_t) { .addr = mr_addr, .rank = rank, .tail = tail };
  hwffcmrw.data     = ddrctl_lpddr5_get_mr_value(mr, mr_addr, byte_select);
  hwffcmrw.interval = ddrctl_lpddr5_get_mrw_interval(mr_addr);
  return hwffcmrw;
}

static uint32_t encode_hwffcmrw(HWFFCMRW_t hwffcmrw) {
  SNPS_DEBUG(
    "Writing MR value to MRWBUF with MRaddr=%2d MRdata=%2x interval=%1x rank=%1d tail=%1d",
    hwffcmrw.addr, hwffcmrw.data, hwffcmrw.interval, hwffcmrw.rank, hwffcmrw.tail
  );
  return
    (hwffcmrw.data     <<  0) |
    (hwffcmrw.addr     <<  8) |
    (hwffcmrw.interval << 16) |
    (hwffcmrw.tail     << 19) |
    (hwffcmrw.rank     << 20) ;
}

/**
 *  @brief Generate MR value and program to MRWBUF.
 */
static int gen_mr_program_mrwbuf (
  const SubsysHdlr_t* const cinit_cfg,
  const int pstate,
        int mrwbuf_index,
  const int mr_addr,
  const int per_rank,
  const int per_byte,
  const int last_mr
) {
  // This function is only applicable to LPDDR5 device
  CINIT_ASSERT(cinit_cfg->memCtrlr_m.static_cfg.lpddr5 || cinit_cfg->memCtrlr_m.static_cfg.lpddr5x);
  // per_byte MR must also be per_rank
  if(per_byte) CINIT_ASSERT(per_rank);

  // The set of mode registers of this pstate. Its MR members are described in dwc_ddrctl_cinit_types.h
  const lpddr5_mode_registers_t* const mr = &cinit_cfg->memCtrlr_m.lpddr5_mr[pstate];

  // Flags
  const int dual_rank  = cinit_cfg->spdData_m.num_ranks > 1;
  // Which rank and byte are to be written?
  const int* sdram_width  = cinit_cfg->spdData_m.sdram_width_bits;
  const int rank1byte1    = dual_rank && per_rank && sdram_width[1]==8 && per_byte;
  const int rank0byte1    =                          sdram_width[0]==8 && per_byte;
  const int rank1         = dual_rank && per_rank                                 ;
  const int rank0_or_both = 1                                                     ;
  // Only this case the same value can be written to both rank simultaneously
  const int both_rank     = dual_rank && !per_rank;
  const int mixed_package_and_per_byte = rank1byte1 && !rank0byte1;

  if(mixed_package_and_per_byte) SNPS_DEBUG("Mixed package && per byte MRW detected. Programming order is: rank1byte1 -> rank1byte0 -> rank0");
  SNPS_DEBUG("dr=%0d, r1b1=%0d, r0b1=%0d, r1=%0d, r0=%0d, br=%0d, mppb=%0d",
    dual_rank, rank1byte1, rank0byte1, rank1, rank0_or_both, both_rank, mixed_package_and_per_byte);
  if(cinit_cfg->memCtrlr_m.static_cfg.lpddr_mixed_pkg_en && per_byte) CINIT_ASSERT(mixed_package_and_per_byte);

  // Replicate MRW according to its destination flags
  if(rank1byte1) {
    // If device is x8 and per_byte, write MRW twice. Either of them is with upper byte flag
    HWFFCMRW_t hwffcmrw = get_mrw_entry(mr, mr_addr, 0b10, 0, 1);
    if(!mixed_package_and_per_byte) hwffcmrw.interval = TB2B; // override interval. As NOT mixed package, next MRW is for *rank0* byte1. Interval between writing rank1 and 0 can be shorten
    dwc_ddrctl_cinit_write_hwffc_mrwbuf(pstate, mrwbuf_index++, encode_hwffcmrw(hwffcmrw));
  }
  if(rank0byte1) {
    HWFFCMRW_t hwffcmrw = get_mrw_entry(mr, mr_addr, 0b01, 0, 1);
    dwc_ddrctl_cinit_write_hwffc_mrwbuf(pstate, mrwbuf_index++, encode_hwffcmrw(hwffcmrw));
  }
  if(rank1) {
    HWFFCMRW_t hwffcmrw = get_mrw_entry(mr, mr_addr, 0b10, 0, 0);
    hwffcmrw.interval = TB2B; // override interval. Interval between writing rank1 and 0 can be shorten
    dwc_ddrctl_cinit_write_hwffc_mrwbuf(pstate, mrwbuf_index++, encode_hwffcmrw(hwffcmrw));
  }
  if(rank0_or_both) {
    const int rank = both_rank ? 0b11 : 0b01;
    HWFFCMRW_t hwffcmrw = get_mrw_entry(mr, mr_addr, rank, last_mr, 0);
    dwc_ddrctl_cinit_write_hwffc_mrwbuf(pstate, mrwbuf_index++, encode_hwffcmrw(hwffcmrw));
  }

  return mrwbuf_index;
}
#endif // DDRCTL_HWFFC_EXT_AND_LPDDR5X

/**
 *  @brief method to program HWFFC MRW Buffer
 */
void dwc_ddrctl_cinit_prgm_hwffcmrw(SubsysHdlr_t *cinit_cfg) {
#ifdef DDRCTL_HWFFC_EXT_AND_LPDDR5X
  if(!cinit_cfg->memCtrlr_m.static_cfg.lpddr5 && !cinit_cfg->memCtrlr_m.static_cfg.lpddr5x) {
    SNPS_DEBUG("Skipping MRWBUF initialization. DRAM device is neither LPDDR5 nor LDPDR5X.");
    return;
  }
  for (uint32_t pstate = 0; pstate < cinit_cfg->num_pstates; pstate++) {
    // flags
    const int lpddr5x     = cinit_cfg->memCtrlr_m.static_cfg.lpddr5x;
    // index of MRW Buffer
    int i = 0;

    // Config settings : MR19, 18, 1, 2, 3, 10, 11, 17, 20, 22, 41, 58.  Note : MRW for MR17 is per rank
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 19, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 18, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i,  1, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i,  2, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i,  3, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 10, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 11, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 17, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 20, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 22, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 41, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    if(lpddr5x){
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 58, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0);
    }

    // Only for testing purpose : MR56, MR60
    // insert MRs to exercise MR interval
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 56, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0); // MR56 : SDRAM will ignore. test tVRCG_DISABLE
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 60, HWFFCMRW_ALLRANK, HWFFCMRW_ALLBYTE, 0); // MR60 : SDRAM will ignore. test tVRCG_ENABLE

    // Trained value settings : MR12, 14, 15, 24, 30, 69, 70, 71, 72, 73, 74.
    // Note : All MRWs are for per channel/rank. MR12 is written per byte also.
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 12, HWFFCMRW_PERRANK, HWFFCMRW_PERBYTE, 0); // MR12 : Vref(CA) - per byte
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 14, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0); // MR14 : Vref(DQ)
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 15, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0); // MR15 : Vref(DQ)
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 24, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0); // MR24 : DFE
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 30, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, !lpddr5x); // MR30 : DCA. Last MR if not LP5X
    if(lpddr5x){
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 69, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0); // MR69 : Read DCA
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 70, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0); // MR70-74 : Per-pin DFE
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 71, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 72, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 73, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 0);
    i = gen_mr_program_mrwbuf(cinit_cfg, pstate, i, 74, HWFFCMRW_PERRANK, HWFFCMRW_ALLBYTE, 1); // Last MR
    }

    // check index overrun
    CINIT_ASSERT(i <= DDRCTL_MRWBUF_NUM_PER_FREQ);

    // Only for testing purpose
    // Store unique value at the tail of the MRWBUF pstate block. Used to validate read sequence
    const int TEST_MRW_ADDR = 127;
    HWFFCMRW_t testmrw = (HWFFCMRW_t){.addr=TEST_MRW_ADDR, .interval=TB2B, .rank=0b00, .tail=1, .data=pstate};
    dwc_ddrctl_cinit_write_hwffc_mrwbuf(pstate, DDRCTL_MRWBUF_NUM_PER_FREQ-1, encode_hwffcmrw(testmrw));
  }

#endif // DDRCTL_HWFFC_EXT_AND_LPDDR5X
}
