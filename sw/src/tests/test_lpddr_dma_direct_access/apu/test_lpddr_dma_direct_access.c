// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Rodrigo Borges <rodrigo.borges@axelera.ai>
//
// Description: Generate a 64 byte write and read transfer to LPDDR0 (graph 0) for debug porpuses.

#include <lpddr/drv_lpddr.h>
#include <trex/generated_data.h>
#include <trex/trex_utils.h>

char *arrRef1024 = RANDOM_DATA_1024B;

void dma_access(uint64_t src_address, uint64_t dst_address) {
  // shamelessly stolen from TREX
  uint64_t tf_size_0[] = {64}; // 64 byte transfer
  uint64_t num_channels_0 = 1;
  uint64_t dmac_ch_num_0[] = {0};
  uint64_t cfg_flags_0[] = {CH_CFG_SRC_OSR_LMT(15) | CH_CFG_DST_OSR_LMT(15) | CH_CFG_WR_UID(4) |
                            CH_CFG_RD_UID(4)};
  uint64_t ctl_flags_0[] = {CH_CTL_AWLEN_EN | CH_CTL_ARLEN_EN | CH_CTL_AWLEN(64) |
                            CH_CTL_ARLEN(64)};
  uintptr_t src_0[] = {(uintptr_t)src_address};
  uintptr_t dst_0[] = {(uintptr_t)dst_address};

  test_snps_dma_multi_channel_sel("LPDDR 64 bytes",(snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), num_channels_0, dmac_ch_num_0, src_0, dst_0,
                                  ctl_flags_0, cfg_flags_0, tf_size_0, true);
}


int main(void) {
  testcase_init();

  #ifdef REAL_LPDDR
    lpddrSubsystemInit(false);
  #endif

  printf("Initialize first 1024 bytes of LPDDR1\n");
  prepare_loc_array( (char * ) DDR_1_BASE, arrRef1024, DATA_SIZE_1024B );

  printf("DMA access of 64 bytes from LPDDR1 to LPDDR0\n");
  dma_access(DDR_1_BASE, DDR_0_BASE);

  printf("DMA access of 64 bytes from LPDDR0 to LPDDR1 + 0x400 (uninitialized portion of LPDDR1)\n");
  dma_access(DDR_0_BASE, DDR_1_BASE + 0x400);

  // Perform data check
  // =============================
  printf("Starting memory compare for first 64 bytes of LPDDR1 + 0x400\n");
  check_mem_snapshot(arrRef1024, (char * ) DDR_1_BASE + 0x400, 0, 64, "LPDDR1 + 0x400", 0);

  return testcase_finalize();
}
