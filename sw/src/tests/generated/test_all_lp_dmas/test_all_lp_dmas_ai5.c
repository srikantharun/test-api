// AUTO GENERATED, DON'T MANUALLY EDIT!!
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Automatic generated test file
// Owner: scripts/trex

#include <trex/trex_utils.h>
#include <testutils.h>
#include <printf.h>
#include <memutils.h>
#include <trex/generated_data.h>
#include <platform.h>
char *arrRef16384 = RANDOM_DATA_16384B;
char *arrInit16384 = INIT_DATA_16384B;

int main() {


// Task description
// ================================
// The task executed has the following command:
// name='task_ai5' resource=['AI5'] instance='LP_DMA_AI5' type='SNPS_DW' mode='CSR' num_channels=1 channels=[0] source_address=['SYS_SPM_BASE'] destination_address=['AICORE_5_SPM_BASE+0x20000'] burst_length=[64] osr=[15] src_xbytesize=[16384] dst_xbytesize=[16384] src_ms=[0] dst_ms=[0] src_xaddrinc=None dst_xaddrinc=None tran_size=None xtype=None fillval=None fillval_mode=None ytype=None src_yrowsize=None dst_yrowsize=None src_yaddrstride=None dst_yaddrstride=None

// Configure the number of channels
// ================================
uint64_t num_channels_0=1;
uint64_t dmac_ch_num_0[] = { 0 };

// Configure the transfer size
// =============================
uint64_t tf_size_0[] = { DATA_SIZE_16384B };

// Configure the CH_CFG register
// =============================
// Allows changing the number of outstanding transactions: Allowed values: 0-15  for 1 to 6 transactions
// Allows enabling multiple UID for the transaction for RD/WR channels : set to the max UID
uint64_t cfg_flags_0[] = { CH_CFG_SRC_OSR_LMT(15)|CH_CFG_DST_OSR_LMT(15)|CH_CFG_WR_UID(4)|CH_CFG_RD_UID(4)  };

// Configure the CH_CTL register
// =============================
uint64_t ctl_flags_0[] = { CH_CTL_AWLEN_EN|CH_CTL_ARLEN_EN|CH_CTL_AWLEN(64)|CH_CTL_ARLEN(64) };

// Configure the SRC and DST
// =============================
uintptr_t src_0[] =  {  (uintptr_t) SYS_SPM_BASE  };
uintptr_t dst_0[] =  {  (uintptr_t) AICORE_5_SPM_BASE+0x20000  };

// Initialise source and destination
// ==================================
prepare_loc_array( (char * ) src_0[0], arrRef16384, DATA_SIZE_16384B );
// Execute DMA task
// =============================
test_snps_dma_multi_channel_sel("task_ai5",(snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI5"), num_channels_0, dmac_ch_num_0, src_0, dst_0, ctl_flags_0, cfg_flags_0, tf_size_0, true);

// Perform data check
// =============================
// If the start address is unaligned then the SNPS DMA will only transfer
// blk_size_bytes_dma_u = (CHx_BLOCK_TS.BLOCK_TS * src_single_size_bytes) - Source Unaligned bytes
// when src_single_size_bytes = CHx_CTL.SRC_TR_WIDTH/8

uint64_t src_align_bytes_0[] = { src_0[0] % 8 };

check_mem_snapshot(arrRef16384, (char * ) dst_0[0], 0, DATA_SIZE_16384B, get_memory_region_name(dst_0[0]), src_align_bytes_0[0]);

return testcase_finalize();
}

