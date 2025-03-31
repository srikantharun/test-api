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
#include <multicore.h>
#include <thread.h>
#include <pctl_utils.h>
char *arrRef1024 = RANDOM_DATA_1024B;
char *arrInit1024 = INIT_DATA_1024B;

int main() {

testcase_init();

enable_simple_multicore_printf(APU_CORE_5);

// Always unfence the SDMA modules
pctl_enable_module(SDMA_MODULE_0);
pctl_enable_module(SDMA_MODULE_1);

// Always unfence the L2
pctl_enable_l2();

// Start the AICORE and PVE CPUs

// Task description
// ================================
// The task executed has the following command:
// name='task1' resource=['APU'] instance='LP_DMA_APU' type='SNPS_DW' mode='CSR' num_channels=1 channels=[0] source_address=['SYS_SPM_BASE+0x20000'] destination_address=['SYS_SPM_BASE+0x40000'] burst_length=[64] osr=[15] src_xbytesize=[1024] dst_xbytesize=[1024] src_ms=[1] dst_ms=[1] src_xaddrinc=None dst_xaddrinc=None tran_size=None xtype=None fillval=None fillval_mode=None ytype=None src_yrowsize=None dst_yrowsize=None src_yaddrstride=None dst_yaddrstride=None

// Configure the number of channels
// ================================
uint64_t num_channels_0=1;
uint64_t dmac_ch_num_0[] = { 0 };

// Configure the transfer size
// =============================
uint64_t tf_size_0[] = { DATA_SIZE_1024B };

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
uintptr_t src_0[] =  {  (uintptr_t) SYS_SPM_BASE+0x20000  };
uintptr_t dst_0[] =  {  (uintptr_t) SYS_SPM_BASE+0x40000  };

// Initialise source and destination
// ==================================
prepare_loc_array( (char * ) src_0[0], arrRef1024, DATA_SIZE_1024B );
// Execute DMA task
// =============================
test_snps_dma_multi_channel_sel("task1",(snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), num_channels_0, dmac_ch_num_0, src_0, dst_0, ctl_flags_0, cfg_flags_0, tf_size_0, true);

// Perform data check
// =============================
// If the start address is unaligned then the SNPS DMA will only transfer
// blk_size_bytes_dma_u = (CHx_BLOCK_TS.BLOCK_TS * src_single_size_bytes) - Source Unaligned bytes
// when src_single_size_bytes = CHx_CTL.SRC_TR_WIDTH/8

uint64_t src_align_bytes_0[] = { src_0[0] % 8 };

check_mem_snapshot(arrRef1024, (char * ) dst_0[0], 0, DATA_SIZE_1024B, get_memory_region_name(dst_0[0]), src_align_bytes_0[0]);

disable_simple_multicore_printf(APU_CORE_5);

return testcase_finalize();
}

