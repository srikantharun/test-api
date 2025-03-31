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
char *arrRef4096 = RANDOM_DATA_4096B;
char *arrInit4096 = INIT_DATA_4096B;

int main() {


// Task description
// ================================
// The task executed has the following command:
// name='task' resource=['AI0'] instance='HP_DMA_AI0' type='AXE' mode='CSR' num_channels=1 channels=[0] source_address=['AICORE_0_L1_BASE'] destination_address=['AICORE_0_L1_BASE+0x8000'] burst_length=[64] osr=[15] src_xbytesize=[4096] dst_xbytesize=[4096] src_ms=[1] dst_ms=[1] src_xaddrinc=[1] dst_xaddrinc=[1] tran_size=[0] xtype=[1] fillval=None fillval_mode=None ytype=[0] src_yrowsize=[0] dst_yrowsize=[0] src_yaddrstride=[0] dst_yaddrstride=[0]

// Configure the number of channels
// ================================
uint64_t num_channels_0=1;
uint64_t dmac_ch_num_0[] = { 0 };

// Configure the transfer
// =============================
uint64_t src_xbytesize_0[] = { DATA_SIZE_4096B };
uint64_t dst_xbytesize_0[] = { DATA_SIZE_4096B };

uint64_t src_xaddrinc_0[] = {  1  };
uint64_t dst_xaddrinc_0[] = {  1  };

uint64_t tran_size_0[] = {  0  };
uint64_t xtype_0[] = {  1  };

uint64_t fillval_mode_0[] = {};
uint64_t fillval_0[] = {};
uint64_t src_burstlen_0[] = {  64  };
uint64_t dst_burstlen_0[] = {  64  };

uint64_t src_osr_lmt_0[] = {  15  };
uint64_t dst_osr_lmt_0[] = {  15  };

uint64_t ytype_0[] = {  0  };

uint64_t src_yrowsize_0[] = { };
uint64_t dst_yrowsize_0[] = { };

uint64_t src_yaddrstride_0[] = { };
uint64_t dst_yaddrstride_0[] = { };
uint64_t src_ms_0[] = {  1  };
uint64_t dst_ms_0[] = {  1  };
uint64_t irq_en_0[] = {1};
uint64_t irq_clr_0[] = {1};

// Configure the SRC and DST
// =============================
uintptr_t src_0[] =  {  (uintptr_t) AICORE_0_L1_BASE  };
uintptr_t dst_0[] =  {  (uintptr_t) AICORE_0_L1_BASE+0x8000  };

// Configure the DMA config
// =============================
axe_dma_config config_0 = {
     .dmac = (axe_dma_regs *)get_dma_base_addr("HP_DMA_AI0"),
     .num_channels =num_channels_0,
     .dmac_ch_num =  dmac_ch_num_0,
     .src = src_0,
     .dst = dst_0,
     .src_xbytesize = src_xbytesize_0,
     .dst_xbytesize = dst_xbytesize_0,
     .src_xaddrinc=src_xaddrinc_0,
     .dst_xaddrinc=dst_xaddrinc_0,
     .tran_size= tran_size_0,
     .xtype=xtype_0,
     .fillval_mode=fillval_mode_0,
     .fillval=fillval_0,
     .ytype=ytype_0,
     .src_yrowsize= src_yrowsize_0,
     .dst_yrowsize= dst_yrowsize_0,
     .src_yaddrstride=src_yaddrstride_0,
     .dst_yaddrstride=dst_yaddrstride_0,
     .src_burstlen=src_burstlen_0,
     .dst_burstlen=dst_burstlen_0,
     .src_osr_lmt=src_osr_lmt_0,
     .dst_osr_lmt=dst_osr_lmt_0,
     .src_ms= src_ms_0,
     .dst_ms= dst_ms_0,
     .irq_en= irq_en_0,
     .irq_clr= irq_clr_0
};


// Initialise source and destination
// ==================================
prepare_loc_array( (char * ) src_0[0], arrRef4096, DATA_SIZE_4096B );
// Execute DMA task
// =============================

test_axe_dma_multi_channel_sel("task", &config_0, true);

// Perform data check
// =============================
check_mem_snapshot(arrRef4096, (char * ) dst_0[0], 0, DATA_SIZE_4096B, get_memory_region_name(dst_0[0]),0);

return testcase_finalize();
}

