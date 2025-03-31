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
char *arrRef512 = RANDOM_DATA_512B;
char *arrInit512 = INIT_DATA_512B;

int main() {


// Task description
// ================================
// The task executed has the following command:
// name='task' resource=['PVE1'] instance='HP_DMA0_PVE1' type='AXE' mode='CSR' num_channels=4 channels=[0, 1, 2, 3] source_address=['L2_MODULE_0_BASE', 'L2_MODULE_1_BASE', 'L2_MODULE_2_BASE', 'L2_MODULE_3_BASE'] destination_address=['L2_MODULE_4_BASE', 'L2_MODULE_5_BASE', 'L2_MODULE_6_BASE', 'L2_MODULE_7_BASE'] burst_length=[64, 64, 64, 64] osr=[15, 15, 15, 15] src_xbytesize=[512, 512, 512, 512] dst_xbytesize=[512, 512, 512, 512] src_ms=[0, 0, 1, 1] dst_ms=[0, 0, 1, 1] src_xaddrinc=[1, 1, 1, 1] dst_xaddrinc=[1, 1, 1, 1] tran_size=[0, 0, 0, 0] xtype=[1, 1, 1, 1] fillval=None fillval_mode=None ytype=[0, 0, 0, 0] src_yrowsize=[0, 0, 0, 0] dst_yrowsize=[0, 0, 0, 0] src_yaddrstride=[0, 0, 0, 0] dst_yaddrstride=[0, 0, 0, 0]

// Configure the number of channels
// ================================
uint64_t num_channels_0=4;
uint64_t dmac_ch_num_0[] = { 0, 1, 2, 3 };

// Configure the transfer
// =============================
uint64_t src_xbytesize_0[] = { DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B };
uint64_t dst_xbytesize_0[] = { DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B };

uint64_t src_xaddrinc_0[] = {  1 ,  1 ,  1 ,  1  };
uint64_t dst_xaddrinc_0[] = {  1 ,  1 ,  1 ,  1  };

uint64_t tran_size_0[] = {  0 ,  0 ,  0 ,  0  };
uint64_t xtype_0[] = {  1 ,  1 ,  1 ,  1  };

uint64_t fillval_mode_0[] = {};
uint64_t fillval_0[] = {};
uint64_t src_burstlen_0[] = {  64 ,  64 ,  64 ,  64  };
uint64_t dst_burstlen_0[] = {  64 ,  64 ,  64 ,  64  };

uint64_t src_osr_lmt_0[] = {  15 ,  15 ,  15 ,  15  };
uint64_t dst_osr_lmt_0[] = {  15 ,  15 ,  15 ,  15  };

uint64_t ytype_0[] = {  0 ,  0 ,  0 ,  0  };

uint64_t src_yrowsize_0[] = { };
uint64_t dst_yrowsize_0[] = { };

uint64_t src_yaddrstride_0[] = { };
uint64_t dst_yaddrstride_0[] = { };
uint64_t src_ms_0[] = {  0 ,  0 ,  1 ,  1  };
uint64_t dst_ms_0[] = {  0 ,  0 ,  1 ,  1  };
uint64_t irq_en_0[] = {1};
uint64_t irq_clr_0[] = {1};

// Configure the SRC and DST
// =============================
uintptr_t src_0[] =  {  (uintptr_t) L2_MODULE_0_BASE ,  (uintptr_t) L2_MODULE_1_BASE ,  (uintptr_t) L2_MODULE_2_BASE ,  (uintptr_t) L2_MODULE_3_BASE  };
uintptr_t dst_0[] =  {  (uintptr_t) L2_MODULE_4_BASE ,  (uintptr_t) L2_MODULE_5_BASE ,  (uintptr_t) L2_MODULE_6_BASE ,  (uintptr_t) L2_MODULE_7_BASE  };

// Configure the DMA config
// =============================
axe_dma_config config_0 = {
     .dmac = (axe_dma_regs *)get_dma_base_addr("HP_DMA0_PVE1"),
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
prepare_loc_array( (char * ) src_0[0], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_0[1], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_0[2], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_0[3], arrRef512, DATA_SIZE_512B );
// Execute DMA task
// =============================

test_axe_dma_multi_channel_sel("task", &config_0, true);

// Perform data check
// =============================
check_mem_snapshot(arrRef512, (char * ) dst_0[0], 0, DATA_SIZE_512B, get_memory_region_name(dst_0[0]),0);
check_mem_snapshot(arrRef512, (char * ) dst_0[1], 0, DATA_SIZE_512B, get_memory_region_name(dst_0[1]),0);
check_mem_snapshot(arrRef512, (char * ) dst_0[2], 0, DATA_SIZE_512B, get_memory_region_name(dst_0[2]),0);
check_mem_snapshot(arrRef512, (char * ) dst_0[3], 0, DATA_SIZE_512B, get_memory_region_name(dst_0[3]),0);


// Task description
// ================================
// The task executed has the following command:
// name='task' resource=['PVE1'] instance='HP_DMA1_PVE1' type='AXE' mode='CSR' num_channels=4 channels=[0, 1, 2, 3] source_address=['L2_MODULE_0_BASE', 'L2_MODULE_1_BASE', 'L2_MODULE_2_BASE', 'L2_MODULE_3_BASE'] destination_address=['L2_MODULE_4_BASE', 'L2_MODULE_5_BASE', 'L2_MODULE_6_BASE', 'L2_MODULE_7_BASE'] burst_length=[64, 64, 64, 64] osr=[15, 15, 15, 15] src_xbytesize=[512, 512, 512, 512] dst_xbytesize=[512, 512, 512, 512] src_ms=[0, 0, 1, 1] dst_ms=[0, 0, 1, 1] src_xaddrinc=[1, 1, 1, 1] dst_xaddrinc=[1, 1, 1, 1] tran_size=[0, 0, 0, 0] xtype=[1, 1, 1, 1] fillval=None fillval_mode=None ytype=[0, 0, 0, 0] src_yrowsize=[0, 0, 0, 0] dst_yrowsize=[0, 0, 0, 0] src_yaddrstride=[0, 0, 0, 0] dst_yaddrstride=[0, 0, 0, 0]

// Configure the number of channels
// ================================
uint64_t num_channels_1=4;
uint64_t dmac_ch_num_1[] = { 0, 1, 2, 3 };

// Configure the transfer
// =============================
uint64_t src_xbytesize_1[] = { DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B };
uint64_t dst_xbytesize_1[] = { DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B, DATA_SIZE_512B };

uint64_t src_xaddrinc_1[] = {  1 ,  1 ,  1 ,  1  };
uint64_t dst_xaddrinc_1[] = {  1 ,  1 ,  1 ,  1  };

uint64_t tran_size_1[] = {  0 ,  0 ,  0 ,  0  };
uint64_t xtype_1[] = {  1 ,  1 ,  1 ,  1  };

uint64_t fillval_mode_1[] = {};
uint64_t fillval_1[] = {};
uint64_t src_burstlen_1[] = {  64 ,  64 ,  64 ,  64  };
uint64_t dst_burstlen_1[] = {  64 ,  64 ,  64 ,  64  };

uint64_t src_osr_lmt_1[] = {  15 ,  15 ,  15 ,  15  };
uint64_t dst_osr_lmt_1[] = {  15 ,  15 ,  15 ,  15  };

uint64_t ytype_1[] = {  0 ,  0 ,  0 ,  0  };

uint64_t src_yrowsize_1[] = { };
uint64_t dst_yrowsize_1[] = { };

uint64_t src_yaddrstride_1[] = { };
uint64_t dst_yaddrstride_1[] = { };
uint64_t src_ms_1[] = {  0 ,  0 ,  1 ,  1  };
uint64_t dst_ms_1[] = {  0 ,  0 ,  1 ,  1  };
uint64_t irq_en_1[] = {1};
uint64_t irq_clr_1[] = {1};

// Configure the SRC and DST
// =============================
uintptr_t src_1[] =  {  (uintptr_t) L2_MODULE_0_BASE ,  (uintptr_t) L2_MODULE_1_BASE ,  (uintptr_t) L2_MODULE_2_BASE ,  (uintptr_t) L2_MODULE_3_BASE  };
uintptr_t dst_1[] =  {  (uintptr_t) L2_MODULE_4_BASE ,  (uintptr_t) L2_MODULE_5_BASE ,  (uintptr_t) L2_MODULE_6_BASE ,  (uintptr_t) L2_MODULE_7_BASE  };

// Configure the DMA config
// =============================
axe_dma_config config_1 = {
     .dmac = (axe_dma_regs *)get_dma_base_addr("HP_DMA1_PVE1"),
     .num_channels =num_channels_1,
     .dmac_ch_num =  dmac_ch_num_1,
     .src = src_1,
     .dst = dst_1,
     .src_xbytesize = src_xbytesize_1,
     .dst_xbytesize = dst_xbytesize_1,
     .src_xaddrinc=src_xaddrinc_1,
     .dst_xaddrinc=dst_xaddrinc_1,
     .tran_size= tran_size_1,
     .xtype=xtype_1,
     .fillval_mode=fillval_mode_1,
     .fillval=fillval_1,
     .ytype=ytype_1,
     .src_yrowsize= src_yrowsize_1,
     .dst_yrowsize= dst_yrowsize_1,
     .src_yaddrstride=src_yaddrstride_1,
     .dst_yaddrstride=dst_yaddrstride_1,
     .src_burstlen=src_burstlen_1,
     .dst_burstlen=dst_burstlen_1,
     .src_osr_lmt=src_osr_lmt_1,
     .dst_osr_lmt=dst_osr_lmt_1,
     .src_ms= src_ms_1,
     .dst_ms= dst_ms_1,
     .irq_en= irq_en_1,
     .irq_clr= irq_clr_1
};


// Initialise source and destination
// ==================================
prepare_loc_array( (char * ) src_1[0], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_1[1], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_1[2], arrRef512, DATA_SIZE_512B );
prepare_loc_array( (char * ) src_1[3], arrRef512, DATA_SIZE_512B );
// Execute DMA task
// =============================

test_axe_dma_multi_channel_sel("task", &config_1, true);

// Perform data check
// =============================
check_mem_snapshot(arrRef512, (char * ) dst_1[0], 0, DATA_SIZE_512B, get_memory_region_name(dst_1[0]),0);
check_mem_snapshot(arrRef512, (char * ) dst_1[1], 0, DATA_SIZE_512B, get_memory_region_name(dst_1[1]),0);
check_mem_snapshot(arrRef512, (char * ) dst_1[2], 0, DATA_SIZE_512B, get_memory_region_name(dst_1[2]),0);
check_mem_snapshot(arrRef512, (char * ) dst_1[3], 0, DATA_SIZE_512B, get_memory_region_name(dst_1[3]),0);

return testcase_finalize();
}

