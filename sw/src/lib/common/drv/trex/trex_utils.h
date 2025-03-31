// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#ifndef TREX_TEST_UTILS_H
#define TREX_TEST_UTILS_H

// includes used for all tests

#include <testutils.h>
#include <dma/snps/drv_snps_dma.h>
#include <dma/axe/drv_axe_dma.h>
#include "dmas.h"
#include "memories.h"

typedef struct {
    axe_dma_regs* dmac;
    uint64_t num_channels;
    uint64_t* dmac_ch_num;
    uintptr_t* src;
    uintptr_t* dst;
    uint64_t* src_xbytesize;
    uint64_t* dst_xbytesize;
    uint64_t* src_xaddrinc;
    uint64_t* dst_xaddrinc;
    uint64_t* tran_size;
    uint64_t* xtype;
    uint64_t* fillval_mode;
    uint64_t* fillval;
    uint64_t* ytype;
    uint64_t* src_yrowsize;
    uint64_t* dst_yrowsize;
    uint64_t* src_yaddrstride;
    uint64_t* dst_yaddrstride;
    uint64_t* src_burstlen;
    uint64_t* dst_burstlen;
    uint64_t* src_osr_lmt;
    uint64_t* dst_osr_lmt;
    uint64_t* src_ms;
    uint64_t* dst_ms;
    uint64_t* irq_en;
    uint64_t* irq_clr;
} axe_dma_config;

void test_snps_dma_multi_channel_sel(char* task_name, snps_dmac_regs* dmac, uint64_t num_channels, uint64_t dmac_ch_num[], uintptr_t src[], uintptr_t dst[], uint64_t ctl_flags[], uint64_t cfg_flags[], uint64_t tf_size[], bool verbose);
void test_axe_dma_multi_channel_sel(char* task_name, axe_dma_config* config , bool verbose);

void prepare_loc_array(char* loc, const char* arr, size_t data_size);
void check_mem_snapshot(const char* x, const char* y, int offset, int n_bytes, const char* msg, uint64_t src_align_bytes);



#endif  //#ifndef TREX_TEST_UTILS_H
