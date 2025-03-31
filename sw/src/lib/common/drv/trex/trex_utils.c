// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "trex_utils.h"
#include <printf.h>
#include "memories.h"
#include "dmas.h"
/**************************************************************************
 * Comment on DMA tests:
 *
 * Overview:

 * Some helpers and variables are shared for all tests.
 *************************************************************************/

// /**************************************************************************
//  * test_snps_dma_multi_channel_sel
//  *************************************************************************/
void test_snps_dma_multi_channel_sel(char* task_name, snps_dmac_regs* dmac, uint64_t num_channels, uint64_t dmac_ch_num[],
                                uintptr_t src[], uintptr_t dst[],
                                uint64_t ctl_flags[], uint64_t cfg_flags[],
                                uint64_t tf_size[],bool verbose) {
    uint64_t cycles;
    uint64_t init_cycles;
    uint64_t chan_config_cycles[num_channels];
    uint64_t chan_enable_cycles[num_channels];
    uint64_t chan_start_cycles[num_channels];
    uint64_t chan_transfer_cycles[num_channels];


    uint64_t data_size[num_channels];
    snps_dma_channel chan[num_channels];  // Static array of snps_dma_channel structs for all channels


    cycles = read_csr(cycle);
    snps_dma_init_dmac(dmac, 0);
    init_cycles = read_csr(cycle) - cycles -1;


    // Set up each channel
    for (uint64_t i = 0; i < num_channels; i++) {
        // Calculate data sizes for each channel
        data_size[i] = (tf_size[i] / DMAC_TR_WIDTH - 1);

        cycles = read_csr(cycle);
        snps_dma_init_channel(&chan[dmac_ch_num[i]], dmac, dmac_ch_num[i]);
        snps_dma_configure_channel(&chan[dmac_ch_num[i]], SNPS_SINGLE_BLOCK, cfg_flags[i]);
        snps_dma_configure_block_transfer(&chan[dmac_ch_num[i]], (uintptr_t)src[i], (uintptr_t)dst[i], data_size[i], ctl_flags[i] | SNPS_DMA_CTL_TR_WIDTH(512, 512));
        chan_config_cycles[i]= read_csr(cycle) - cycles -1;
    }

    // Enable all channels
    for (uint64_t i = 0; i < num_channels; i++) {
        cycles = read_csr(cycle);
        snps_dma_enable_channel(&chan[dmac_ch_num[i]]);
        chan_start_cycles[i]=read_csr(cycle);
        chan_enable_cycles[i]=read_csr(cycle) - cycles -1;
    }

    int channel_done[num_channels];
    for (uint64_t i = 0; i < num_channels; i++) {
        channel_done[i] = 0;
    }

    // Wait until all channels are done
    while (1) {
        int all_done = 1;
        for (uint64_t i = 0; i < num_channels; i++) {
            if (snps_dma_channel_enabled(&chan[dmac_ch_num[i]])) {
                all_done = 0;
                break;
            }
            else if (!channel_done[i] && !snps_dma_channel_enabled(&chan[dmac_ch_num[i]])) {
                chan_transfer_cycles[i]=read_csr(cycle) - chan_start_cycles[i] -1;
                channel_done[i] = snps_dma_channel_enabled(&chan[dmac_ch_num[i]]);
            }

        }
        if (all_done) break;
    }

    // Check the status of each channel
    for (uint64_t i = 0; i < num_channels; i++) {
        CHECK_TRUE(chan[dmac_ch_num[i]].regs->intstatus == CH_INTSTATUS_DMA_TFR_DONE);
        CHECK_TRUE(chan[dmac_ch_num[i]].regs->status == data_size[i] + 1);
    }

    if (verbose) {
        printf("\n================ Test Summary ================\n");
        for (uint64_t i = 0; i < num_channels; i++) {
            printf("Task: %s, DMA: %s, channel %10ld, SRC: %s, DST: %s, Size: %10ld, Init cycles: %10ld, config cycles: %10ld, transfer cycles: %10ld, expected cycles: %10ld \n, ",
            task_name, get_dma_name((uintptr_t)dmac), dmac_ch_num[i],get_memory_region_name(src[i]),get_memory_region_name(dst[i]),tf_size[i],
            init_cycles,chan_config_cycles[i],chan_transfer_cycles[i],0);
        }
        printf("\n=============================================\n");
    }
}

// /**************************************************************************
//  * test_axe_dma_multi_channel_sel
//  *************************************************************************/
void test_axe_dma_multi_channel_sel(char* task_name, axe_dma_config* config, bool verbose) {
    uint64_t cycles;
    uint64_t init_cycles;
    uint64_t chan_config_cycles[config->num_channels];
    uint64_t chan_enable_cycles[config->num_channels];
    uint64_t chan_start_cycles[config->num_channels];
    uint64_t chan_transfer_cycles[config->num_channels];

    axe_dma_channel chan[config->num_channels];  // Static array of dma_channel structs for all channels
    uint64_t tf_size[config->num_channels];
    uint64_t data_size[config->num_channels];

    cycles = read_csr(cycle);
    init_cycles = read_csr(cycle) - cycles -1;

    // Set up each channel
    for (uint64_t i = 0; i < config->num_channels; i++) {
        // Calculate data sizes for each channel
        tf_size[i] = config->dst_xbytesize[i];
        data_size[i] = (tf_size[i] / DMA_PARAM_AXI_DATAW_BYTES - 1);

        cycles = read_csr(cycle);
        axe_dma_init_channel(&chan[config->dmac_ch_num[i]], config->dmac, config->dmac_ch_num[i]);

        if (config->ytype[i] == 0) {
          axe_dma_1d_config config_1d =  {
             .chan =&chan[config->dmac_ch_num[i]],
             .src_addr=config->src[i],
             .dst_addr=config->dst[i],
             .src_xbytesize=config->src_xbytesize[i],
             .dst_xbytesize=config->dst_xbytesize[i],
             .src_xaddrinc=config->src_xaddrinc[i],
             .dst_xaddrinc=config->dst_xaddrinc[i],
             .tran_size=config->tran_size[i],
             .xtype=config->xtype[i],
             .fillval_mode=config->fillval_mode[i],
             .fillval=config->fillval[i],
             .src_burstlen=config->src_burstlen[i],
             .dst_burstlen=config->dst_burstlen[i]
          };

          axe_dma_configure_1d_transfer(&config_1d); }
        else {

            axe_dma_2d_config config_2d =  {
             .chan=&chan[config->dmac_ch_num[i]],
             .src_addr=config->src[i],
             .dst_addr=config->dst[i],
             .src_xbytesize=config->src_xbytesize[i],
             .dst_xbytesize=config->dst_xbytesize[i],
             .src_xaddrinc=config->src_xaddrinc[i],
             .dst_xaddrinc=config->dst_xaddrinc[i],
             .tran_size=config->tran_size[i],
             .xtype=config->xtype[i],
             .fillval_mode=config->fillval_mode[i],
             .fillval=config->fillval[i],
             .src_burstlen=config->src_burstlen[i],
             .dst_burstlen=config->dst_burstlen[i],
             .ytype=config->ytype[i],
             .src_yrowsize=config->src_yrowsize[i],
             .dst_yrowsize=config->dst_yrowsize[i],
             .src_yaddrstride=config->src_yaddrstride[i],
             .dst_yaddrstride=config->dst_yaddrstride[i]
          };

           axe_dma_configure_2d_transfer(&config_2d);
        }
        chan_config_cycles[i]= read_csr(cycle) - cycles -1;
    }

    // Enable all channels
    for (uint64_t i = 0; i < config->num_channels; i++) {
        cycles = read_csr(cycle);

        axe_dma_ctrl_config config_ctrl =  {
             .chan=&chan[config->dmac_ch_num[i]],
             .src_ms=config->src_ms[i],
             .dst_ms=config->dst_ms[i],
             .irq_en=config->irq_en[i],
             .irq_clr=config->irq_clr[i],
             .src_osr_lmt=config->src_osr_lmt[i],
             .dst_osr_lmt=config->dst_osr_lmt[i]
          };

        axe_dma_enable_channel(&config_ctrl);
        chan_start_cycles[i]=read_csr(cycle);
        chan_enable_cycles[i]=read_csr(cycle) - cycles -1;
    }

    int channel_done[config->num_channels];
    for (uint64_t i = 0; i < config->num_channels; i++) {
        channel_done[i] = 0;
    }

    // Wait until all channels are done
    while (1) {
        int all_done = 1;
        for (uint64_t i = 0; i < config->num_channels; i++) {
            if (axe_dma_channel_enabled(&chan[config->dmac_ch_num[i]])) {
                all_done = 0;
                break;
            }
            else if (!channel_done[i] && !axe_dma_channel_enabled(&chan[config->dmac_ch_num[i]])) {
                chan_transfer_cycles[i]=read_csr(cycle) - chan_start_cycles[i] -1;
                channel_done[i] = axe_dma_channel_enabled(&chan[config->dmac_ch_num[i]]);
            }

        }
        if (all_done) break;
    }

    // Check the status of each channel
    for (uint64_t i = 0; i < config->num_channels; i++) {
        CHECK_TRUE(chan[config->dmac_ch_num[i]].regs->ch_status == 0);
        // CHECK_TRUE(chan[dmac_ch_num[i]].regs->status == data_size[i] + 1);
    }

    if (verbose) {
        printf("\n================ Test Summary ================\n");
        for (uint64_t i = 0; i < config->num_channels; i++) {
            printf("Task: %s, DMA: %s, channel %10ld, SRC: %s, DST: %s, Size: %10ld, Init cycles: %10ld, config cycles: %10ld, transfer cycles: %10ld, expected cycles: %10ld \n, ",
            task_name, get_dma_name((uintptr_t)config->dmac), config->dmac_ch_num[i],get_memory_region_name(config->src[i]),get_memory_region_name(config->dst[i]),tf_size[i],
            init_cycles,chan_config_cycles[i],chan_transfer_cycles[i],0);
        }
        printf("\n=============================================\n");

    }
}

// write memory area with reference data
void prepare_loc_array(char* loc, const char* arr, size_t data_size) {
    memcpy(loc, arr, data_size);
}

// Compare memory and provide useful log. Support both aligned and unaligned
void check_mem_snapshot(const char* x, const char* y, int offset, int n_bytes, const char* msg, uint64_t src_align_bytes) {

    int mem_equal = 1;
    int n_prints_left = 2; // Control number of blocks printed in case of error here

    // Determine if alignment is less than 8 bytes
    int align_x = (uintptr_t)(x + offset) % 8;
    int align_y = (uintptr_t)(y + offset) % 8;
    int unaligned_access = (align_x != 0 || align_y != 0);
    // In case the SNPS DMA is used then the unaligned access will result into less bytes than the configured ones
    // due to the alignment difference. Hence we need to reduce the check only to the bytes transferred
    int end_offset =offset + n_bytes - src_align_bytes;

    if (unaligned_access) {

        // Use byte-wise comparison for unaligned memory
        for (; offset < end_offset; offset++) {
            uint8_t bx = *(uint8_t*)(x + offset);
            uint8_t by = *(uint8_t*)(y + offset);
            if (bx != by) {
                if (mem_equal) {
                    printf("[CHECK FAILED] Memory different (%s)\n", msg);
                    mem_equal = 0;
                }
                if (n_prints_left) {
                    printf(" | %5d : %02x -> %02x\n", offset, bx, by);
                    n_prints_left--;
                }
            }
        }
    } else {
        int end_offset = offset + n_bytes;
        // Use 8-byte comparison for aligned memory
        while (offset < end_offset) {
            uint64_t ix = *(uint64_t*)(x + offset);
            uint64_t iy = *(uint64_t*)(y + offset);
            if (ix != iy) {
                if (mem_equal) {
                    printf("[CHECK FAILED] Memory different (%s)\n", msg);
                    mem_equal = 0;
                }
                if (n_prints_left) {
                    printf(" | %5d : %016lx -> %016lx\n", offset, ix, iy);
                    n_prints_left--;
                }
            }
            offset += 8;
        }
    }

    CHECK_TRUE(mem_equal,"[CHECK FAILED] Memory is not equal (%s)\n", msg);

}



