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


#include "dwc_ddrctl_phy_training.h"
#include "dwc_ddrctl_cinit_common_sequences.h"
#include "dwc_ddrctl_cinit_ddr_sequences.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_sequences_utils.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_phy_training_common.h"
#include "physetup.h"
#include "cinit_status.h"
#include "phy/sinit_phy_types.h"
#include "phy/ddr54/sinit_ddrphy54_regmap.h"

// TODO: Known items for discussion
// Possible issues with multiple frequencies
// Correct source for the DDR4_PHY_CDD_BASE_ADDR and DDR4_TRAIN_DATA_SIZE configurations

#ifdef DDRCTL_DDR

#define DDR4_PHY_CDD_BASE_ADDR ((DDR54_PHY_BLOCK_UCTL_MEMORY) + 0x8012)

#define MAX_SUPPORTED_RANKS  4

#ifdef CINIT_DDR4

typedef enum ddr4_train_type_e {
    CDD_WRITE_READ = 0,
    CDD_READ_WRITE = 1,
    CDD_WRITE_WRITE = 2,
    CDD_READ_READ = 3
} ddr4_train_type_t;

typedef enum ddr4_rank_type_e {
    CDD_SAME_RANK,
    CDD_DIFF_RANK,
    CDD_ALL_RANK,
} ddr4r_rank_type_t;

typedef struct ddr4_train_data_process_s {
    int8_t critical_delay[4][MAX_SUPPORTED_RANKS][MAX_SUPPORTED_RANKS];
} ddr4_train_data_process_t;

/**
 * @brief Read the critical delay difference timings results from the PHY train
 *
 * @param train_data struture to store the train data
 */
static void read_ccd_train_data(ddr4_train_data_process_t *train_data){
    uint16_t cdd_num;
    uint16_t high_low;
    uint16_t reg_cdd_data;
    int8_t cdd_data[DDR4_TRAIN_DATA_SIZE][2];
    int8_t i, j, type;

	/** - l_n_phy_cdd_high[0] & l_n_phy_cdd_low[0]*/
	/** - addr-0x:  58012 |58013 |58014 |58015 |58016 |58017 ||58018 |58019 |5801a |5801b |5801c |5801d |5801e |5801f |58020 ||58021 |58022 |58023 |58024 |58025 ||58026 |58027 |58028 |58029 |5802a |5802b |5802c |5802d |5802e |*/
	/** - index:    0     |1     |2     |3     |4     |5     ||6     |7     |8     |9     |10    |11    ||12    |13    |14    |15    |16    |17    |18    |19    ||20    |21    |22    |23    |24    |25    |26    |27    |28    |*/
  /** - cdd_high: RR_3_2|RR_3_0|RR_2_1|RR_1_3|RR_1_0|RR_0_2||WW_3_2|WW_3_0|WW_2_1|WW_1_3|WW_1_0|WW_0_2||RW_3_3|RW_3_1|RW_2_3|RW_2_1|RW_1_3|RW_1_1|RW_0_3|RW_0_1||WR_3_3|WR_3_1|WR_2_3|WR_2_1|WR_1_3|WR_1_1|WR_0_3|WR_0_1|      |*/
	/** - cdd_low:        |RR_3_1|RR_2_3|RR_2_0|RR_1_2|RR_0_3| RR_0_1|WW_3_1|WW_2_3|WW_2_0|WW_1_2|WW_0_3| WW_0_1|RW_3_2|RW_3_0|RW_2_2|RW_2_0|RW_1_2|RW_1_0|RW_0_2| RW_0_0|WR_3_2|WR_3_0|WR_2_2|WR_2_0|WR_1_2|WR_1_0|WR_0_2|WR_0_0|*/

    // For each CDD
    for (cdd_num = 0; cdd_num < DDR4_TRAIN_DATA_SIZE; cdd_num++){
        // read CDD
        reg_cdd_data = physetup_io_read16(DDR4_PHY_CDD_BASE_ADDR + cdd_num);

        // load CDD value into a arrays separating low and high
        cdd_data[cdd_num][0] = (int8_t) (reg_cdd_data & 0x00FF);
        cdd_data[cdd_num][1] = (int8_t) ((reg_cdd_data >> 8) & 0x00FF);
    }

    /**
     *  To fill in the train data in a array in a easy and compact way we follow the registers in the inverse order
     *  Reach to the next sequence:
     *      Index 28 Low  WR_0_0
     *      Index 27 High WR_0_1
     *      Index 27 Low  WR_0_2
     *      Index 26 High WR_0_3
     *      ...
     *   next value possition = ( Index = (Low_High == Low ? Index-- : Index) , Low_High =  ~ (Low_High) )
     **/

    high_low = 0;
    cdd_num = 28;

    for (type = CDD_WRITE_READ; type <= CDD_READ_READ; type++ ) {
        for (i = 0; i < MAX_SUPPORTED_RANKS; i++ ) {
            for (j = 0; j < MAX_SUPPORTED_RANKS; j++ ) {
                if ((i == j) && ((type == CDD_WRITE_WRITE) || (type == CDD_READ_READ))) {
                    continue;
                }
                train_data->critical_delay[type][i][j] = cdd_data[cdd_num][high_low];
                if (0 == high_low) {
                    cdd_num = cdd_num - 1;
                    high_low = 1;
                } else {
                    high_low = 0;
                }
            }
        }
    }
}

/**
 * @brief Get maximum critical delay difference value
 *
 * @param train_data    Train data result
 * @param train_type    CCD type (WW, RR, WR, RW)
 * @param rank_type     Type of max calculation (Same Rank, Diff Rank)
 * @param n_ranks       Number os active ranks
 * @return int8_t       max result
 */
static int8_t get_cdd_type_max(ddr4_train_data_process_t *train_data, ddr4_train_type_t train_type,
                               ddr4r_rank_type_t rank_type, uint8_t n_ranks)
{
    uint8_t i, j;
    int8_t  max_cdd = SCHAR_MIN;

    if (((rank_type == CDD_ALL_RANK) || (rank_type == CDD_SAME_RANK)) &&
        ((train_type == CDD_WRITE_WRITE) || (train_type == CDD_READ_READ))) {
        SNPS_ERROR("Get CDD max type %d rank check %d", train_type, rank_type);
        return max_cdd;
    }

    // Calculating cdd_rr_max
    for (i = 0; i < n_ranks; i++) {
        for (j = 0; j < n_ranks; j++) {
            if ((CDD_SAME_RANK == rank_type) && (i != j)) {
                continue;
            }
            if ((CDD_DIFF_RANK == rank_type) && (i == j)) {
                continue;
            }
            max_cdd = max(max_cdd, train_data->critical_delay[train_type][i][j]);
        }
    }
    return max_cdd;
}


/**
 * @brief method to apply training results to the controller DDR4
 *
 */
bool dwc_ddrctl_apply_training_ddr4()
{
    ddr4_train_data_process_t train_data;
    int8_t cdd_rr_max;
    int8_t cdd_ww_max;
    int8_t cdd_rw_diff_rank;
    int8_t cdd_wr_diff_rank;
    int8_t cdd_rw_same_rank;
    int8_t cdd_wr_same_rank;
    uint8_t diff_rank_wr_gap;
    uint8_t diff_rank_rd_gap;
    uint8_t read_write_cmd;
    uint8_t write_read_cmd;
    uint8_t read_write_diff_rank;
    uint8_t write_read_diff_rank;
    uint8_t write2read_diff_bg;
    uint8_t n_freq;
    uint32_t ranktmg0;
    uint32_t ranktmg1;
    uint32_t dramset1tmg9;
    uint32_t dramset1tmg2;
    uint8_t ranks;

    read_ccd_train_data(&train_data);

    ranks = cinit_get_number_ranks();

    SNPS_LOG("Active Ranks %d ", ranks);

    for(n_freq = 0; n_freq < hdlr->num_pstates; n_freq++){

         /** - Get maximum value for each CDD value.*/
        cdd_rr_max       = get_cdd_type_max(&train_data, CDD_READ_READ,   CDD_DIFF_RANK, ranks);
        cdd_ww_max       = get_cdd_type_max(&train_data, CDD_WRITE_WRITE, CDD_DIFF_RANK, ranks);
        cdd_rw_diff_rank = get_cdd_type_max(&train_data, CDD_READ_WRITE,  CDD_DIFF_RANK, ranks);
        cdd_wr_diff_rank = get_cdd_type_max(&train_data, CDD_WRITE_READ,  CDD_DIFF_RANK, ranks);
        cdd_rw_same_rank = get_cdd_type_max(&train_data, CDD_READ_WRITE,  CDD_SAME_RANK, ranks);
        cdd_wr_same_rank = get_cdd_type_max(&train_data, CDD_WRITE_READ,  CDD_SAME_RANK, ranks);

        SNPS_LOG("CDD_RR = %d, CDD_WW = %d ",cdd_rr_max, cdd_ww_max);
        SNPS_LOG("CDD_RW = %d(diff rank), CDD_WR = %d(diff rank)",cdd_rw_diff_rank,cdd_wr_diff_rank);
        SNPS_LOG("CDD_RW = %d(same rank & diff bank gp), CDD_WR = %d(same rank & diff bank gp), ",
                cdd_rw_same_rank, cdd_wr_same_rank);

        if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_pre_qdyn_write");
            return false;
        }
        /** - Read original programed latency in controller register.*/
        dramset1tmg2 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, 0) + DRAMSET1TMG2);
        read_write_cmd = SNPS_READ_FIELD(dramset1tmg2, DRAMSET1TMG2_RD2WR);
        write_read_cmd = SNPS_READ_FIELD(dramset1tmg2, DRAMSET1TMG2_WR2RD);

        read_write_cmd = read_write_cmd + max(0, cdd_rw_same_rank);
        write_read_cmd = write_read_cmd + max(0, cdd_wr_same_rank);

        SNPS_WRITE_FIELD(dramset1tmg2, DRAMSET1TMG2_RD2WR, read_write_cmd);
        SNPS_WRITE_FIELD(dramset1tmg2, DRAMSET1TMG2_WR2RD, write_read_cmd);
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, 0) + DRAMSET1TMG2, dramset1tmg2);

        dramset1tmg9 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, 0) + DRAMSET1TMG9);
        write2read_diff_bg = SNPS_READ_FIELD(dramset1tmg9, DRAMSET1TMG9_WR2RD_S);
        SNPS_LOG("Controller latency: wr2rd_s = %d", write2read_diff_bg);

        write2read_diff_bg = write2read_diff_bg + max(0, cdd_wr_same_rank);

        SNPS_WRITE_FIELD(dramset1tmg9, DRAMSET1TMG9_WR2RD_S, write2read_diff_bg);
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, 0) + DRAMSET1TMG9, dramset1tmg9);
        SNPS_LOG("Expected latency:wr2rd_s = %d", write2read_diff_bg);

        /** Configure ranktmg0 if the number of logic ranks are bigger than 1.*/
        if (UMCTL2_NUM_LRANKS_TOTAL > 1) {
            ranktmg0 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, 0) + RANKTMG0);
            diff_rank_wr_gap = SNPS_READ_FIELD(ranktmg0, RANKTMG0_DIFF_RANK_WR_GAP);
            diff_rank_rd_gap = SNPS_READ_FIELD(ranktmg0, RANKTMG0_DIFF_RANK_RD_GAP);
            SNPS_LOG("Controller latency: diff_rank_rd_gap = %d,diff_rank_wr_gap = %d",diff_rank_rd_gap,diff_rank_wr_gap);

            // BL/2+ max(0, CDD_RR_[i]_[j]) + 4 MEMCLK
            diff_rank_rd_gap = diff_rank_rd_gap + max(0, cdd_rr_max );
            // BL/2+ max(0, CDD_WW_[i]_[j]) + 4 MEMCLK
            diff_rank_wr_gap = diff_rank_wr_gap + max(0, cdd_ww_max );

            SNPS_WRITE_FIELD(ranktmg0, RANKTMG0_DIFF_RANK_WR_GAP, diff_rank_wr_gap);
            SNPS_WRITE_FIELD(ranktmg0, RANKTMG0_DIFF_RANK_RD_GAP, diff_rank_rd_gap);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, 0) + RANKTMG0, ranktmg0);
            SNPS_LOG("Expected latency: diff_rank_rd_gap = %d,diff_rank_wr_gap = %d", diff_rank_rd_gap, diff_rank_wr_gap);
        }

        /** Configure ranktmg1 if the number of ranks are bigger than 1.*/
        if (MEMC_NUM_RANKS > 1) {
            ranktmg1 = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, 0) + RANKTMG1);
            read_write_diff_rank = SNPS_READ_FIELD(ranktmg1, RANKTMG1_RD2WR_DR);
            write_read_diff_rank = SNPS_READ_FIELD(ranktmg1, RANKTMG1_WR2RD_DR);
            SNPS_LOG("Controller latency: rd2wr_dr = %d,wr2rd_dr = %d",read_write_diff_rank, write_read_diff_rank);

            // System_R2W  + max(0,CDD_RW_R[i]_R[j]) + 5 MEMCLK
            read_write_diff_rank = read_write_diff_rank + max(0, cdd_rw_diff_rank );
            // System_W2R  + max(0,CDD_WR_R[i]_R[j]) + 5 MEMCLK
            write_read_diff_rank = write_read_diff_rank + max(0, cdd_wr_diff_rank );

            SNPS_WRITE_FIELD(ranktmg1, RANKTMG1_RD2WR_DR, read_write_diff_rank);
            SNPS_WRITE_FIELD(ranktmg1, RANKTMG1_WR2RD_DR, write_read_diff_rank);
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, 0) + RANKTMG1, ranktmg1);
            SNPS_LOG("Expected latency: rd2wr_dr = %d,wr2rd_dr = %d",read_write_diff_rank, write_read_diff_rank);
        }

        if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
            SNPS_LOG("Error in seq_post_qdyn_write");
            return false;
        }
    }

    if (dwc_ddrctl_phy_train_ctrl_delay() == false) {
        SNPS_LOG("Error writing the control delay");
        return false;
    }

    if (dwc_ddrctl_phy_train_wrdata_delay() == false) {
        SNPS_LOG("Error writing the wrdata delay");
        return false;
    }

    return true;
}

#endif

#endif
