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
#include "cinit_status.h"
#include "bit_macros.h"
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_common_sequences.h"
#include "dwc_ddrctl_cinit_ddr_sequences.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_phy_training_common.h"
#include "physetup.h"
#include "phy/sinit_phy_types.h"
#include "phy/ddr54/sinit_ddrphy54_regmap.h"


#ifdef DDRCTL_DDR
#ifdef CINIT_DDR5

#define DDR5_PHY_CDD_CH0_BASE_ADDR ((DDR54_PHY_BLOCK_UCTL_MEMORY) + 0x8013)
#define DDR5_PHY_CDD_CH1_BASE_ADDR ((DDR54_PHY_BLOCK_UCTL_MEMORY) + 0x8089)

#define DDR5_N_CHANNELS 2

typedef struct ddr5_train_data_process_s {
    int8_t cdd_low[DDR5_N_CHANNELS][DDR5_TRAIN_DATA_SIZE];
    int8_t cdd_high[DDR5_N_CHANNELS][DDR5_TRAIN_DATA_SIZE];

    uint8_t cdd_rw_s_max;
    uint8_t cdd_wr_s_max;

    // - expected latency - RANK_SWITCH_TIMING_CONTROL0~5
    uint8_t ranks_index_max;
    int8_t wr2wr_gap[4][4];
    int8_t rd2wr_gap[4][4];
    int8_t wr2rd_gap[4][4];
    int8_t rd2rd_gap[4][4];

    int8_t rd2wr;
    int8_t wr2rd;
    int8_t wr2rd_s;
    int8_t rd2wr_dlr;
    int8_t wr2rd_dlr;

    // - controller latency
    uint8_t t_wr_postamble;
    uint8_t t_rd_postamble;
    uint8_t t_wr_preamble;
    uint8_t t_rd_preamble;

    int8_t system_w2w;
    int8_t system_r2w;
    int8_t system_w2r;
    int8_t system_r2r;
    ddrctl_bool_t use_two_dram_clock;
} ddr5_train_data_process_t;


/** @brief Internal function to read CDD values
 */
static void load_cdd(ddr5_train_data_process_t *train_process)
{
    uint16_t cdd_num;
    uint16_t cdd_data0;
    uint16_t cdd_data1;

/** - For cha -cdd_high[0] & cdd_low[0]*/
/** - addr-0x:  58013 |58014 |58015 |58016 |58017 |58018 ||58019 |5801a |5801b |5801c |5801d |5801e |5801f |58020 ||58021 |58022 |58023 |58024 |58025 |58026 |58027 |58028 ||58029 |5802a |5802b |5802c |5802d |5802e |*/
/** - index:    0     |1     |2     |3     |4     |5     ||6     |7     |8     |9     |10    |11    |12    |13    ||14    |15    |16    |17    |18    |19    |20    |21    ||22    |23    |24    |25    |26    |27    |*/
/** - cdd_low:  RR_3_2|RR_3_0|RR_2_1|RR_1_3|RR_1_0|RR_0_2||RW_3_3|RW_3_1|RW_2_3|RW_2_1|RW_1_3|RW_1_1|RW_0_3|RW_0_1||WR_3_3|WR_3_1|WR_2_3|WR_2_1|WR_1_3|WR_1_1|WR_0_3|WR_0_1||WW_3_2|WW_3_0|WW_2_1|WW_1_3|WW_1_0|WW_0_2|*/
/** - cdd_high: RR_3_1|RR_2_3|RR_2_0|RR_1_2|RR_0_3|RR_0_1||RW_3_2|RW_3_0|RW_2_2|RW_2_0|RW_1_2|RW_1_0|RW_0_2|RW_0_0||WR_3_2|WR_3_0|WR_2_2|WR_2_0|WR_1_2|WR_1_0|WR_0_2|WR_0_0||WW_3_1|WW_2_3|WW_2_0|WW_1_2|WW_0_3|WW_0_1|*/

/** - For chb -cdd_high[1] & cdd_low[1]*/
/** - addr-0x:  58089 |5808a |5808b |5808c |5808d |5808e ||5808f |58090 |58091 |58092 |58093 |58094 |58095 |58096 ||58097 |58098 |58099 |5809a |5809b |5809c |5809d |5809e ||5809f |580a0 |580a1 |580a2 |580a3 |580a4 |*/
/** - index:    0     |1     |2     |3     |4     |5     ||6     |7     |8     |9     |10    |11    |12    |13    ||14    |15    |16    |17    |18    |19    |20    |21    ||22    |23    |24    |25    |26    |27    |*/
/** - cdd_low:  RR_3_2|RR_3_0|RR_2_1|RR_1_3|RR_1_0|RR_0_2||RW_3_3|RW_3_1|RW_2_3|RW_2_1|RW_1_3|RW_1_1|RW_0_3|RW_0_1||WR_3_3|WR_3_1|WR_2_3|WR_2_1|WR_1_3|WR_1_1|WR_0_3|WR_0_1||WW_3_2|WW_3_0|WW_2_1|WW_1_3|WW_1_0|WW_0_2|*/
/** - cdd_high: RR_3_1|RR_2_3|RR_2_0|RR_1_2|RR_0_3|RR_0_1||RW_3_2|RW_3_0|RW_2_2|RW_2_0|RW_1_2|RW_1_0|RW_0_2|RW_0_0||WR_3_2|WR_3_0|WR_2_2|WR_2_0|WR_1_2|WR_1_0|WR_0_2|WR_0_0||WW_3_1|WW_2_3|WW_2_0|WW_1_2|WW_0_3|WW_0_1|*/

    // For each CDD
    for (cdd_num = 0; cdd_num < DDR5_TRAIN_DATA_SIZE; cdd_num++){
        // read CDD
        cdd_data0 = physetup_io_read16(DDR5_PHY_CDD_CH0_BASE_ADDR + cdd_num);
        cdd_data1 = physetup_io_read16(DDR5_PHY_CDD_CH1_BASE_ADDR + cdd_num);

        // load CDD into a arrays separating low and high
        train_process->cdd_low[0][cdd_num] = cdd_data0 & 0x00FF;
        train_process->cdd_high[0][cdd_num] = (cdd_data0 >> 8) & 0x00FF;
        //printf("Address: 0x%x = 0x%x\n", DDR5_PHY_CDD_CH0_BASE_ADDR + cdd_num, cdd_data0);

        train_process->cdd_low[1][cdd_num] = cdd_data1 & 0x00FF;
        train_process->cdd_high[1][cdd_num] = (cdd_data1 >> 8) & 0x00FF;
    }
}

/** @brief Get maximum value for cdd_rw_s CDD value
 */
static uint8_t get_cdd_rw_s_max(ddr5_train_data_process_t *train_process)
{
    uint8_t ret = 0;

    // Calculating cdd_rw_s_max, use max(0, CDD value) instead of abs(CDD value)
    ret = max(train_process->cdd_high[1][13], ret);
    ret = max(train_process->cdd_high[0][13], ret);
    ret = max(train_process->cdd_high[1][ 8], ret);
    ret = max(train_process->cdd_high[0][ 8], ret);
    ret = max(train_process->cdd_low[1][11], ret);
    ret = max(train_process->cdd_low[0][11], ret);
    ret = max(train_process->cdd_low[1][ 6], ret);
    ret = max(train_process->cdd_low[0][ 6], ret);

    return ret;
}

/** @brief Get maximum value for cdd_wr_s CDD value
 */
static uint8_t get_cdd_wr_s_max(ddr5_train_data_process_t *train_process)
{
    uint8_t ret = 0;

   // Calculating cdd_wr_s_max, use max(0, CDD value) instead of abs(CDD value)
    ret = max(train_process->cdd_high[1][21], ret);
    ret = max(train_process->cdd_high[0][21], ret);
    ret = max(train_process->cdd_high[1][16], ret);
    ret = max(train_process->cdd_high[0][16], ret);
    ret = max(train_process->cdd_low[1][19], ret);
    ret = max(train_process->cdd_low[0][19], ret);
    ret = max(train_process->cdd_low[1][14], ret);
    ret = max(train_process->cdd_low[0][14], ret);
    return ret;
}

/** @brief Internal function load gap values
 */
static void load_gap(ddr5_train_data_process_t *train_process)
{
    train_process->rd2wr_gap[0][0] = max(train_process->cdd_high[0][13], train_process->cdd_high[1][13]);
    train_process->rd2wr_gap[1][1] = max(train_process->cdd_low [0][11], train_process->cdd_low [1][11]);
    train_process->rd2wr_gap[2][2] = max(train_process->cdd_high[0][ 8], train_process->cdd_high[1][ 8]);
    train_process->rd2wr_gap[3][3] = max(train_process->cdd_low [0][ 6], train_process->cdd_low [1][ 6]);

    train_process->wr2rd_gap[0][0] = max(train_process->cdd_high[0][21], train_process->cdd_high[1][21]);
    train_process->wr2rd_gap[1][1] = max(train_process->cdd_low [0][19], train_process->cdd_low [1][19]);
    train_process->wr2rd_gap[2][2] = max(train_process->cdd_high[0][16], train_process->cdd_high[1][16]);
    train_process->wr2rd_gap[3][3] = max(train_process->cdd_low [0][14], train_process->cdd_low [1][14]);

    // - Controller RANK_SWITCH_TIMING_CONTROL registers all have a suffix RxRy. It represents the gap when performing consecutive reads/writes from rank Y to rank X according to databook. Jira:P80001562-419711 
    // - PHY PUB CSR CDD_RW_R[i]_R[j]: suffix R[i]_R[j] represents the gap from rank i to rank j 
    if (train_process->ranks_index_max > 1){
        // - Rank0/RANK1 - RANK_SWITCH_TIMING_CONTROL0
        train_process->wr2wr_gap[0][1] = max(train_process->cdd_low [0][26], train_process->cdd_low [1][26]);
        train_process->wr2wr_gap[1][0] = max(train_process->cdd_high[0][27], train_process->cdd_high[1][27]);
        train_process->rd2wr_gap[0][1] = max(train_process->cdd_high[0][11], train_process->cdd_high[1][11]);
        train_process->rd2wr_gap[1][0] = max(train_process->cdd_low [0][13], train_process->cdd_low [1][13]);
        train_process->wr2rd_gap[0][1] = max(train_process->cdd_high[0][19], train_process->cdd_high[1][19]);
        train_process->wr2rd_gap[1][0] = max(train_process->cdd_low [0][21], train_process->cdd_low [1][21]);
        train_process->rd2rd_gap[0][1] = max(train_process->cdd_low [0][ 4], train_process->cdd_low [1][ 4]);
        train_process->rd2rd_gap[1][0] = max(train_process->cdd_high[0][ 5], train_process->cdd_high[1][ 5]);
        if (train_process->ranks_index_max > 3){
            // - Rank0/RANK2 - RANK_SWITCH_TIMING_CONTROL1
            train_process->wr2wr_gap[0][2] = max(train_process->cdd_high[0][24], train_process->cdd_high[1][24]);
            train_process->wr2wr_gap[2][0] = max(train_process->cdd_low [0][27], train_process->cdd_low [1][27]);
            train_process->rd2wr_gap[0][2] = max(train_process->cdd_high[0][ 9], train_process->cdd_high[1][ 9]);
            train_process->rd2wr_gap[2][0] = max(train_process->cdd_high[0][12], train_process->cdd_high[1][12]);
            train_process->wr2rd_gap[0][2] = max(train_process->cdd_high[0][17], train_process->cdd_high[1][17]);
            train_process->wr2rd_gap[2][0] = max(train_process->cdd_high[0][20], train_process->cdd_high[1][20]);
            train_process->rd2rd_gap[0][2] = max(train_process->cdd_high[0][ 2], train_process->cdd_high[1][ 2]);
            train_process->rd2rd_gap[2][0] = max(train_process->cdd_low [0][ 5], train_process->cdd_low [1][ 5]);

           // - Rank0/RANK3 - RANK_SWITCH_TIMING_CONTROL2
            train_process->wr2wr_gap[0][3] = max(train_process->cdd_low [0][23], train_process->cdd_low [1][23]);
            train_process->wr2wr_gap[3][0] = max(train_process->cdd_high[0][26], train_process->cdd_high[1][26]);
            train_process->rd2wr_gap[0][3] = max(train_process->cdd_high[0][ 7], train_process->cdd_high[1][ 7]);
            train_process->rd2wr_gap[3][0] = max(train_process->cdd_low [0][12], train_process->cdd_low [1][12]);
            train_process->wr2rd_gap[0][3] = max(train_process->cdd_high[0][15], train_process->cdd_high[1][15]);
            train_process->wr2rd_gap[3][0] = max(train_process->cdd_low [0][20], train_process->cdd_low [1][20]);
            train_process->rd2rd_gap[0][3] = max(train_process->cdd_low [0][ 1], train_process->cdd_low [1][ 1]);
            train_process->rd2rd_gap[3][0] = max(train_process->cdd_high[0][ 4], train_process->cdd_high[1][ 4]);

            // - Rank1/RANK2 - RANK_SWITCH_TIMING_CONTROL3
            train_process->wr2wr_gap[1][2] = max(train_process->cdd_low [0][24], train_process->cdd_low [1][24]);
            train_process->wr2wr_gap[2][1] = max(train_process->cdd_high[0][25], train_process->cdd_high[1][25]);
            train_process->rd2wr_gap[1][2] = max(train_process->cdd_low [0][ 9], train_process->cdd_low [1][ 9]);
            train_process->rd2wr_gap[2][1] = max(train_process->cdd_high[0][10], train_process->cdd_high[1][10]);
            train_process->wr2rd_gap[1][2] = max(train_process->cdd_low [0][17], train_process->cdd_low [1][17]);
            train_process->wr2rd_gap[2][1] = max(train_process->cdd_high[0][18], train_process->cdd_high[1][18]);
            train_process->rd2rd_gap[1][2] = max(train_process->cdd_low [0][ 2], train_process->cdd_low [1][ 2]);
            train_process->rd2rd_gap[2][1] = max(train_process->cdd_high[0][ 3], train_process->cdd_high[1][ 3]);

            // - Rank1/RANK3 - RANK_SWITCH_TIMING_CONTROL4
            train_process->wr2wr_gap[1][3] = max(train_process->cdd_high[0][22], train_process->cdd_high[1][22]);
            train_process->wr2wr_gap[3][1] = max(train_process->cdd_low [0][25], train_process->cdd_low [1][25]);
            train_process->rd2wr_gap[1][3] = max(train_process->cdd_low [0][ 7], train_process->cdd_low [1][ 7]);
            train_process->rd2wr_gap[3][1] = max(train_process->cdd_low [0][10], train_process->cdd_low [1][10]);
            train_process->wr2rd_gap[1][3] = max(train_process->cdd_low [0][15], train_process->cdd_low [1][15]);
            train_process->wr2rd_gap[3][1] = max(train_process->cdd_low [0][18], train_process->cdd_low [1][18]);
            train_process->rd2rd_gap[1][3] = max(train_process->cdd_high[0][ 0], train_process->cdd_high[1][ 0]);
            train_process->rd2rd_gap[3][1] = max(train_process->cdd_low [0][ 3], train_process->cdd_low [1][ 3]);

            // - Rank2/RANK3 - RANK_SWITCH_TIMING_CONTROL5
            train_process->wr2wr_gap[2][3] = max(train_process->cdd_low [0][22], train_process->cdd_low [1][22]);
            train_process->wr2wr_gap[3][2] = max(train_process->cdd_high[0][23], train_process->cdd_high[1][23]);
            train_process->rd2wr_gap[2][3] = max(train_process->cdd_high[0][ 6], train_process->cdd_high[1][ 6]);
            train_process->rd2wr_gap[3][2] = max(train_process->cdd_low [0][ 8], train_process->cdd_low [1][ 8]);
            train_process->wr2rd_gap[2][3] = max(train_process->cdd_high[0][14], train_process->cdd_high[1][14]);
            train_process->wr2rd_gap[3][2] = max(train_process->cdd_low [0][16], train_process->cdd_low [1][16]);
            train_process->rd2rd_gap[2][3] = max(train_process->cdd_low [0][ 0], train_process->cdd_low [1][ 0]);
            train_process->rd2rd_gap[3][2] = max(train_process->cdd_high[0][ 1], train_process->cdd_high[1][ 1]);

        }
    }

    {
        uint8_t i, j;
        for (i = 0; i < train_process->ranks_index_max; i++) {
            for (j = 0; j < train_process->ranks_index_max; j++) {
                if (i == j) {
                    continue;
                }
                SNPS_LOG("Read: Rank to Rank Wr 2 Wr gap [%d][%d] = %d", i, j, train_process->wr2wr_gap[i][j]);
                SNPS_LOG("Read: Rank to Rank Rd 2 Wr gap [%d][%d] = %d", i, j, train_process->rd2wr_gap[i][j]);
                SNPS_LOG("Read: Rank to Rank Wr 2 Rd gap [%d][%d] = %d", i, j, train_process->wr2rd_gap[i][j]);
                SNPS_LOG("Read: Rank to Rank Rd 2 Rd gap [%d][%d] = %d", i, j, train_process->rd2rd_gap[i][j]);
            }
        }
    }

}

/** @brief Internal function normalize gap values
 */
static void calcule_timing_spacing(ddr5_train_data_process_t *train_process)
{
    uint8_t i, j;

    for (i = 0; i < train_process->ranks_index_max; i++) {
        for (j = 0; j < train_process->ranks_index_max; j++) {
            if (i == j) {
                continue;
            }
            train_process->wr2wr_gap[i][j] = train_process->system_w2w + 5 + max(train_process->wr2wr_gap[i][j], 0);
            train_process->rd2wr_gap[i][j] = train_process->system_r2w + 5 + max(train_process->rd2wr_gap[i][j], 0);
            train_process->wr2rd_gap[i][j] = train_process->system_w2r + 5 + max(train_process->wr2rd_gap[i][j], 0);
            train_process->rd2rd_gap[i][j] = train_process->system_r2r + 5 + max(train_process->rd2rd_gap[i][j], 0);

            if ((train_process->wr2wr_gap[i][j] > 15) || (train_process->rd2wr_gap[i][j] > 15) ||
                (train_process->wr2rd_gap[i][j] > 15) || (train_process->rd2rd_gap[i][j] > 15)) {
                train_process->use_two_dram_clock = DDRCTL_TRUE;
            }

            SNPS_LOG("Normalize: Rank to Rank Wr 2 Wr Timing [%d][%d] = %d", i, j, train_process->wr2wr_gap[i][j]);
            SNPS_LOG("Normalize: Rank to Rank Rd 2 Wr Timing [%d][%d] = %d", i, j, train_process->rd2wr_gap[i][j]);
            SNPS_LOG("Normalize: Rank to Rank Wr 2 Rd Timing [%d][%d] = %d", i, j, train_process->wr2rd_gap[i][j]);
            SNPS_LOG("Normalize: Rank to Rank Rd 2 Rd Timing [%d][%d] = %d", i, j, train_process->rd2rd_gap[i][j]);
        }
    }
}


static uint32_t get_rank_switch_timing_control_value(uint8_t control_reg_num, ddr5_train_data_process_t *train_process)
{
    uint32_t    value = 0;
    uint8_t     i, j;
    uint8_t     gap_unit;

    switch (control_reg_num) {
        case 1:
            i=0; j=2; break;
        case 2:
            i=0; j=3; break;
        case 3:
            i=1; j=2; break;
        case 4:
            i=1; j=3; break;
        case 5:
            i=2; j=3; break;
        default:
        case 0:
            i=0; j=1; break;
    }

    if (DDRCTL_TRUE == train_process->use_two_dram_clock) {
        gap_unit = 2;
    } else {
        gap_unit = 1;
    }

    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R0R1, CEIL(train_process->rd2rd_gap[i][j], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_RD2RD_GAP_R1R0, CEIL(train_process->rd2rd_gap[j][i], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R0R1, CEIL(train_process->wr2rd_gap[i][j], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_WR2RD_GAP_R1R0, CEIL(train_process->wr2rd_gap[j][i], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R0R1, CEIL(train_process->rd2wr_gap[i][j], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_RD2WR_GAP_R1R0, CEIL(train_process->rd2wr_gap[j][i], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R0R1, CEIL(train_process->wr2wr_gap[i][j], gap_unit));
    SNPS_WRITE_FIELD(value, RANK_SWITCH_TIMING_CONTROL0_T_WR2WR_GAP_R1R0, CEIL(train_process->wr2wr_gap[j][i], gap_unit));

    SNPS_DEBUG("Write: Rank to Rank Rd 2 Rd Timing [%d][%d] = %d", i, j, CEIL(train_process->rd2rd_gap[i][j], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Rd 2 Rd Timing [%d][%d] = %d", j, i, CEIL(train_process->rd2rd_gap[j][i], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Wr 2 Wr Timing [%d][%d] = %d", i, j, CEIL(train_process->wr2wr_gap[i][j], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Wr 2 Wr Timing [%d][%d] = %d", j, i, CEIL(train_process->wr2wr_gap[j][i], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Rd 2 Wr Timing [%d][%d] = %d", i, j, CEIL(train_process->rd2wr_gap[i][j], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Rd 2 Wr Timing [%d][%d] = %d", j, i, CEIL(train_process->rd2wr_gap[j][i], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Wr 2 Rd Timing [%d][%d] = %d", i, j, CEIL(train_process->wr2rd_gap[i][j], gap_unit));
    SNPS_DEBUG("Write: Rank to Rank Wr 2 Rd Timing [%d][%d] = %d", j, i, CEIL(train_process->wr2rd_gap[j][i], gap_unit));

    return value;
}

/** @brief Internal function that sets the Rank switch timing control
 *
 * This function must be called with Quasi-dynamic programing mode enable
 */
static void set_rank_sw_timing_ctrl(uint8_t n_freq, uint8_t channel, ddr5_train_data_process_t *train_process)
{
    uint8_t     i, j;
    uint8_t     num_ranks = cinit_get_number_ranks();
    uint8_t     use_two_dram_clock;
    uint32_t    pasctl1;

    if (num_ranks > 1) {

        if (DDRCTL_TRUE == train_process->use_two_dram_clock) {
            use_two_dram_clock = 1;
        } else {
            use_two_dram_clock = 0;
        }

        SNPS_DEBUG("Configure Rank Switch Gap Unit to %d clock cycle", use_two_dram_clock == 0 ? 1: 2);

        // Configure the Rank Switch Gap Unit, 0 - 1 DRAM clock cycle. 1 - 2 DRAM clock cycles
        pasctl1 = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(channel) + PASCTL1);
        SNPS_WRITE_FIELD(pasctl1, PASCTL1_RANK_SWITCH_GAP_UNIT_SEL, use_two_dram_clock);
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(channel) + PASCTL1, pasctl1);

        // - Rank0/RANK1 - RANK_SWITCH_TIMING_CONTROL0
        dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL0,
                                    get_rank_switch_timing_control_value(0, train_process));

        if (num_ranks > 2) {
            // - Rank 0 - Rank 2
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL1,
                                        get_rank_switch_timing_control_value(1, train_process));
            // - Rank 0 - Rank 3
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL2,
                                        get_rank_switch_timing_control_value(2, train_process));
            // - Rank 1 - Rank 2
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL3,
                                        get_rank_switch_timing_control_value(3, train_process));
            // - Rank 1 - Rank 3
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL4,
                                        get_rank_switch_timing_control_value(4, train_process));
            // - Rank 2 - Rank 3
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + RANK_SWITCH_TIMING_CONTROL5,
                                        get_rank_switch_timing_control_value(5, train_process));
        }
    }
}


/** @brief method to apply training results to the controller DDR4
 */
bool dwc_ddrctl_apply_training_ddr5()
{
    uint8_t n_freq;
    uint8_t channel;
    uint8_t num_channels;

    ddr5_train_data_process_t train_process;
    DRAMSET1TMG2_t  dramset1tmg2;
    DRAMSET1TMG9_t  dramset1tmg9;
    DRAMSET1TMG22_t dramset1tmg22;

    memset(&train_process, 0, sizeof(ddr5_train_data_process_t));

    train_process.ranks_index_max = (MEMC_NUM_RANKS < 2) ? 0 : ((MEMC_NUM_RANKS < 3) ? 2 : 4);
    num_channels = cinit_get_num_channels_enable();

    load_cdd(&train_process);
    load_gap(&train_process);

    for(channel = 0; channel < num_channels; channel++) {
    //currently only one frequency is supported by this code
        for(n_freq = 0; n_freq < hdlr->num_pstates; n_freq++) {

            /** - Get maximum value for each CDD value.*/
            train_process.cdd_rw_s_max = get_cdd_rw_s_max(&train_process);
            train_process.cdd_wr_s_max = get_cdd_wr_s_max(&train_process);
            SNPS_LOG("[Rank Timing]CDD value: CDD_RW_S=%d(same rank),CDD_WR_S=%d(same rank)", train_process.cdd_rw_s_max, train_process.cdd_wr_s_max);

            /** - Read original read/write latency in controller register.*/
            dramset1tmg2.value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG2);
            train_process.rd2wr = dramset1tmg2.rd2wr; // CL - CWL + BL/2 + 2 - (Read DQS offset) + (RD_POSTAMBLE-0.5) + WR_PREAMBLE
            train_process.wr2rd = dramset1tmg2.wr2rd; // CWL + BL/2 + tWTR_L
            SNPS_LOG("[Clr read][rd2wr] Min read to write command time: %d", train_process.rd2wr);
            SNPS_LOG("[Clr read][wr2rd] Min write to read command time: %d", train_process.wr2rd);

            dramset1tmg9.value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG9);
            train_process.wr2rd_s = dramset1tmg9.wr2rd_s; // CWL + PL + BL/2 + tWTR_S
            SNPS_LOG("[Clr read][wr2rd_s] Min write to read command time different bank group: %d", train_process.wr2rd_s);

            dramset1tmg22.value = dwc_ddrctl_cinit_io_read32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG22);
            train_process.rd2wr_dlr = dramset1tmg22.t_rd2wr_dlr;  // CL-CWL+RBL/2+2tCK - (read DQS offset) + (tRPST - tCK/2) + tWPRE
            train_process.wr2rd_dlr = dramset1tmg22.t_wr2rd_dlr;  // CWL+WBL/2+tWRT_S
            SNPS_LOG("[Clr read][t_rd2wr_dlr] read to write switch to different logical rank in same physical rank: %d", train_process.rd2wr_dlr);
            SNPS_LOG("[Clr read][t_wr2rd_dlr] write to read switch to different logical rank in same physical rank: %d", train_process.wr2rd_dlr);

            train_process.rd2wr     = train_process.rd2wr     + train_process.cdd_rw_s_max;
            train_process.wr2rd     = train_process.wr2rd     + train_process.cdd_wr_s_max;
            train_process.wr2rd_s   = train_process.wr2rd_s   + train_process.cdd_wr_s_max;
            train_process.rd2wr_dlr = train_process.rd2wr_dlr + train_process.cdd_rw_s_max;
            train_process.wr2rd_dlr = train_process.wr2rd_dlr + train_process.cdd_wr_s_max;

            /* - Calculate new read/write latency with CDD value of RANK_SWITCH_TIMING_CONTROL registers. */
            /* According to PUB databook Version 3.60a                                             */  
            /* tphy_wrcsgap  = 5 MEMCLK + PreamblePostambleAdjustment + D5PositionTxPhaseUpdateAdjustment + MAX[ 0, CDD_WW_R[i]_R[j] ] , PUB databook Table 5-3    */
            /* tphy_rdcsgap  = 5 MEMCLK + PreamblePostambleAdjustment + D5PositionRxPhaseUpdateAdjustment + MAX[ 0, CDD_RR_R[i]_R[j] ] , PUB databook Table 5-5    */
            /* tCCDmin (R_rank[i], W_rank[j]) = System_R2W + BL/2 + max(0,CDD_RW_R[i]_R[j]) + 5 MEMCLK ,  PUB databook 10.2.1.2.1                                  */
            /* tCCDmin (W_rank[i], R_rank[j]) = System_W2R + BL/2 + max(0,CDD_WR_R[i]_R[j]) + 5 MEMCLK ,  PUB databook 10.2.1.2.2                                  */
            /* 2 = CL - CWL, (-2) = CWL - CL , used in system_r2w/system_w2r respectively */

            train_process.t_wr_postamble =  hdlr->memCtrlr_m.ddr5_mr[n_freq].mr8.wr_postamble & 0x0001; // write postamble - 0.5
            train_process.t_rd_postamble =  hdlr->memCtrlr_m.ddr5_mr[n_freq].mr8.rd_postamble & 0x0001; // read  postamble - 0.5
            train_process.t_wr_preamble  = (hdlr->memCtrlr_m.ddr5_mr[n_freq].mr8.wr_preamble  & 0x0003) + 1;
            train_process.t_rd_preamble  =  hdlr->memCtrlr_m.ddr5_mr[n_freq].mr8.rd_preamble;

            if ((train_process.t_rd_preamble & 0x0007) < 2) {
                train_process.t_rd_preamble = train_process.t_rd_preamble + 1;
            }

            SNPS_LOG("t_wr_postamble: %d, t_rd_postamble: %d, t_wr_preamble %d, t_rd_preamble%d", train_process.t_wr_postamble,
            train_process.t_rd_postamble, train_process.t_wr_preamble, train_process.t_rd_preamble);

            train_process.system_w2w =        (train_process.t_wr_preamble - 2) + train_process.t_wr_postamble ;
            train_process.system_r2w =   2  + (train_process.t_wr_preamble - 2) + train_process.t_rd_postamble ;
            train_process.system_w2r = (-2) + (train_process.t_rd_preamble - 2) + train_process.t_wr_postamble ;
            train_process.system_r2r =        (train_process.t_rd_preamble - 1) + train_process.t_rd_postamble ;

            SNPS_LOG("system_w2w: %d, system_r2w: %d, system_w2r: %d, system_r2r: %d", train_process.system_w2w,
                    train_process.system_r2w, train_process.system_w2r, train_process.system_r2r);

            calcule_timing_spacing(&train_process);

            if (dwc_ddrctl_cinit_seq_pre_qdyn_write(0) == false) {
                SNPS_LOG("Error in seq_pre_qdyn_write");
                return false;
            }

            /** - Write new read/write latency in controller register.*/
            dramset1tmg2.rd2wr = train_process.rd2wr;
            dramset1tmg2.wr2rd = train_process.wr2rd;
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG2, dramset1tmg2.value);
            SNPS_LOG("[Clr write][rd2wr] Min read to write command time: %d", train_process.rd2wr);
            SNPS_LOG("[Clr write][wr2rd] Min write to read command time: %d", train_process.wr2rd);

            dramset1tmg9.wr2rd_s = train_process.wr2rd_s;
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG9, dramset1tmg9.value);
            SNPS_LOG("[Clr write][wr2rd_s] Min write to read command time different bank group: %d", train_process.wr2rd_s);

            dramset1tmg22.t_rd2wr_dlr = train_process.rd2wr_dlr;
            dramset1tmg22.t_wr2rd_dlr = train_process.wr2rd_dlr;
            dwc_ddrctl_cinit_io_write32(REGB_FREQ_CH(n_freq, channel) + DRAMSET1TMG22, dramset1tmg22.value);
            SNPS_LOG("[Clr write][t_rd2wr_dlr] read to write switch to different logical rank in same physical rank: %d", train_process.rd2wr_dlr);
            SNPS_LOG("[Clr write][t_wr2rd_dlr] write to read switch to different logical rank in same physical rank: %d", train_process.wr2rd_dlr);

            set_rank_sw_timing_ctrl(n_freq, channel, &train_process);

            if (dwc_ddrctl_cinit_seq_post_qdyn_write(0) == false) {
                SNPS_LOG("Error in seq_post_qdyn_write");
                return false;
            }
        }
#ifndef DDR5_PHY
        if (dwc_ddrctl_phy_train_ctrl_delay() == false) {
            SNPS_LOG("Error writing the control delay");
            return false;
        }
#endif

        if (dwc_ddrctl_phy_train_wrdata_delay() == false) {
            SNPS_LOG("Error writing the wrdata delay");
            return false;
        }
    }

    SNPS_LOG("apply_phy_trained_value_ddr5 complete");
    SNPS_TRACE("Leaving");
    return true;
}

#endif /* CINIT_DDR5 */

#endif /* DDRCTL_DDR */
