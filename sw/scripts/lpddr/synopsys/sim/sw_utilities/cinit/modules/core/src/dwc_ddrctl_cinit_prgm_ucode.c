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
#include "dwc_ddrctl_cinit_prgm_ucode_reg.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_ddrctl_cinit_defines.h"

/** @brief method to program DDR5 low power microcode
 */
void dwc_ddrctl_cinit_prgm_ucode_load_lp(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_DDR
	uint32_t active_ranks;
	uint32_t dimm_type;
	uint32_t active_channels=DWC_DDRCTL_NUM_CHANNEL;

    dimm_type = cinit_cfg->spdData_m.module_type;

#ifdef MEMC_NUM_RANKS_GT_1
    active_ranks = cinit_cfg->memCtrlr_m.static_cfg.active_ranks;
#else
    active_ranks = 1;
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
	if(REGB_DDRC_CH0.chctl.dual_channel_en==0) {
            active_channels=1;
	}
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH

	SNPS_LOG("ucode: Channels %d DIMM %d, Ranks %d", active_channels, dimm_type, active_ranks);

	MPC_UCODE_t MC_ZQCALSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALSTART[i].cmd_code = MPC_CMD;
		MC_ZQCALSTART[i].last_cmd = 1;
		MC_ZQCALSTART[i].op = 5; // OP (ZQCal Start)
	}

	MC_ZQCALSTART[0].csn_sel = RANK0_SEL;
	MC_ZQCALSTART[1].csn_sel = RANK1_SEL;
	MC_ZQCALSTART[2].csn_sel = RANK2_SEL;
	MC_ZQCALSTART[3].csn_sel = RANK3_SEL;
	MC_ZQCALSTART[4].csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_ZQCALLATCH[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALLATCH[i].cmd_code = MPC_CMD;
		MC_ZQCALLATCH[i].last_cmd = 0;
		MC_ZQCALLATCH[i].op = 4; // OP
	}

	MC_ZQCALLATCH[0].csn_sel = RANK0_SEL;
	MC_ZQCALLATCH[1].csn_sel = RANK1_SEL;
	MC_ZQCALLATCH[2].csn_sel = RANK2_SEL;
	MC_ZQCALLATCH[3].csn_sel = RANK3_SEL;
	MC_ZQCALLATCH[4].csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_DQSOSCSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_DQSOSCSTART[i].cmd_code = MPC_CMD;
		MC_DQSOSCSTART[i].last_cmd = 1;
		MC_DQSOSCSTART[i].op = 7; // OP
	}

	MC_DQSOSCSTART[0].csn_sel = RANK0_SEL;
	MC_DQSOSCSTART[1].csn_sel = RANK1_SEL;
	MC_DQSOSCSTART[2].csn_sel = RANK2_SEL;
	MC_DQSOSCSTART[3].csn_sel = RANK3_SEL;
	MC_DQSOSCSTART[4].csn_sel = RANK_R15_SEL;

	MRR_UCODE_t MC_MRR[4][2][48];

	for (uint32_t i = 0; i < 4; i++) {
        for (uint32_t j = 0; j < 2; j++) {
		    for (uint32_t k = 46; k < 48; k++) {
			    MC_MRR[i][j][k].cmd_code = MRR_CMD;
			    MC_MRR[i][j][k].prank_num = i;
			    MC_MRR[i][j][k].phy_snoop_en = j;
			    MC_MRR[i][j][k].prank_sel = 0;
			    MC_MRR[i][j][k].last_cmd = 1;
			    MC_MRR[i][j][k].mra = k;
            }
	    }
    }

	MRR_UCODE_t MC_MRR4[4];

	for (uint32_t i = 0; i < 4; i++) {
		MC_MRR4[i].cmd_code = MRR_CMD;
		MC_MRR4[i].prank_num = i;
		MC_MRR4[i].phy_snoop_en = 0;
		MC_MRR4[i].prank_sel = 0;
		MC_MRR4[i].last_cmd = 1;
		MC_MRR4[i].mra = 4;
	}

	SRE_UCODE_t MC_SRE[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRE[i].cmd_code = SRE_CMD;
		MC_SRE[i].last_cmd = 1;
		MC_SRE[i].freq_change = 0;
		MC_SRE[i].wait_type = 1;
		MC_SRE[i].wait_reg = 2; //tCPDED
	}

	MC_SRE[0].csn_sel = RANK0_SEL;
	MC_SRE[1].csn_sel = RANK1_SEL;
	MC_SRE[2].csn_sel = RANK2_SEL;
	MC_SRE[3].csn_sel = RANK3_SEL;
	MC_SRE[4].csn_sel = RANK0_1_SEL;
	MC_SRE[5].csn_sel = RANK2_3_SEL;
	MC_SRE[6].csn_sel = RANK_ALL_SEL;
	MC_SRE[7].csn_sel = RANK_R15_SEL;

	SRX_UCODE_t MC_SRX[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRX[i].cmd_code = SRX_CMD;
		MC_SRX[i].last_cmd = 1;
		MC_SRX[i].wait_type = 1;
		MC_SRX[i].wait_reg = 8; //tXS
	}

	MC_SRX[0].csn_sel = RANK0_SEL;
	MC_SRX[1].csn_sel = RANK1_SEL;
	MC_SRX[2].csn_sel = RANK2_SEL;
	MC_SRX[3].csn_sel = RANK3_SEL;
	MC_SRX[4].csn_sel = RANK0_1_SEL;
	MC_SRX[5].csn_sel = RANK2_3_SEL;
	MC_SRX[6].csn_sel = RANK_ALL_SEL;
	MC_SRX[7].csn_sel = RANK_R15_SEL;

	PDE_UCODE_t MC_PDE[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDE[i].cmd_code = PDE_CMD;
		MC_PDE[i].last_cmd = 1;
		MC_PDE[i].wait_type = 1;
		MC_PDE[i].wait_cycle = 2; //tCPDED
	}

	MC_PDE[0].csn_sel = RANK0_SEL;
	MC_PDE[1].csn_sel = RANK1_SEL;
	MC_PDE[2].csn_sel = RANK2_SEL;
	MC_PDE[3].csn_sel = RANK3_SEL;
	MC_PDE[4].csn_sel = RANK_R15_SEL;

	PDX_UCODE_t MC_PDX[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDX[i].cmd_code = PDX_CMD;
		MC_PDX[i].last_cmd = 0;
		MC_PDX[i].wait_type = 1;
		MC_PDX[i].wait_reg = 7; //tXP
	}

	MC_PDX[0].csn_sel = RANK0_SEL;
	MC_PDX[1].csn_sel = RANK1_SEL;
	MC_PDX[2].csn_sel = RANK2_SEL;
	MC_PDX[3].csn_sel = RANK3_SEL;
	MC_PDX[4].csn_sel = RANK_R15_SEL;

	NOP_UCODE_t MC_NOP[8][2];

	for (uint32_t i = 0; i < 8; i++) {
		for (uint32_t j = 0; j < 2; j++) {
			MC_NOP[i][j].cmd_code = NOP_CMD;
			MC_NOP[i][j].last_cmd = 1;
			MC_NOP[i][j]._RESERVED = 0;
			MC_NOP[i][j].nop_len = j;
		}
	}

	for (uint32_t i = 0; i < 2; i++) {
		MC_NOP[0][i].csn_sel = RANK0_SEL;
		MC_NOP[1][i].csn_sel = RANK1_SEL;
		MC_NOP[2][i].csn_sel = RANK2_SEL;
		MC_NOP[3][i].csn_sel = RANK3_SEL;
		MC_NOP[4][i].csn_sel = RANK0_1_SEL;
		MC_NOP[5][i].csn_sel = RANK2_3_SEL;
		MC_NOP[6][i].csn_sel = RANK_ALL_SEL;
		MC_NOP[7][i].csn_sel = RANK_R15_SEL;
	}

	DES_UCODE_t MC_DES;

	MC_DES.cmd_code = DES_CMD;
	MC_DES.last_cmd = 1;
	MC_DES.unit_sel = 0;
	MC_DES.unit_count = 1;

	IWAIT_REG_UCODE_t MC_IWAITCAPARRETRYWINDOW;

	MC_IWAITCAPARRETRYWINDOW.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITCAPARRETRYWINDOW.wait_type = 1;
	MC_IWAITCAPARRETRYWINDOW._RESERVED = 0;
	MC_IWAITCAPARRETRYWINDOW.wait_reg = 15;

	IWAIT_REG_UCODE_t MC_IWAITTSTAB;

	MC_IWAITTSTAB.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTSTAB.wait_type = 1;
	MC_IWAITTSTAB._RESERVED = 0;
	MC_IWAITTSTAB.wait_reg = 14;

	IWAIT_REG_UCODE_t MC_IWAITTSRFEXITSTAGGER;

	MC_IWAITTSRFEXITSTAGGER.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTSRFEXITSTAGGER.wait_type = 1;
	MC_IWAITTSRFEXITSTAGGER._RESERVED = 0;
	MC_IWAITTSRFEXITSTAGGER.wait_reg = 13;

	IWAIT_REG_UCODE_t MC_IWAITTCKOFF;

	MC_IWAITTCKOFF.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTCKOFF.wait_type = 1;
	MC_IWAITTCKOFF._RESERVED = 0;
	MC_IWAITTCKOFF.wait_reg = 12;

	IWAIT_REG_UCODE_t MC_IWAITTZQLAT;

	MC_IWAITTZQLAT.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQLAT.wait_type = 1;
	MC_IWAITTZQLAT._RESERVED = 0;
	MC_IWAITTZQLAT.wait_reg = 11;

	IWAIT_REG_UCODE_t MC_IWAITTZQCAL;

	MC_IWAITTZQCAL.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQCAL.wait_type = 1;
	MC_IWAITTZQCAL._RESERVED = 0;
	MC_IWAITTZQCAL.wait_reg = 10;

	IWAIT_REG_UCODE_t MC_IWAITTMR;

	MC_IWAITTMR.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTMR.wait_type = 1;
	MC_IWAITTMR._RESERVED = 0;
	MC_IWAITTMR.wait_reg = 3;

	IWAIT_TIME_UCODE_t MC_IWAITTRKCALCCUR;

	MC_IWAITTRKCALCCUR.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTRKCALCCUR.wait_type = 0;
	MC_IWAITTRKCALCCUR.wait_unit = 1;
	MC_IWAITTRKCALCCUR.wait_time = 10;
	if (ddrctl_sw_get_ratio(cinit_cfg, 0) == DWC_RATIO_1_4 ) {
		MC_IWAITTRKCALCCUR.wait_time = DIV_2(MC_IWAITTRKCALCCUR.wait_time);
	}

	IWAIT_TIME_UCODE_t MC_IWAITTIME[32];

	MC_IWAITTIME[0].cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTIME[0].wait_type = 0;
	MC_IWAITTIME[0].wait_unit = 0;
	MC_IWAITTIME[0].wait_time = 0;
	MC_IWAITTIME[1].cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTIME[1].wait_type = 0;
	MC_IWAITTIME[1].wait_unit = 0;
	MC_IWAITTIME[1].wait_time = 1;
	MC_IWAITTIME[31].cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTIME[31].wait_type = 0;
	MC_IWAITTIME[31].wait_unit = 0;
	MC_IWAITTIME[31].wait_time = 31;

	IWAIT_TIME_UCODE_t MC_IWAITDELAYPIPES;

	MC_IWAITDELAYPIPES.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITDELAYPIPES.wait_type = 0;
	MC_IWAITDELAYPIPES.wait_unit = 0;
	MC_IWAITDELAYPIPES.wait_time = DDRCTL_DCH_SYNC_DELAY_PIPES;

	IWAIT_SIG_UCODE_t MC_IWAITCHANNELMESSAGE[4][2];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 0; j < 2; j++) {
			MC_IWAITCHANNELMESSAGE[i][j].cmd_code = IWAIT_SIG_CMD;
			MC_IWAITCHANNELMESSAGE[i][j].sig_value = j;
			MC_IWAITCHANNELMESSAGE[i][j].sig_sel = 16 + i;
			MC_IWAITCHANNELMESSAGE[i][j].wait_cycle = 0;
		}
	}

	IWAIT_SIG_UCODE_t MC_IWAITDQSOSCACK;

	MC_IWAITDQSOSCACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITDQSOSCACK.sig_value = 1;
	MC_IWAITDQSOSCACK.sig_sel = 5;
	MC_IWAITDQSOSCACK.wait_cycle = 0;

	IWAIT_SIG_UCODE_t MC_IWAITTZQCALACK;

	MC_IWAITTZQCALACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITTZQCALACK.sig_value = 1;
	MC_IWAITTZQCALACK.sig_sel = 4;
	MC_IWAITTZQCALACK.wait_cycle = 0;

	IWAIT_SIG_UCODE_t MC_IWAITTXSDLLACK;

	MC_IWAITTXSDLLACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITTXSDLLACK.sig_value = 1;
	MC_IWAITTXSDLLACK.sig_sel = 3;
	MC_IWAITTXSDLLACK.wait_cycle = 0;

	IWAIT_SIG_UCODE_t MC_IWAITTXSACK;

	MC_IWAITTXSACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITTXSACK.sig_value = 1;
	MC_IWAITTXSACK.sig_sel = 2;
	MC_IWAITTXSACK.wait_cycle = 0;

	IWAIT_SIG_UCODE_t MC_IWAITDFILPIDLE;

	MC_IWAITDFILPIDLE.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITDFILPIDLE.sig_value = 0;
	MC_IWAITDFILPIDLE.sig_sel = 0;
	MC_IWAITDFILPIDLE.wait_cycle = 0;

	MOV_UCODE_t MC_MOVCSn2R15;

	MC_MOVCSn2R15.cmd_code = MOV_CMD;
	MC_MOVCSn2R15.mov_dir = 1;
	MC_MOVCSn2R15.mov_type = 0;
	MC_MOVCSn2R15._RESERVED = 0;
	MC_MOVCSn2R15.reg_num = 15;

	MOV_UCODE_t MC_MOVCSn2R0[6];

	MC_MOVCSn2R0[4].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[4].mov_dir = 0;
	MC_MOVCSn2R0[4].mov_type = 1;
	MC_MOVCSn2R0[4]._RESERVED = 0;
	MC_MOVCSn2R0[4].reg_num = 4;
	MC_MOVCSn2R0[5].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[5].mov_dir = 0;
	MC_MOVCSn2R0[5].mov_type = 1;
	MC_MOVCSn2R0[5]._RESERVED = 0;
	MC_MOVCSn2R0[5].reg_num = 5;

	IMM_BIT_UCODE_t MC_SETDUALCHOPMODE;

	MC_SETDUALCHOPMODE.cmd_code = IMM_BIT_CMD;
	MC_SETDUALCHOPMODE.imm_type = 0;
	MC_SETDUALCHOPMODE._RESERVED = 0;
	MC_SETDUALCHOPMODE.reg_sel = 3;
	MC_SETDUALCHOPMODE.bit_loc = 7;
	MC_SETDUALCHOPMODE.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARDUALCHOPMODE;

	MC_CLEARDUALCHOPMODE.cmd_code = IMM_BIT_CMD;
	MC_CLEARDUALCHOPMODE.imm_type = 0;
	MC_CLEARDUALCHOPMODE._RESERVED = 0;
	MC_CLEARDUALCHOPMODE.reg_sel = 3;
	MC_CLEARDUALCHOPMODE.bit_loc = 7;
	MC_CLEARDUALCHOPMODE.bit_val = 0;

	IMM_BIT_UCODE_t MC_STOREDQSOSCSTART;

	MC_STOREDQSOSCSTART.cmd_code = IMM_BIT_CMD;
	MC_STOREDQSOSCSTART.imm_type = 0;
	MC_STOREDQSOSCSTART._RESERVED = 0;
	MC_STOREDQSOSCSTART.reg_sel = 3;
	MC_STOREDQSOSCSTART.bit_loc = 5;
	MC_STOREDQSOSCSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARDQSOSCSTART;

	MC_CLEARDQSOSCSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARDQSOSCSTART.imm_type = 0;
	MC_CLEARDQSOSCSTART._RESERVED = 0;
	MC_CLEARDQSOSCSTART.reg_sel = 3;
	MC_CLEARDQSOSCSTART.bit_loc = 5;
	MC_CLEARDQSOSCSTART.bit_val = 0;

	IMM_BIT_UCODE_t MC_STORETZQCALSTART;

	MC_STORETZQCALSTART.cmd_code = IMM_BIT_CMD;
	MC_STORETZQCALSTART.imm_type = 0;
	MC_STORETZQCALSTART._RESERVED = 0;
	MC_STORETZQCALSTART.reg_sel = 3;
	MC_STORETZQCALSTART.bit_loc = 4;
	MC_STORETZQCALSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARTZQCALSTART;

	MC_CLEARTZQCALSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARTZQCALSTART.imm_type = 0;
	MC_CLEARTZQCALSTART._RESERVED = 0;
	MC_CLEARTZQCALSTART.reg_sel = 3;
	MC_CLEARTZQCALSTART.bit_loc = 4;
	MC_CLEARTZQCALSTART.bit_val = 0;

	IMM_BIT_UCODE_t MC_STORETXSDLLSTART;

	MC_STORETXSDLLSTART.cmd_code = IMM_BIT_CMD;
	MC_STORETXSDLLSTART.imm_type = 0;
	MC_STORETXSDLLSTART._RESERVED = 0;
	MC_STORETXSDLLSTART.reg_sel = 3;
	MC_STORETXSDLLSTART.bit_loc = 3;
	MC_STORETXSDLLSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARTXSDLLSTART;

	MC_CLEARTXSDLLSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARTXSDLLSTART.imm_type = 0;
	MC_CLEARTXSDLLSTART._RESERVED = 0;
	MC_CLEARTXSDLLSTART.reg_sel = 3;
	MC_CLEARTXSDLLSTART.bit_loc = 3;
	MC_CLEARTXSDLLSTART.bit_val = 0;

	IMM_BIT_UCODE_t MC_STORETXSSTART;

	MC_STORETXSSTART.cmd_code = IMM_BIT_CMD;
	MC_STORETXSSTART.imm_type = 0;
	MC_STORETXSSTART._RESERVED = 0;
	MC_STORETXSSTART.reg_sel = 3;
	MC_STORETXSSTART.bit_loc = 2;
	MC_STORETXSSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARTXSSTART;

	MC_CLEARTXSSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARTXSSTART.imm_type = 0;
	MC_CLEARTXSSTART._RESERVED = 0;
	MC_CLEARTXSSTART.reg_sel = 3;
	MC_CLEARTXSSTART.bit_loc = 2;
	MC_CLEARTXSSTART.bit_val = 0;

	IMM_BIT_UCODE_t MC_STORECHANNELMESSAGE[4];

	for (uint32_t i = 0; i < 4; i++) {
		MC_STORECHANNELMESSAGE[i].cmd_code = IMM_BIT_CMD;
		MC_STORECHANNELMESSAGE[i].imm_type = 0;
		MC_STORECHANNELMESSAGE[i]._RESERVED = 0;
		MC_STORECHANNELMESSAGE[i].reg_sel = 2;
		MC_STORECHANNELMESSAGE[i].bit_loc = i;
		MC_STORECHANNELMESSAGE[i].bit_val = 1;
	}

	IMM_BIT_UCODE_t MC_CLEARCHANNELMESSAGE[4];

	for (uint32_t i = 0; i < 4; i++) {
		MC_CLEARCHANNELMESSAGE[i].cmd_code = IMM_BIT_CMD;
		MC_CLEARCHANNELMESSAGE[i].imm_type = 0;
		MC_CLEARCHANNELMESSAGE[i]._RESERVED = 0;
		MC_CLEARCHANNELMESSAGE[i].reg_sel = 2;
		MC_CLEARCHANNELMESSAGE[i].bit_loc = i;
		MC_CLEARCHANNELMESSAGE[i].bit_val = 0;
	}

	DISDQ_UCODE_t MC_DISDQ[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_DISDQ[i].cmd_code = DISDQ_CMD;
		MC_DISDQ[i].last_cmd = 1;
		MC_DISDQ[i]._RESERVED = 0;
		MC_DISDQ[i].disdqset = 1;
		MC_DISDQ[i].disdqreset = 0;
	}

	MC_DISDQ[0].csn_sel = RANK0_SEL;
	MC_DISDQ[1].csn_sel = RANK1_SEL;
	MC_DISDQ[2].csn_sel = RANK2_SEL;
	MC_DISDQ[3].csn_sel = RANK3_SEL;
	MC_DISDQ[4].csn_sel = RANK_R15_SEL;

	DISDQ_UCODE_t MC_ENDQ[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ENDQ[i].cmd_code = DISDQ_CMD;
		MC_ENDQ[i].last_cmd = 1;
		MC_ENDQ[i]._RESERVED = 0;
		MC_ENDQ[i].disdqset = 0;
		MC_ENDQ[i].disdqreset = 1;
	}

	MC_ENDQ[0].csn_sel = RANK0_SEL;
	MC_ENDQ[1].csn_sel = RANK1_SEL;
	MC_ENDQ[2].csn_sel = RANK2_SEL;
	MC_ENDQ[3].csn_sel = RANK3_SEL;
	MC_ENDQ[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PAUSEREF[i].cmd_code = PAUSEREF_CMD;
		MC_PAUSEREF[i].last_cmd = 1;
		MC_PAUSEREF[i]._RESERVED = 0;
		MC_PAUSEREF[i].pausereftype = 0;
		MC_PAUSEREF[i].pauserefset = 1;
		MC_PAUSEREF[i].pauserefreset = 0;
	}

	MC_PAUSEREF[0].csn_sel = RANK0_SEL;
	MC_PAUSEREF[1].csn_sel = RANK1_SEL;
	MC_PAUSEREF[2].csn_sel = RANK2_SEL;
	MC_PAUSEREF[3].csn_sel = RANK3_SEL;
	MC_PAUSEREF[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_BLOCKREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_BLOCKREF[i].cmd_code = PAUSEREF_CMD;
		MC_BLOCKREF[i].last_cmd = 1;
		MC_BLOCKREF[i]._RESERVED = 0;
		MC_BLOCKREF[i].pausereftype = 1;
		MC_BLOCKREF[i].pauserefset = 1;
		MC_BLOCKREF[i].pauserefreset = 0;
	}

	MC_BLOCKREF[0].csn_sel = RANK0_SEL;
	MC_BLOCKREF[1].csn_sel = RANK1_SEL;
	MC_BLOCKREF[2].csn_sel = RANK2_SEL;
	MC_BLOCKREF[3].csn_sel = RANK3_SEL;
	MC_BLOCKREF[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_RESUMEREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_RESUMEREF[i].cmd_code = PAUSEREF_CMD;
		MC_RESUMEREF[i].last_cmd = 1;
		MC_RESUMEREF[i]._RESERVED = 0;
		MC_RESUMEREF[i].pausereftype = 0;
		MC_RESUMEREF[i].pauserefset = 0;
		MC_RESUMEREF[i].pauserefreset = 1;
	}

	MC_RESUMEREF[0].csn_sel = RANK0_SEL;
	MC_RESUMEREF[1].csn_sel = RANK1_SEL;
	MC_RESUMEREF[2].csn_sel = RANK2_SEL;
	MC_RESUMEREF[3].csn_sel = RANK3_SEL;
	MC_RESUMEREF[4].csn_sel = RANK_R15_SEL;

	SRX_DONE_UCODE_t MC_SRXDONETXSDLL[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRXDONETXSDLL[i].cmd_code = SRX_DONE_CMD;
		MC_SRXDONETXSDLL[i].last_cmd = 1;
		MC_SRXDONETXSDLL[i]._RESERVED = 0;
		MC_SRXDONETXSDLL[i].srx_done_txsdll = 1;
		MC_SRXDONETXSDLL[i].srx_done_txs = 0;
	}

	MC_SRXDONETXSDLL[0].csn_sel = RANK0_SEL;
	MC_SRXDONETXSDLL[1].csn_sel = RANK1_SEL;
	MC_SRXDONETXSDLL[2].csn_sel = RANK2_SEL;
	MC_SRXDONETXSDLL[3].csn_sel = RANK3_SEL;
	MC_SRXDONETXSDLL[4].csn_sel = RANK0_1_SEL;
	MC_SRXDONETXSDLL[5].csn_sel = RANK2_3_SEL;
	MC_SRXDONETXSDLL[6].csn_sel = RANK_ALL_SEL;
	MC_SRXDONETXSDLL[7].csn_sel = RANK_R15_SEL;

	SRX_DONE_UCODE_t MC_SRXDONETXS[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRXDONETXS[i].cmd_code = SRX_DONE_CMD;
		MC_SRXDONETXS[i].last_cmd = 1;
		MC_SRXDONETXS[i]._RESERVED = 0;
		MC_SRXDONETXS[i].srx_done_txsdll = 0;
		MC_SRXDONETXS[i].srx_done_txs = 1;
	}

	MC_SRXDONETXS[0].csn_sel = RANK0_SEL;
	MC_SRXDONETXS[1].csn_sel = RANK1_SEL;
	MC_SRXDONETXS[2].csn_sel = RANK2_SEL;
	MC_SRXDONETXS[3].csn_sel = RANK3_SEL;
	MC_SRXDONETXS[4].csn_sel = RANK0_1_SEL;
	MC_SRXDONETXS[5].csn_sel = RANK2_3_SEL;
	MC_SRXDONETXS[6].csn_sel = RANK_ALL_SEL;
	MC_SRXDONETXS[7].csn_sel = RANK_R15_SEL;

	PDX_MPSMX_DONE_UCODE_t MC_PDXDONE[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDXDONE[i].cmd_code = PDX_MPSMX_DONE_CMD;
		MC_PDXDONE[i].last_cmd = 1;
		MC_PDXDONE[i]._RESERVED = 0;
		MC_PDXDONE[i].mpsmx_done = 0;
		MC_PDXDONE[i].pdx_done = 1;
	}

	MC_PDXDONE[0].csn_sel = RANK0_SEL;
	MC_PDXDONE[1].csn_sel = RANK1_SEL;
	MC_PDXDONE[2].csn_sel = RANK2_SEL;
	MC_PDXDONE[3].csn_sel = RANK3_SEL;
	MC_PDXDONE[4].csn_sel = RANK_R15_SEL;

	CTRLUPD_UCODE_t MC_CTRLUPD;

	MC_CTRLUPD.cmd_code = CTRLUPD_CMD;
	MC_CTRLUPD.last_cmd = 1;
	MC_CTRLUPD.dfi_ctrlupd_req_set = 1;
	MC_CTRLUPD.dfi_ctrlupd_retry_en = 0;
	MC_CTRLUPD.wait_unit = 0;
	MC_CTRLUPD.wait_time = 0;

	PRANK_PREAB_UCODE_t MC_PRANKPREAB[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PRANKPREAB[i].cmd_code = PRANK_PREAB_CMD;
		MC_PRANKPREAB[i].last_cmd = 1;
		MC_PRANKPREAB[i]._RESERVED = 0;
		MC_PRANKPREAB[i].wait_type = 1;
		MC_PRANKPREAB[i].wait_reg = 6;
	}

	MC_PRANKPREAB[0].csn_sel = RANK0_SEL;
	MC_PRANKPREAB[1].csn_sel = RANK1_SEL;
	MC_PRANKPREAB[2].csn_sel = RANK2_SEL;
	MC_PRANKPREAB[3].csn_sel = RANK3_SEL;
	MC_PRANKPREAB[4].csn_sel = RANK_R15_SEL;

	PRANK_REFAB_UCODE_t MC_PRANKREFAB[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PRANKREFAB[i].cmd_code = PRANK_REFAB_CMD;
		MC_PRANKREFAB[i].last_cmd = 1;
		MC_PRANKREFAB[i]._RESERVED = 0;
		MC_PRANKREFAB[i].wait_type = 1;
		MC_PRANKREFAB[i].wait_reg = 4;
	}

	MC_PRANKREFAB[0].csn_sel = RANK0_SEL;
	MC_PRANKREFAB[1].csn_sel = RANK1_SEL;
	MC_PRANKREFAB[2].csn_sel = RANK2_SEL;
	MC_PRANKREFAB[3].csn_sel = RANK3_SEL;
	MC_PRANKREFAB[4].csn_sel = RANK_R15_SEL;

	REF_FLUSH_UCODE_t MC_REFFLUSH[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_REFFLUSH[i].cmd_code = REF_FLUSH_CMD;
		MC_REFFLUSH[i].last_cmd = 1;
		MC_REFFLUSH[i]._RESERVED = 0;
		MC_REFFLUSH[i].ref_flush_req_set = 1;
	}

	MC_REFFLUSH[0].csn_sel = RANK0_SEL;
	MC_REFFLUSH[1].csn_sel = RANK1_SEL;
	MC_REFFLUSH[2].csn_sel = RANK2_SEL;
	MC_REFFLUSH[3].csn_sel = RANK3_SEL;
	MC_REFFLUSH[4].csn_sel = RANK0_1_SEL;
	MC_REFFLUSH[5].csn_sel = RANK2_3_SEL;
	MC_REFFLUSH[6].csn_sel = RANK_ALL_SEL;
	MC_REFFLUSH[7].csn_sel = RANK_R15_SEL;

	FORCE_CS_UCODE_t MC_FORCECSX[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_FORCECSX[i].cmd_code = FORCE_CS_CMD;
		MC_FORCECSX[i].last_cmd = 1;
		MC_FORCECSX[i]._RESERVED = 0;
		MC_FORCECSX[i].force_csx = 1;
		MC_FORCECSX[i].force_cse = 0;
	}

	MC_FORCECSX[0].csn_sel = RANK0_SEL;
	MC_FORCECSX[1].csn_sel = RANK1_SEL;
	MC_FORCECSX[2].csn_sel = RANK2_SEL;
	MC_FORCECSX[3].csn_sel = RANK3_SEL;
	MC_FORCECSX[4].csn_sel = RANK0_1_SEL;
	MC_FORCECSX[5].csn_sel = RANK2_3_SEL;
	MC_FORCECSX[6].csn_sel = RANK_ALL_SEL;
	MC_FORCECSX[7].csn_sel = RANK_R15_SEL;

	FORCE_CS_UCODE_t MC_FORCECSE[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_FORCECSE[i].cmd_code = FORCE_CS_CMD;
		MC_FORCECSE[i].last_cmd = 1;
		MC_FORCECSE[i]._RESERVED = 0;
		MC_FORCECSE[i].force_csx = 0;
		MC_FORCECSE[i].force_cse = 1;
	}

	MC_FORCECSE[0].csn_sel = RANK0_SEL;
	MC_FORCECSE[1].csn_sel = RANK1_SEL;
	MC_FORCECSE[2].csn_sel = RANK2_SEL;
	MC_FORCECSE[3].csn_sel = RANK3_SEL;
	MC_FORCECSE[4].csn_sel = RANK0_1_SEL;
	MC_FORCECSE[5].csn_sel = RANK2_3_SEL;
	MC_FORCECSE[6].csn_sel = RANK_ALL_SEL;
	MC_FORCECSE[7].csn_sel = RANK_R15_SEL;

	LOCK_CTRL_UCODE_t MC_RESETSEQONGOING;

	MC_RESETSEQONGOING.cmd_code = LOCK_CTRL_CMD;
	MC_RESETSEQONGOING._RESERVED = 0;
	MC_RESETSEQONGOING.reset_ucode_seq_ongoing_flag = 1;
	MC_RESETSEQONGOING.set_ucode_seq_ongoing_flag = 0;
	MC_RESETSEQONGOING.reset_urgent_flag = 0;
	MC_RESETSEQONGOING.set_urgent_flag = 0;
	MC_RESETSEQONGOING.unlock_ci_bus = 0;
	MC_RESETSEQONGOING.lock_ci_bus = 0;

	LOCK_CTRL_UCODE_t MC_SETSEQONGOING;

	MC_SETSEQONGOING.cmd_code = LOCK_CTRL_CMD;
	MC_SETSEQONGOING._RESERVED = 0;
	MC_SETSEQONGOING.reset_ucode_seq_ongoing_flag = 0;
	MC_SETSEQONGOING.set_ucode_seq_ongoing_flag = 1;
	MC_SETSEQONGOING.reset_urgent_flag = 0;
	MC_SETSEQONGOING.set_urgent_flag = 0;
	MC_SETSEQONGOING.unlock_ci_bus = 0;
	MC_SETSEQONGOING.lock_ci_bus = 0;

	LOCK_CTRL_UCODE_t MC_UNLOCKCTRL;

	MC_UNLOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_UNLOCKCTRL._RESERVED = 0;
	MC_UNLOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.reset_urgent_flag = 0;
	MC_UNLOCKCTRL.set_urgent_flag = 0;
	MC_UNLOCKCTRL.unlock_ci_bus = 1;
	MC_UNLOCKCTRL.lock_ci_bus = 0;

	LOCK_CTRL_UCODE_t MC_LOCKCTRL;

	MC_LOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_LOCKCTRL._RESERVED = 0;
	MC_LOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.reset_urgent_flag = 0;
	MC_LOCKCTRL.set_urgent_flag = 0;
	MC_LOCKCTRL.unlock_ci_bus = 0;
	MC_LOCKCTRL.lock_ci_bus = 1;

	DFICLK_UCODE_t MC_DFICLKENCTRL;

	MC_DFICLKENCTRL.cmd_code = DFI_CLK_CMD;
	MC_DFICLKENCTRL.last_cmd = 1;
	MC_DFICLKENCTRL.csn_sel = RANK_ALL_SEL;
	MC_DFICLKENCTRL._RESERVED = 0;
	MC_DFICLKENCTRL.dfi_ck_disable_clear = 1;
	MC_DFICLKENCTRL.dfi_ck_disable_set = 0;

	DFICLK_UCODE_t MC_DFICLKDISCTRL;

	MC_DFICLKDISCTRL.cmd_code = DFI_CLK_CMD;
	MC_DFICLKDISCTRL.last_cmd = 1;
	MC_DFICLKDISCTRL.csn_sel = RANK_ALL_SEL;
	MC_DFICLKDISCTRL._RESERVED = 0;
	MC_DFICLKDISCTRL.dfi_ck_disable_clear = 0;
	MC_DFICLKDISCTRL.dfi_ck_disable_set = 1;

	NTODT_CTRL_UCODE_t MC_NTODTENCTRL[4];

	for (uint32_t i = 0; i < 4; i++) {
		MC_NTODTENCTRL[i].cmd_code = NTODT_CTRL_CMD;
		MC_NTODTENCTRL[i].last_cmd = 1;
		MC_NTODTENCTRL[i]._RESERVED = 0;
		MC_NTODTENCTRL[i].ntodt_dis_ctrl = 0;
		MC_NTODTENCTRL[i].ntodt_en_ctrl = 1;
	}

	MC_NTODTENCTRL[0].csn_sel = RANK0_SEL;
	MC_NTODTENCTRL[1].csn_sel = RANK1_SEL;
	MC_NTODTENCTRL[2].csn_sel = RANK2_SEL;
	MC_NTODTENCTRL[3].csn_sel = RANK3_SEL;

	JPC_UCODE_t MC_JPC4CAPARRETRY[2];

	for (uint32_t i = 1; i < 2; i++) {
		MC_JPC4CAPARRETRY[i].cmd_code = JPC_CMD;
		MC_JPC4CAPARRETRY[i].sig_value = 1;
		MC_JPC4CAPARRETRY[i].sig_sel = 18;
		MC_JPC4CAPARRETRY[i].jmp_dir = 0;
		MC_JPC4CAPARRETRY[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4STAGGERCS[4];

	for (uint32_t i = 1; i < 4; i++) {
		MC_JPC4STAGGERCS[i].cmd_code = JPC_CMD;
		MC_JPC4STAGGERCS[i].sig_value = 1;
		MC_JPC4STAGGERCS[i].sig_sel = 17;
		MC_JPC4STAGGERCS[i].jmp_dir = 0;
		MC_JPC4STAGGERCS[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4DIMMSRFCLKSTOP[2][6];

	for (uint32_t i = 0; i < 2; i++) {
		for (uint32_t j = 1; j < 6; j++) {
			MC_JPC4DIMMSRFCLKSTOP[i][j].cmd_code = JPC_CMD;
			MC_JPC4DIMMSRFCLKSTOP[i][j].sig_value = i;
			MC_JPC4DIMMSRFCLKSTOP[i][j].sig_sel = 16;
			MC_JPC4DIMMSRFCLKSTOP[i][j].jmp_dir = 0;
			MC_JPC4DIMMSRFCLKSTOP[i][j].jmp_step = j;
		}
	}

	JPC_UCODE_t MC_JPC4DISDQSOSC[22];

	for (uint32_t i = 1; i < 22; i++) {
		MC_JPC4DISDQSOSC[i].cmd_code = JPC_CMD;
		MC_JPC4DISDQSOSC[i].sig_value = 0;
		MC_JPC4DISDQSOSC[i].sig_sel = 14;
		MC_JPC4DISDQSOSC[i].jmp_dir = 0;
		MC_JPC4DISDQSOSC[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4ZQRESISTORSHARED[2];

	for (uint32_t i = 0; i < 2; i++) {
		MC_JPC4ZQRESISTORSHARED[i].cmd_code = JPC_CMD;
		MC_JPC4ZQRESISTORSHARED[i].sig_sel = 13;
		MC_JPC4ZQRESISTORSHARED[i].jmp_dir = 0;
	}

	MC_JPC4ZQRESISTORSHARED[0].jmp_step = 9;
	MC_JPC4ZQRESISTORSHARED[0].sig_value = 0;
	MC_JPC4ZQRESISTORSHARED[1].jmp_step = 35;
	MC_JPC4ZQRESISTORSHARED[1].sig_value = 1;

	JPC_UCODE_t MC_JPC4DISZQCALRDIMM[2];

	for (uint32_t i = 0; i < 2; i++) {
		MC_JPC4DISZQCALRDIMM[i].cmd_code = JPC_CMD;
		MC_JPC4DISZQCALRDIMM[i].sig_value = i;
		MC_JPC4DISZQCALRDIMM[i].sig_sel = 12;
		MC_JPC4DISZQCALRDIMM[i].jmp_dir = 0;
	}

	MC_JPC4DISZQCALRDIMM[0].jmp_step = 8;
	MC_JPC4DISZQCALRDIMM[1].jmp_step = 2;

	JPC_UCODE_t MC_JPC4DISZQCALNODIMM[2];

	for (uint32_t i = 0; i < 2; i++) {
		MC_JPC4DISZQCALNODIMM[i].cmd_code = JPC_CMD;
		MC_JPC4DISZQCALNODIMM[i].sig_value = i;
		MC_JPC4DISZQCALNODIMM[i].sig_sel = 12;
		MC_JPC4DISZQCALNODIMM[i].jmp_dir = 0;
	}

	MC_JPC4DISZQCALNODIMM[0].jmp_step = 45;
	MC_JPC4DISZQCALNODIMM[1].jmp_step = 2;

	JPC_UCODE_t MC_JPC4CTRLUPDPRESRX[2][4];

	for (uint32_t i = 0; i < 2; i++) {
		for (uint32_t j = 1; j < 4; j++) {
			MC_JPC4CTRLUPDPRESRX[i][j].cmd_code = JPC_CMD;
			MC_JPC4CTRLUPDPRESRX[i][j].sig_value = i;
			MC_JPC4CTRLUPDPRESRX[i][j].sig_sel = 11;
			MC_JPC4CTRLUPDPRESRX[i][j].jmp_dir = 0;
			MC_JPC4CTRLUPDPRESRX[i][j].jmp_step = j;
		}
	}

	JPC_UCODE_t MC_JPC4DISCTRLUPD[4];

	for (uint32_t i = 1; i < 4; i++) {
		MC_JPC4DISCTRLUPD[i].cmd_code = JPC_CMD;
		MC_JPC4DISCTRLUPD[i].sig_value = 0;
		MC_JPC4DISCTRLUPD[i].sig_sel = 10;
		MC_JPC4DISCTRLUPD[i].jmp_dir = 0;
		MC_JPC4DISCTRLUPD[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4CLKDIS[9];

	for (uint32_t i = 1; i < 9; i++) {
		MC_JPC4CLKDIS[i].cmd_code = JPC_CMD;
		MC_JPC4CLKDIS[i].sig_value = 1;
		MC_JPC4CLKDIS[i].sig_sel = 9;
		MC_JPC4CLKDIS[i].jmp_dir = 0;
		MC_JPC4CLKDIS[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4APD[10];

	for (uint32_t i = 1; i < 10; i++) {
		MC_JPC4APD[i].cmd_code = JPC_CMD;
		MC_JPC4APD[i].sig_value = 0;
		MC_JPC4APD[i].sig_sel = 8;
		MC_JPC4APD[i].jmp_dir = 0;
		MC_JPC4APD[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4MPSMSRENODIMM;

	MC_JPC4MPSMSRENODIMM.cmd_code = JPC_CMD;
	MC_JPC4MPSMSRENODIMM.sig_value = 1;
	MC_JPC4MPSMSRENODIMM.sig_sel = 4;
	MC_JPC4MPSMSRENODIMM.jmp_dir = 0;
	MC_JPC4MPSMSRENODIMM.jmp_step = 7;

	JPC_UCODE_t MC_JPC4MPSMSRXNODIMM[64];

	for (uint32_t i = 1; i < 64; i++) {
		MC_JPC4MPSMSRXNODIMM[i].cmd_code = JPC_CMD;
		MC_JPC4MPSMSRXNODIMM[i].sig_value = 1;
		MC_JPC4MPSMSRXNODIMM[i].sig_sel = 4;
		MC_JPC4MPSMSRXNODIMM[i].jmp_dir = 0;
		MC_JPC4MPSMSRXNODIMM[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4MPSMSRERDIMM;

	MC_JPC4MPSMSRERDIMM.cmd_code = JPC_CMD;
	MC_JPC4MPSMSRERDIMM.sig_value = 1;
	MC_JPC4MPSMSRERDIMM.sig_sel = 4;
	MC_JPC4MPSMSRERDIMM.jmp_dir = 0;
	MC_JPC4MPSMSRERDIMM.jmp_step = 7;

	JPC_UCODE_t MC_JPC4MPSMSRXRDIMM[32];

	for (uint32_t i = 1; i < 32; i++) {
		MC_JPC4MPSMSRXRDIMM[i].cmd_code = JPC_CMD;
		MC_JPC4MPSMSRXRDIMM[i].sig_value = 1;
		MC_JPC4MPSMSRXRDIMM[i].sig_sel = 4;
		MC_JPC4MPSMSRXRDIMM[i].jmp_dir = 0;
		MC_JPC4MPSMSRXRDIMM[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4AR[4][9];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 1; j < 9; j++) {
			MC_JPC4AR[i][j].cmd_code = JPC_CMD;
			MC_JPC4AR[i][j].sig_value = 1;
			MC_JPC4AR[i][j].sig_sel = i + 4;
			MC_JPC4AR[i][j].jmp_dir = 0;
			MC_JPC4AR[i][j].jmp_step = j;
		}
	}

	JPC_UCODE_t MC_JPC4DISMRR4TCR[10];

	for (uint32_t i = 1; i < 10; i++) {
		MC_JPC4DISMRR4TCR[i].cmd_code = JPC_CMD;
		MC_JPC4DISMRR4TCR[i].sig_value = 0;
		MC_JPC4DISMRR4TCR[i].sig_sel = 15;
		MC_JPC4DISMRR4TCR[i].jmp_dir = 0;
		MC_JPC4DISMRR4TCR[i].jmp_step = i;
	}


	SNPS_TRACE("Entering");

    // [Channel 0 & 1 Powerdown]
    for (uint32_t ch = 0; ch < active_channels; ch++) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(0  , MC_DISDQ[0].value      , ch); // powerdown entry [rank 0]
        dwc_ddrctl_cinit_write_lp_cmdbuf(1  , MC_BLOCKREF[0].value   , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(2  , MC_JPC4APD[1].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(3  , MC_PRANKPREAB[0].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(4  , MC_PDE[0].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(5  , MC_RESUMEREF[0].value  , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(6  , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(7  , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(8  , MC_IWAITDFILPIDLE.value, ch); // powerdown exit  [rank 0]
        dwc_ddrctl_cinit_write_lp_cmdbuf(9  , MC_LOCKCTRL.value      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(10 , MC_PDX[0].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(11 , MC_DES.value           , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(12 , MC_UNLOCKCTRL.value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(13 , MC_ENDQ[0].value       , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(14 , MC_PDXDONE[0].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(15 , MC_IWAITTIME[31].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(16 , MC_DISDQ[1].value      , ch); // powerdown entry [rank 1]
        dwc_ddrctl_cinit_write_lp_cmdbuf(17 , MC_BLOCKREF[1].value   , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(18 , MC_JPC4APD[1].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(19 , MC_PRANKPREAB[1].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(20 , MC_PDE[1].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(21 , MC_RESUMEREF[1].value  , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(22 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(23 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(24 , MC_IWAITDFILPIDLE.value, ch); // powerdown exit  [rank 1]
        dwc_ddrctl_cinit_write_lp_cmdbuf(25 , MC_LOCKCTRL.value      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(26 , MC_PDX[1].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(27 , MC_DES.value           , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(28 , MC_UNLOCKCTRL.value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(29 , MC_ENDQ[1].value       , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(30 , MC_PDXDONE[1].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(31 , MC_IWAITTIME[31].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(32 , MC_DISDQ[2].value      , ch); // powerdown entry [rank 2]
        dwc_ddrctl_cinit_write_lp_cmdbuf(33 , MC_BLOCKREF[2].value   , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(34 , MC_JPC4APD[1].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(35 , MC_PRANKPREAB[2].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(36 , MC_PDE[2].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(37 , MC_RESUMEREF[2].value  , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(38 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(39 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(40 , MC_IWAITDFILPIDLE.value, ch); // powerdown exit  [rank 2]
        dwc_ddrctl_cinit_write_lp_cmdbuf(41 , MC_LOCKCTRL.value      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(42 , MC_PDX[2].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(43 , MC_DES.value           , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(44 , MC_UNLOCKCTRL.value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(45 , MC_ENDQ[2].value       , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(46 , MC_PDXDONE[2].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(47 , MC_IWAITTIME[31].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(48 , MC_DISDQ[3].value      , ch); // powerdown entry [rank 3]
        dwc_ddrctl_cinit_write_lp_cmdbuf(49 , MC_BLOCKREF[3].value   , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(50 , MC_JPC4APD[1].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(51 , MC_PRANKPREAB[3].value , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(52 , MC_PDE[3].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(53 , MC_RESUMEREF[3].value  , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(54 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(55 , 0                      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(56 , MC_IWAITDFILPIDLE.value, ch); // powerdown exit  [rank 3]
        dwc_ddrctl_cinit_write_lp_cmdbuf(57 , MC_LOCKCTRL.value      , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(58 , MC_PDX[3].value        , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(59 , MC_DES.value           , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(60 , MC_UNLOCKCTRL.value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(61 , MC_ENDQ[3].value       , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(62 , MC_PDXDONE[3].value    , ch);
        dwc_ddrctl_cinit_write_lp_cmdbuf(63 , MC_IWAITTIME[31].value , ch);
    }

    // [Channel 0 & 1 Self-refresh]
    if ((dimm_type != DWC_RDIMM) && (dimm_type != DWC_LRDIMM)) {
        for (uint32_t ch = 0; ch < active_channels; ch++) {
            dwc_ddrctl_cinit_write_lp_cmdbuf(64 , MC_MOVCSn2R0[4].value           , ch); // self-refresh entry1
            dwc_ddrctl_cinit_write_lp_cmdbuf(65 , MC_MOVCSn2R15.value             , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(66 , MC_DISDQ[4].value               , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(67 , MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(68 , MC_JPC4MPSMSRENODIMM.value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(69 , MC_JPC4AR[3][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(70 , MC_PRANKPREAB[3].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(71 , MC_JPC4AR[2][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(72 , MC_PRANKPREAB[2].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(73 , MC_JPC4AR[1][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(74 , MC_PRANKPREAB[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(75 , MC_PRANKPREAB[0].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(76 , MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(77 , MC_REFFLUSH[7].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(78 , MC_PAUSEREF[4].value            , ch); // self-refresh entry2
            dwc_ddrctl_cinit_write_lp_cmdbuf(79 , MC_SRE[7].value                 , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(80 , MC_JPC4CAPARRETRY[1].value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(81 , MC_IWAITCAPARRETRYWINDOW.value  , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(82 , MC_FORCECSE[7].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(83 , MC_JPC4CLKDIS[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(84 , MC_DFICLKDISCTRL.value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(85 , MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(86 , MC_IWAITDFILPIDLE.value         , ch); // self-refresh exit1
            dwc_ddrctl_cinit_write_lp_cmdbuf(87 , MC_JPC4CLKDIS[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(88 , MC_DFICLKENCTRL.value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(89 , MC_JPC4DISCTRLUPD[2].value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(90 , MC_JPC4CTRLUPDPRESRX[1][1].value, ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(91 , MC_CTRLUPD.value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(92 , MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(93 , MC_SRX[7].value                 , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(94 , MC_SRXDONETXS[6].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(95 , MC_JPC4DISCTRLUPD[2].value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(96 , MC_JPC4CTRLUPDPRESRX[0][1].value, ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(97 , MC_CTRLUPD.value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(98 , MC_MOVCSn2R0[5].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(99 , MC_MOVCSn2R15.value             , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(100, MC_STORETXSDLLSTART.value       , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(101, MC_JPC4MPSMSRXNODIMM[58].value  , ch);
#ifdef UMCTL2_CID_EN
            dwc_ddrctl_cinit_write_lp_cmdbuf(102, MC_JPC4AR[3][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(103, MC_PRANKREFAB[3].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(104, MC_JPC4AR[2][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(105, MC_PRANKREFAB[2].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(106, MC_JPC4AR[1][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(107, MC_PRANKREFAB[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(108, MC_PRANKREFAB[0].value          , ch);
#else  /* UMCTL2_CID_EN */
            dwc_ddrctl_cinit_write_lp_cmdbuf(102, MC_PRANKREFAB[4].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(103, MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(104, MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(105, MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(106, MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(107, MC_IWAITTIME[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(108, MC_IWAITTIME[0].value           , ch);
#endif /* UMCTL2_CID_EN */
            dwc_ddrctl_cinit_write_lp_cmdbuf(109, MC_JPC4DISDQSOSC[2].value       , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(110, MC_DQSOSCSTART[4].value         , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(111, MC_STOREDQSOSCSTART.value       , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(112, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(113, MC_REFFLUSH[7].value            , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(114, MC_JPC4DISZQCALNODIMM[0].value  , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(115, MC_JPC4ZQRESISTORSHARED[0].value, ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(116, MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(117, MC_ZQCALSTART[4].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(118, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(119, MC_IWAITTZQCAL.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(120, MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(121, MC_ZQCALLATCH[4].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(122, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(123, MC_IWAITTZQLAT.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(124, MC_JPC4ZQRESISTORSHARED[1].value, ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(125, MC_JPC4AR[3][8].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(126, MC_BLOCKREF[3].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(127, MC_ZQCALSTART[3].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(128, MC_RESUMEREF[3].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(129, MC_IWAITTZQCAL.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(130, MC_BLOCKREF[3].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(131, MC_ZQCALLATCH[3].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(132, MC_RESUMEREF[3].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(133, MC_IWAITTZQLAT.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(134, MC_JPC4AR[2][8].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(135, MC_BLOCKREF[2].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(136, MC_ZQCALSTART[2].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(137, MC_RESUMEREF[2].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(138, MC_IWAITTZQCAL.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(139, MC_BLOCKREF[2].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(140, MC_ZQCALLATCH[2].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(141, MC_RESUMEREF[2].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(142, MC_IWAITTZQLAT.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(143, MC_JPC4AR[1][8].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(144, MC_BLOCKREF[1].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(145, MC_ZQCALSTART[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(146, MC_RESUMEREF[1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(147, MC_IWAITTZQCAL.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(148, MC_BLOCKREF[1].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(149, MC_ZQCALLATCH[1].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(150, MC_RESUMEREF[1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(151, MC_IWAITTZQLAT.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(152, MC_BLOCKREF[0].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(153, MC_ZQCALSTART[0].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(154, MC_RESUMEREF[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(155, MC_IWAITTZQCAL.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(156, MC_BLOCKREF[0].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(157, MC_ZQCALLATCH[0].value          , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(158, MC_RESUMEREF[0].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(159, MC_IWAITTZQLAT.value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(160, MC_IWAITTXSDLLACK.value         , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(161, MC_CLEARTXSDLLSTART.value       , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(162, MC_SRXDONETXSDLL[6].value       , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(163, MC_JPC4MPSMSRXNODIMM[26].value  , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(164, MC_JPC4DISMRR4TCR[9].value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(165, MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(166, MC_JPC4AR[3][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(167, MC_MRR4[3].value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(168, MC_JPC4AR[2][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(169, MC_MRR4[2].value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(170, MC_JPC4AR[1][1].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(171, MC_MRR4[1].value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(172, MC_MRR4[0].value                , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(173, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(174, MC_JPC4DISDQSOSC[15].value      , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(175, MC_IWAITDQSOSCACK.value         , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(176, MC_CLEARDQSOSCSTART.value       , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(177, MC_BLOCKREF[4].value            , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(178, MC_JPC4AR[3][2].value           , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(179, MC_MRR[3][1][46].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(180, MC_MRR[3][1][47].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(181, MC_JPC4AR[2][2].value           , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(182, MC_MRR[2][1][46].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(183, MC_MRR[2][1][47].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(184, MC_JPC4AR[1][2].value           , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(185, MC_MRR[1][1][46].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(186, MC_MRR[1][1][47].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(187, MC_MRR[0][1][46].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(188, MC_MRR[0][1][47].value          , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(189, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(190, MC_JPC4DISCTRLUPD[1].value      , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(191, MC_CTRLUPD.value                , ch); 
            dwc_ddrctl_cinit_write_lp_cmdbuf(192, MC_RESUMEREF[4].value           , ch);
            dwc_ddrctl_cinit_write_lp_cmdbuf(193, MC_ENDQ[4].value                , ch); // self-refresh exit2
        }
    } else {
        // [Channel 0 Self-refresh]
        dwc_ddrctl_cinit_write_lp_cmdbuf(64 , MC_MOVCSn2R0[4].value             , 0); // self-refresh entry1
        dwc_ddrctl_cinit_write_lp_cmdbuf(65 , MC_MOVCSn2R15.value               , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(66 , MC_DISDQ[4].value                 , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(67 , MC_BLOCKREF[4].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(68 , MC_JPC4MPSMSRERDIMM.value         , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(69 , MC_JPC4AR[3][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(70 , MC_PRANKPREAB[3].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(71 , MC_JPC4AR[2][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(72 , MC_PRANKPREAB[2].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(73 , MC_JPC4AR[1][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(74 , MC_PRANKPREAB[1].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(75 , MC_PRANKPREAB[0].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(76 , MC_RESUMEREF[4].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(77 , MC_REFFLUSH[7].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(78 , MC_PAUSEREF[4].value              , 0); // self-refresh entry2
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(79 , MC_SRE[4].value                   , 0);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(79 , MC_SRE[6].value                   , 0);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(80 , MC_JPC4CAPARRETRY[1].value        , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(81 , MC_IWAITCAPARRETRYWINDOW.value    , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(82 , MC_IWAITCHANNELMESSAGE[0][1].value, 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(83 , MC_SETDUALCHOPMODE.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(84 , MC_IWAITDELAYPIPES.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(85 , MC_JPC4DIMMSRFCLKSTOP[1][2].value , 0);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(86 , MC_FORCECSE[4].value              , 0);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(86 , MC_FORCECSE[6].value              , 0);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(87 , MC_JPC4DIMMSRFCLKSTOP[0][1].value , 0);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(88 , MC_NOP[4][0].value                , 0);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(88 , MC_NOP[6][0].value                , 0);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(89 , MC_STORECHANNELMESSAGE[1].value   , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(90 , MC_IWAITCHANNELMESSAGE[0][0].value, 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(91 , MC_CLEARDUALCHOPMODE.value        , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(92 , MC_IWAITDELAYPIPES.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(93 , MC_CLEARCHANNELMESSAGE[1].value   , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(94 , MC_JPC4CLKDIS[2].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(95 , MC_IWAITTCKOFF.value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(96 , MC_DFICLKDISCTRL.value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(97 , MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(98 , MC_SETSEQONGOING.value            , 0); // self-refresh exit1
        dwc_ddrctl_cinit_write_lp_cmdbuf(99 , MC_IWAITDFILPIDLE.value           , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(100, MC_JPC4DIMMSRFCLKSTOP[1][4].value , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(101, MC_JPC4CLKDIS[1].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(102, MC_DFICLKENCTRL.value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(103, MC_FORCECSX[6].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(104, MC_IWAITTSTAB.value               , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(105, MC_JPC4DISCTRLUPD[2].value        , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(106, MC_JPC4CTRLUPDPRESRX[1][1].value  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(107, MC_CTRLUPD.value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(108, MC_BLOCKREF[4].value              , 0);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(109, MC_SRX[4].value                   , 0);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(109, MC_SRX[6].value                   , 0);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(110, MC_SRXDONETXS[6].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(111, MC_JPC4DISCTRLUPD[2].value        , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(112, MC_JPC4CTRLUPDPRESRX[0][1].value  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(113, MC_CTRLUPD.value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(114, MC_MOVCSn2R0[5].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(115, MC_MOVCSn2R15.value               , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(116, MC_STORETXSDLLSTART.value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(117, MC_JPC4MPSMSRXRDIMM[21].value     , 0); 
#ifdef UMCTL2_CID_EN
        dwc_ddrctl_cinit_write_lp_cmdbuf(118, MC_JPC4AR[3][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(119, MC_PRANKREFAB[3].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(120, MC_JPC4AR[2][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(121, MC_PRANKREFAB[2].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(122, MC_JPC4AR[1][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(123, MC_PRANKREFAB[1].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(124, MC_PRANKREFAB[0].value            , 0);
#else  /* UMCTL2_CID_EN */
        dwc_ddrctl_cinit_write_lp_cmdbuf(118, MC_PRANKREFAB[4].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(119, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(120, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(121, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(122, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(123, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(124, MC_IWAITTIME[0].value             , 0);
#endif /* UMCTL2_CID_EN */
        dwc_ddrctl_cinit_write_lp_cmdbuf(125, MC_JPC4DISDQSOSC[2].value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(126, MC_DQSOSCSTART[4].value           , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(127, MC_STOREDQSOSCSTART.value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(128, MC_RESUMEREF[4].value             , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(129, MC_REFFLUSH[7].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(130, MC_JPC4DISZQCALRDIMM[0].value     , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(131, MC_BLOCKREF[4].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(132, MC_ZQCALSTART[4].value            , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(133, MC_RESUMEREF[4].value             , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(134, MC_IWAITTZQCAL.value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(135, MC_BLOCKREF[4].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(136, MC_ZQCALLATCH[4].value            , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(137, MC_RESUMEREF[4].value             , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(138, MC_IWAITTZQLAT.value              , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(139, MC_IWAITTXSDLLACK.value           , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(140, MC_CLEARTXSDLLSTART.value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(141, MC_SRXDONETXSDLL[6].value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(142, MC_JPC4MPSMSRXRDIMM[28].value     , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(143, MC_JPC4DISMRR4TCR[9].value        , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(144, MC_BLOCKREF[4].value              , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(145, MC_JPC4AR[3][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(146, MC_MRR4[3].value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(147, MC_JPC4AR[2][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(148, MC_MRR4[2].value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(149, MC_JPC4AR[1][1].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(150, MC_MRR4[1].value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(151, MC_MRR4[0].value                  , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(152, MC_RESUMEREF[4].value             , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(153, MC_JPC4DISDQSOSC[19].value        , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(154, MC_IWAITDQSOSCACK.value           , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(155, MC_CLEARDQSOSCSTART.value         , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(156, MC_BLOCKREF[4].value              , 0);
        if (dimm_type == DWC_RDIMM) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(157, MC_JPC4AR[3][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(158, MC_MRR[3][1][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(159, MC_MRR[3][1][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(160, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(161, MC_JPC4AR[2][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(162, MC_MRR[2][1][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(163, MC_MRR[2][1][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(164, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(165, MC_JPC4AR[1][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(166, MC_MRR[1][1][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(167, MC_MRR[1][1][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(168, MC_IWAITTIME[0].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(169, MC_MRR[0][1][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(170, MC_MRR[0][1][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(171, MC_IWAITTIME[0].value             , 0);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(157, MC_JPC4AR[3][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(158, MC_MRR[3][0][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(159, MC_MRR[3][0][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(160, MC_IWAITTRKCALCCUR.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(161, MC_JPC4AR[2][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(162, MC_MRR[2][0][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(163, MC_MRR[2][0][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(164, MC_IWAITTRKCALCCUR.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(165, MC_JPC4AR[1][3].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(166, MC_MRR[1][0][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(167, MC_MRR[1][0][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(168, MC_IWAITTRKCALCCUR.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(169, MC_MRR[0][0][46].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(170, MC_MRR[0][0][47].value            , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(171, MC_IWAITTRKCALCCUR.value          , 0);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(172, MC_RESUMEREF[4].value             , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(173, MC_JPC4DISCTRLUPD[1].value        , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(174, MC_CTRLUPD.value                  , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(175, MC_RESETSEQONGOING.value          , 0);
        dwc_ddrctl_cinit_write_lp_cmdbuf(176, MC_RESUMEREF[4].value             , 0); 
        dwc_ddrctl_cinit_write_lp_cmdbuf(177, MC_ENDQ[4].value                  , 0); // self-refresh exit2
#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
        // [Channel 1 Self-refresh]
        dwc_ddrctl_cinit_write_lp_cmdbuf(64 , MC_MOVCSn2R0[4].value             , 1); // self-refresh entry1
        dwc_ddrctl_cinit_write_lp_cmdbuf(65 , MC_MOVCSn2R15.value               , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(66 , MC_DISDQ[4].value                 , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(67 , MC_BLOCKREF[4].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(68 , MC_JPC4MPSMSRERDIMM.value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(69 , MC_JPC4AR[3][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(70 , MC_PRANKPREAB[3].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(71 , MC_JPC4AR[2][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(72 , MC_PRANKPREAB[2].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(73 , MC_JPC4AR[1][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(74 , MC_PRANKPREAB[1].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(75 , MC_PRANKPREAB[0].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(76 , MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(77 , MC_REFFLUSH[7].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(78, MC_PAUSEREF[4].value               , 1); // self-refresh entry2
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(79 , MC_SRE[4].value                   , 1);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(79 , MC_SRE[6].value                   , 1);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(80 , MC_JPC4CAPARRETRY[1].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(81 , MC_IWAITCAPARRETRYWINDOW.value    , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(82 , MC_STORECHANNELMESSAGE[0].value   , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(83 , MC_IWAITCHANNELMESSAGE[1][1].value, 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(84, MC_JPC4DIMMSRFCLKSTOP[1][1].value  , 1);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(85 , MC_FORCECSE[4].value              , 1);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(85 , MC_FORCECSE[6].value              , 1);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(86 , MC_CLEARCHANNELMESSAGE[0].value   , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(87 , MC_IWAITCHANNELMESSAGE[1][0].value, 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(88 , MC_JPC4CLKDIS[2].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(89 , MC_IWAITTCKOFF.value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(90 , MC_DFICLKDISCTRL.value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(91 , MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(92 , MC_SETSEQONGOING.value            , 1); // self-refresh exit1
        dwc_ddrctl_cinit_write_lp_cmdbuf(93 , MC_IWAITDFILPIDLE.value           , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(94 , MC_JPC4DIMMSRFCLKSTOP[1][2].value , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(95 , MC_JPC4CLKDIS[1].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(96 , MC_DFICLKENCTRL.value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(97 , MC_IWAITTSRFEXITSTAGGER.value     , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(98 , MC_JPC4DIMMSRFCLKSTOP[1][2].value , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(99 , MC_FORCECSX[6].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(100, MC_IWAITTSTAB.value               , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(101, MC_JPC4DISCTRLUPD[2].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(102, MC_JPC4CTRLUPDPRESRX[1][1].value  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(103, MC_CTRLUPD.value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(104, MC_BLOCKREF[4].value              , 1);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(105, MC_SRX[4].value                   , 1);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(105, MC_SRX[6].value                   , 1);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(106, MC_SRXDONETXS[6].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(107, MC_JPC4DISCTRLUPD[2].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(108, MC_JPC4CTRLUPDPRESRX[0][1].value  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(109, MC_CTRLUPD.value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(110, MC_MOVCSn2R0[5].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(111, MC_MOVCSn2R15.value               , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(112, MC_STORETXSDLLSTART.value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(113, MC_JPC4MPSMSRXRDIMM[21].value     , 1);
#ifdef UMCTL2_CID_EN
        dwc_ddrctl_cinit_write_lp_cmdbuf(114, MC_JPC4AR[3][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(115, MC_PRANKREFAB[3].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(116, MC_JPC4AR[2][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(117, MC_PRANKREFAB[2].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(118, MC_JPC4AR[1][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(119, MC_PRANKREFAB[1].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(120, MC_PRANKREFAB[0].value            , 1);
#else  /* UMCTL2_CID_EN */
        dwc_ddrctl_cinit_write_lp_cmdbuf(114, MC_PRANKREFAB[4].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(115, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(116, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(117, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(118, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(119, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(120, MC_IWAITTIME[0].value             , 1);
#endif /* UMCTL2_CID_EN */
        dwc_ddrctl_cinit_write_lp_cmdbuf(121, MC_JPC4DISDQSOSC[2].value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(122, MC_DQSOSCSTART[4].value           , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(123, MC_STOREDQSOSCSTART.value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(124, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(125, MC_REFFLUSH[7].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(126, MC_JPC4DISZQCALRDIMM[0].value     , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(127, MC_BLOCKREF[4].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(128, MC_ZQCALSTART[4].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(129, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(130, MC_IWAITTZQCAL.value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(131, MC_BLOCKREF[4].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(132, MC_ZQCALLATCH[4].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(133, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(134, MC_IWAITTZQLAT.value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(135, MC_IWAITTXSDLLACK.value           , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(136, MC_CLEARTXSDLLSTART.value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(137, MC_SRXDONETXSDLL[6].value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(138, MC_JPC4MPSMSRXRDIMM[28].value     , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(139, MC_JPC4DISMRR4TCR[9].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(140, MC_BLOCKREF[4].value              , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(141, MC_JPC4AR[3][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(142, MC_MRR4[3].value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(143, MC_JPC4AR[2][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(144, MC_MRR4[2].value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(145, MC_JPC4AR[1][1].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(146, MC_MRR4[1].value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(147, MC_MRR4[0].value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(148, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(149, MC_JPC4DISDQSOSC[19].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(150, MC_IWAITDQSOSCACK.value           , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(151, MC_CLEARDQSOSCSTART.value         , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(152, MC_BLOCKREF[4].value              , 1);
        if (dimm_type == DWC_RDIMM) {
        dwc_ddrctl_cinit_write_lp_cmdbuf(153, MC_JPC4AR[3][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(154, MC_MRR[3][1][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(155, MC_MRR[3][1][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(156, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(157, MC_JPC4AR[2][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(158, MC_MRR[2][1][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(159, MC_MRR[2][1][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(160, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(161, MC_JPC4AR[1][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(162, MC_MRR[1][1][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(163, MC_MRR[1][1][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(164, MC_IWAITTIME[0].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(165, MC_MRR[0][1][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(166, MC_MRR[0][1][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(167, MC_IWAITTIME[0].value             , 1);
        } else {
        dwc_ddrctl_cinit_write_lp_cmdbuf(153, MC_JPC4AR[3][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(154, MC_MRR[3][0][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(155, MC_MRR[3][0][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(156, MC_IWAITTRKCALCCUR.value          , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(157, MC_JPC4AR[2][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(158, MC_MRR[2][0][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(159, MC_MRR[2][0][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(160, MC_IWAITTRKCALCCUR.value          , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(161, MC_JPC4AR[1][3].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(162, MC_MRR[1][0][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(163, MC_MRR[1][0][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(164, MC_IWAITTRKCALCCUR.value          , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(165, MC_MRR[0][0][46].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(166, MC_MRR[0][0][47].value            , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(167, MC_IWAITTRKCALCCUR.value          , 1);
        }
        dwc_ddrctl_cinit_write_lp_cmdbuf(168, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(169, MC_JPC4DISCTRLUPD[1].value        , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(170, MC_CTRLUPD.value                  , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(171, MC_RESETSEQONGOING.value          , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(172, MC_RESUMEREF[4].value             , 1);
        dwc_ddrctl_cinit_write_lp_cmdbuf(173, MC_ENDQ[4].value                  , 1); // self-refresh exit2
#endif /* DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH */
	}
#endif // DDRCTL_DDR
	SNPS_TRACE("Leaving");
}

/** @brief method to program DDR5 utility microcode
 */
void dwc_ddrctl_cinit_prgm_ucode_load_du(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_DDR
    uint32_t dimm_type;
    uint32_t active_logical_ranks = 0;
    uint32_t active_channels=DWC_DDRCTL_NUM_CHANNEL;

    dimm_type = cinit_cfg->spdData_m.module_type;

    active_logical_ranks = CINIT_GET_LRANKS(cinit_cfg, 0);

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    if(REGB_DDRC_CH0.chctl.dual_channel_en==0) {
        active_channels=1;
    }
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH

	SNPS_LOG("ucode: Channels %d DIMM %d, Logic Ranks %d", active_channels, dimm_type, active_logical_ranks);

	// [Global block 0]
	MOV_UCODE_t MC_MOVCSn2R0_GLB_BLK_0;

	MC_MOVCSn2R0_GLB_BLK_0.cmd_code = MOV_CMD;
	MC_MOVCSn2R0_GLB_BLK_0.mov_dir = 0;
	MC_MOVCSn2R0_GLB_BLK_0.mov_type = 1;
	MC_MOVCSn2R0_GLB_BLK_0._RESERVED = 0;
	MC_MOVCSn2R0_GLB_BLK_0.reg_num = 5;

	MOV_UCODE_t MC_MOVCSn2R15_GLB_BLK_1;

	MC_MOVCSn2R15_GLB_BLK_1.cmd_code = MOV_CMD;
	MC_MOVCSn2R15_GLB_BLK_1.mov_dir = 1;
	MC_MOVCSn2R15_GLB_BLK_1.mov_type = 0;
	MC_MOVCSn2R15_GLB_BLK_1._RESERVED = 0;
	MC_MOVCSn2R15_GLB_BLK_1.reg_num = 15;

	DISDQ_UCODE_t MC_DISDQ_GLB_BLK_2;

	MC_DISDQ_GLB_BLK_2.cmd_code = DISDQ_CMD;
	MC_DISDQ_GLB_BLK_2.last_cmd = 1;
	MC_DISDQ_GLB_BLK_2._RESERVED = 0;
	MC_DISDQ_GLB_BLK_2.disdqset = 1;
	MC_DISDQ_GLB_BLK_2.disdqreset = 0;
	MC_DISDQ_GLB_BLK_2.csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_GLB_BLK_3;

	MC_PAUSEREF_GLB_BLK_3.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_GLB_BLK_3.last_cmd = 1;
	MC_PAUSEREF_GLB_BLK_3._RESERVED = 0;
	MC_PAUSEREF_GLB_BLK_3.pausereftype = 1;
	MC_PAUSEREF_GLB_BLK_3.pauserefset = 1;
	MC_PAUSEREF_GLB_BLK_3.pauserefreset = 0;
	MC_PAUSEREF_GLB_BLK_3.csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_ZQCALSTART_GLB_BLK_4;

	MC_ZQCALSTART_GLB_BLK_4.cmd_code = MPC_CMD;
	MC_ZQCALSTART_GLB_BLK_4.last_cmd = 1;
	MC_ZQCALSTART_GLB_BLK_4.op = 5;
	MC_ZQCALSTART_GLB_BLK_4.csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_GLB_BLK_5;

	MC_PAUSEREF_GLB_BLK_5.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_GLB_BLK_5.last_cmd = 1;
	MC_PAUSEREF_GLB_BLK_5._RESERVED = 0;
	MC_PAUSEREF_GLB_BLK_5.pausereftype = 0;
	MC_PAUSEREF_GLB_BLK_5.pauserefset = 0;
	MC_PAUSEREF_GLB_BLK_5.pauserefreset = 1;
	MC_PAUSEREF_GLB_BLK_5.csn_sel = RANK_R15_SEL;

	DISDQ_UCODE_t MC_DISDQ_GLB_BLK_6;

	MC_DISDQ_GLB_BLK_6.cmd_code = DISDQ_CMD;
	MC_DISDQ_GLB_BLK_6.last_cmd = 1;
	MC_DISDQ_GLB_BLK_6._RESERVED = 0;
	MC_DISDQ_GLB_BLK_6.disdqset = 0;
	MC_DISDQ_GLB_BLK_6.disdqreset = 1;
	MC_DISDQ_GLB_BLK_6.csn_sel = RANK_R15_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_GLB_BLK_7;

	MC_IMMSET_GLB_BLK_7.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_GLB_BLK_7.imm_type = 0;
	MC_IMMSET_GLB_BLK_7._RESERVED = 0;
	MC_IMMSET_GLB_BLK_7.reg_sel = 2;
	MC_IMMSET_GLB_BLK_7.bit_loc = 4;
	MC_IMMSET_GLB_BLK_7.bit_val = 1;

	// [Global block 1]
	CTRLUPD_UCODE_t MC_CTRLUPD_GLB_BLK_8;

	MC_CTRLUPD_GLB_BLK_8.cmd_code = CTRLUPD_CMD;
	MC_CTRLUPD_GLB_BLK_8.last_cmd = 1;
	MC_CTRLUPD_GLB_BLK_8.dfi_ctrlupd_req_set = 1;
	MC_CTRLUPD_GLB_BLK_8.dfi_ctrlupd_retry_en = 0;
	MC_CTRLUPD_GLB_BLK_8.wait_unit = 0;
	MC_CTRLUPD_GLB_BLK_8.wait_time = 0;

	// [Global block 4]
	IMM_BIT_UCODE_t MC_IMMCLEAR_GLB_BLK_32;

	MC_IMMCLEAR_GLB_BLK_32.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_GLB_BLK_32.imm_type = 0;
	MC_IMMCLEAR_GLB_BLK_32._RESERVED = 0;
	MC_IMMCLEAR_GLB_BLK_32.reg_sel = 2;
	MC_IMMCLEAR_GLB_BLK_32.bit_loc = 4;
	MC_IMMCLEAR_GLB_BLK_32.bit_val = 0;

	MOV_UCODE_t MC_MOVCSn2R0_GLB_BLK_33;

	MC_MOVCSn2R0_GLB_BLK_33.cmd_code = MOV_CMD;
	MC_MOVCSn2R0_GLB_BLK_33.mov_dir = 0;
	MC_MOVCSn2R0_GLB_BLK_33.mov_type = 1;
	MC_MOVCSn2R0_GLB_BLK_33._RESERVED = 0;
	MC_MOVCSn2R0_GLB_BLK_33.reg_num = 5;

	MOV_UCODE_t MC_MOVCSn2R15_GLB_BLK_34;

	MC_MOVCSn2R15_GLB_BLK_34.cmd_code = MOV_CMD;
	MC_MOVCSn2R15_GLB_BLK_34.mov_dir = 1;
	MC_MOVCSn2R15_GLB_BLK_34.mov_type = 0;
	MC_MOVCSn2R15_GLB_BLK_34._RESERVED = 0;
	MC_MOVCSn2R15_GLB_BLK_34.reg_num = 15;

	DISDQ_UCODE_t MC_DISDQ_GLB_BLK_35;

	MC_DISDQ_GLB_BLK_35.cmd_code = DISDQ_CMD;
	MC_DISDQ_GLB_BLK_35.last_cmd = 1;
	MC_DISDQ_GLB_BLK_35._RESERVED = 0;
	MC_DISDQ_GLB_BLK_35.disdqset = 1;
	MC_DISDQ_GLB_BLK_35.disdqreset = 0;
	MC_DISDQ_GLB_BLK_35.csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_GLB_BLK_36;

	MC_PAUSEREF_GLB_BLK_36.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_GLB_BLK_36.last_cmd = 1;
	MC_PAUSEREF_GLB_BLK_36._RESERVED = 0;
	MC_PAUSEREF_GLB_BLK_36.pausereftype = 1;
	MC_PAUSEREF_GLB_BLK_36.pauserefset = 1;
	MC_PAUSEREF_GLB_BLK_36.pauserefreset = 0;
	MC_PAUSEREF_GLB_BLK_36.csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_ZQCALLATCH_GLB_BLK_37;

	MC_ZQCALLATCH_GLB_BLK_37.cmd_code = MPC_CMD;
	MC_ZQCALLATCH_GLB_BLK_37.last_cmd = 1;
	MC_ZQCALLATCH_GLB_BLK_37.op = 4;
	MC_ZQCALLATCH_GLB_BLK_37.csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_GLB_BLK_38;

	MC_PAUSEREF_GLB_BLK_38.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_GLB_BLK_38.last_cmd = 1;
	MC_PAUSEREF_GLB_BLK_38._RESERVED = 0;
	MC_PAUSEREF_GLB_BLK_38.pausereftype = 0;
	MC_PAUSEREF_GLB_BLK_38.pauserefset = 0;
	MC_PAUSEREF_GLB_BLK_38.pauserefreset = 1;
	MC_PAUSEREF_GLB_BLK_38.csn_sel = RANK_R15_SEL;

	DISDQ_UCODE_t MC_DISDQ_GLB_BLK_39;

	MC_DISDQ_GLB_BLK_39.cmd_code = DISDQ_CMD;
	MC_DISDQ_GLB_BLK_39.last_cmd = 1;
	MC_DISDQ_GLB_BLK_39._RESERVED = 0;
	MC_DISDQ_GLB_BLK_39.disdqset = 0;
	MC_DISDQ_GLB_BLK_39.disdqreset = 1;
	MC_DISDQ_GLB_BLK_39.csn_sel = RANK_R15_SEL;

	// [Rank block 0]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_0;

	MC_DISDQ_RANK_BLK_0.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_0.last_cmd = 1;
	MC_DISDQ_RANK_BLK_0._RESERVED = 0;
	MC_DISDQ_RANK_BLK_0.disdqset = 1;
	MC_DISDQ_RANK_BLK_0.disdqreset = 0;
	MC_DISDQ_RANK_BLK_0.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_1;

	MC_PAUSEREF_RANK_BLK_1.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_1.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_1._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_1.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_1.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_1.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_1.csn_sel = RANK0_SEL;

	MPC_UCODE_t MC_ZQCALSTART_RANK_BLK_2;

	MC_ZQCALSTART_RANK_BLK_2.cmd_code = MPC_CMD;
	MC_ZQCALSTART_RANK_BLK_2.last_cmd = 1;
	MC_ZQCALSTART_RANK_BLK_2.op = 5;
	MC_ZQCALSTART_RANK_BLK_2.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_3;

	MC_PAUSEREF_RANK_BLK_3.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_3.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_3._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_3.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_3.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_3.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_3.csn_sel = RANK0_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_4;

	MC_DISDQ_RANK_BLK_4.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_4.last_cmd = 1;
	MC_DISDQ_RANK_BLK_4._RESERVED = 0;
	MC_DISDQ_RANK_BLK_4.disdqset = 0;
	MC_DISDQ_RANK_BLK_4.disdqreset = 1;
	MC_DISDQ_RANK_BLK_4.csn_sel = RANK0_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_5;

	MC_IMMSET_RANK_BLK_5.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_5.imm_type = 0;
	MC_IMMSET_RANK_BLK_5._RESERVED = 0;
	MC_IMMSET_RANK_BLK_5.reg_sel = 0;
	MC_IMMSET_RANK_BLK_5.bit_loc = 0;
	MC_IMMSET_RANK_BLK_5.bit_val = 1;

	// [Rank block 8]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_64;

	MC_DISDQ_RANK_BLK_64.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_64.last_cmd = 1;
	MC_DISDQ_RANK_BLK_64._RESERVED = 0;
	MC_DISDQ_RANK_BLK_64.disdqset = 1;
	MC_DISDQ_RANK_BLK_64.disdqreset = 0;
	MC_DISDQ_RANK_BLK_64.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_65;

	MC_PAUSEREF_RANK_BLK_65.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_65.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_65._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_65.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_65.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_65.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_65.csn_sel = RANK1_SEL;

	MPC_UCODE_t MC_ZQCALSTART_RANK_BLK_66;

	MC_ZQCALSTART_RANK_BLK_66.cmd_code = MPC_CMD;
	MC_ZQCALSTART_RANK_BLK_66.last_cmd = 1;
	MC_ZQCALSTART_RANK_BLK_66.op = 5;
	MC_ZQCALSTART_RANK_BLK_66.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_67;

	MC_PAUSEREF_RANK_BLK_67.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_67.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_67._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_67.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_67.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_67.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_67.csn_sel = RANK1_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_68;

	MC_DISDQ_RANK_BLK_68.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_68.last_cmd = 1;
	MC_DISDQ_RANK_BLK_68._RESERVED = 0;
	MC_DISDQ_RANK_BLK_68.disdqset = 0;
	MC_DISDQ_RANK_BLK_68.disdqreset = 1;
	MC_DISDQ_RANK_BLK_68.csn_sel = RANK1_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_69;

	MC_IMMSET_RANK_BLK_69.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_69.imm_type = 0;
	MC_IMMSET_RANK_BLK_69._RESERVED = 0;
	MC_IMMSET_RANK_BLK_69.reg_sel = 0;
	MC_IMMSET_RANK_BLK_69.bit_loc = 4;
	MC_IMMSET_RANK_BLK_69.bit_val = 1;

	// [Rank block 16]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_128;

	MC_DISDQ_RANK_BLK_128.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_128.last_cmd = 1;
	MC_DISDQ_RANK_BLK_128._RESERVED = 0;
	MC_DISDQ_RANK_BLK_128.disdqset = 1;
	MC_DISDQ_RANK_BLK_128.disdqreset = 0;
	MC_DISDQ_RANK_BLK_128.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_129;

	MC_PAUSEREF_RANK_BLK_129.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_129.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_129._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_129.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_129.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_129.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_129.csn_sel = RANK2_SEL;

	MPC_UCODE_t MC_ZQCALSTART_RANK_BLK_130;

	MC_ZQCALSTART_RANK_BLK_130.cmd_code = MPC_CMD;
	MC_ZQCALSTART_RANK_BLK_130.last_cmd = 1;
	MC_ZQCALSTART_RANK_BLK_130.op = 5;
	MC_ZQCALSTART_RANK_BLK_130.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_131;

	MC_PAUSEREF_RANK_BLK_131.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_131.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_131._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_131.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_131.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_131.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_131.csn_sel = RANK2_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_132;

	MC_DISDQ_RANK_BLK_132.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_132.last_cmd = 1;
	MC_DISDQ_RANK_BLK_132._RESERVED = 0;
	MC_DISDQ_RANK_BLK_132.disdqset = 0;
	MC_DISDQ_RANK_BLK_132.disdqreset = 1;
	MC_DISDQ_RANK_BLK_132.csn_sel = RANK2_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_133;

	MC_IMMSET_RANK_BLK_133.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_133.imm_type = 0;
	MC_IMMSET_RANK_BLK_133._RESERVED = 0;
	MC_IMMSET_RANK_BLK_133.reg_sel = 1;
	MC_IMMSET_RANK_BLK_133.bit_loc = 0;
	MC_IMMSET_RANK_BLK_133.bit_val = 1;

	// [Rank block 24]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_192;

	MC_DISDQ_RANK_BLK_192.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_192.last_cmd = 1;
	MC_DISDQ_RANK_BLK_192._RESERVED = 0;
	MC_DISDQ_RANK_BLK_192.disdqset = 1;
	MC_DISDQ_RANK_BLK_192.disdqreset = 0;
	MC_DISDQ_RANK_BLK_192.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_193;

	MC_PAUSEREF_RANK_BLK_193.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_193.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_193._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_193.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_193.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_193.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_193.csn_sel = RANK3_SEL;

	MPC_UCODE_t MC_ZQCALSTART_RANK_BLK_194;

	MC_ZQCALSTART_RANK_BLK_194.cmd_code = MPC_CMD;
	MC_ZQCALSTART_RANK_BLK_194.last_cmd = 1;
	MC_ZQCALSTART_RANK_BLK_194.op = 5;
	MC_ZQCALSTART_RANK_BLK_194.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_195;

	MC_PAUSEREF_RANK_BLK_195.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_195.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_195._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_195.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_195.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_195.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_195.csn_sel = RANK3_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_196;

	MC_DISDQ_RANK_BLK_196.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_196.last_cmd = 1;
	MC_DISDQ_RANK_BLK_196._RESERVED = 0;
	MC_DISDQ_RANK_BLK_196.disdqset = 0;
	MC_DISDQ_RANK_BLK_196.disdqreset = 1;
	MC_DISDQ_RANK_BLK_196.csn_sel = RANK3_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_197;

	MC_IMMSET_RANK_BLK_197.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_197.imm_type = 0;
	MC_IMMSET_RANK_BLK_197._RESERVED = 0;
	MC_IMMSET_RANK_BLK_197.reg_sel = 1;
	MC_IMMSET_RANK_BLK_197.bit_loc = 4;
	MC_IMMSET_RANK_BLK_197.bit_val = 1;

	// [Rank block 1]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_8;

	MC_DISDQ_RANK_BLK_8.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_8.last_cmd = 1;
	MC_DISDQ_RANK_BLK_8._RESERVED = 0;
	MC_DISDQ_RANK_BLK_8.disdqset = 1;
	MC_DISDQ_RANK_BLK_8.disdqreset = 0;
	MC_DISDQ_RANK_BLK_8.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_9;

	MC_PAUSEREF_RANK_BLK_9.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_9.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_9._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_9.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_9.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_9.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_9.csn_sel = RANK0_SEL;

	MPC_UCODE_t MC_DQSOSCSTART_RANK_BLK_10;

	MC_DQSOSCSTART_RANK_BLK_10.cmd_code = MPC_CMD;
	MC_DQSOSCSTART_RANK_BLK_10.last_cmd = 1;
	MC_DQSOSCSTART_RANK_BLK_10.op = 7;
	MC_DQSOSCSTART_RANK_BLK_10.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_11;

	MC_PAUSEREF_RANK_BLK_11.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_11.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_11._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_11.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_11.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_11.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_11.csn_sel = RANK0_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_12;

	MC_DISDQ_RANK_BLK_12.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_12.last_cmd = 1;
	MC_DISDQ_RANK_BLK_12._RESERVED = 0;
	MC_DISDQ_RANK_BLK_12.disdqset = 0;
	MC_DISDQ_RANK_BLK_12.disdqreset = 1;
	MC_DISDQ_RANK_BLK_12.csn_sel = RANK0_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_13;

	MC_IMMSET_RANK_BLK_13.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_13.imm_type = 0;
	MC_IMMSET_RANK_BLK_13._RESERVED = 0;
	MC_IMMSET_RANK_BLK_13.reg_sel = 0;
	MC_IMMSET_RANK_BLK_13.bit_loc = 1;
	MC_IMMSET_RANK_BLK_13.bit_val = 1;

	// [Rank block 9]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_72;

	MC_DISDQ_RANK_BLK_72.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_72.last_cmd = 1;
	MC_DISDQ_RANK_BLK_72._RESERVED = 0;
	MC_DISDQ_RANK_BLK_72.disdqset = 1;
	MC_DISDQ_RANK_BLK_72.disdqreset = 0;
	MC_DISDQ_RANK_BLK_72.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_73;

	MC_PAUSEREF_RANK_BLK_73.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_73.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_73._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_73.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_73.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_73.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_73.csn_sel = RANK1_SEL;

	MPC_UCODE_t MC_DQSOSCSTART_RANK_BLK_74;

	MC_DQSOSCSTART_RANK_BLK_74.cmd_code = MPC_CMD;
	MC_DQSOSCSTART_RANK_BLK_74.last_cmd = 1;
	MC_DQSOSCSTART_RANK_BLK_74.op = 7;
	MC_DQSOSCSTART_RANK_BLK_74.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_75;

	MC_PAUSEREF_RANK_BLK_75.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_75.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_75._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_75.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_75.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_75.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_75.csn_sel = RANK1_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_76;

	MC_DISDQ_RANK_BLK_76.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_76.last_cmd = 1;
	MC_DISDQ_RANK_BLK_76._RESERVED = 0;
	MC_DISDQ_RANK_BLK_76.disdqset = 0;
	MC_DISDQ_RANK_BLK_76.disdqreset = 1;
	MC_DISDQ_RANK_BLK_76.csn_sel = RANK1_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_77;

	MC_IMMSET_RANK_BLK_77.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_77.imm_type = 0;
	MC_IMMSET_RANK_BLK_77._RESERVED = 0;
	MC_IMMSET_RANK_BLK_77.reg_sel = 0;
	MC_IMMSET_RANK_BLK_77.bit_loc = 5;
	MC_IMMSET_RANK_BLK_77.bit_val = 1;

	// [Rank block 17]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_136;

	MC_DISDQ_RANK_BLK_136.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_136.last_cmd = 1;
	MC_DISDQ_RANK_BLK_136._RESERVED = 0;
	MC_DISDQ_RANK_BLK_136.disdqset = 1;
	MC_DISDQ_RANK_BLK_136.disdqreset = 0;
	MC_DISDQ_RANK_BLK_136.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_137;

	MC_PAUSEREF_RANK_BLK_137.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_137.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_137._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_137.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_137.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_137.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_137.csn_sel = RANK2_SEL;

	MPC_UCODE_t MC_DQSOSCSTART_RANK_BLK_138;

	MC_DQSOSCSTART_RANK_BLK_138.cmd_code = MPC_CMD;
	MC_DQSOSCSTART_RANK_BLK_138.last_cmd = 1;
	MC_DQSOSCSTART_RANK_BLK_138.op = 7;
	MC_DQSOSCSTART_RANK_BLK_138.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_139;

	MC_PAUSEREF_RANK_BLK_139.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_139.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_139._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_139.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_139.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_139.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_139.csn_sel = RANK2_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_140;

	MC_DISDQ_RANK_BLK_140.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_140.last_cmd = 1;
	MC_DISDQ_RANK_BLK_140._RESERVED = 0;
	MC_DISDQ_RANK_BLK_140.disdqset = 0;
	MC_DISDQ_RANK_BLK_140.disdqreset = 1;
	MC_DISDQ_RANK_BLK_140.csn_sel = RANK2_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_141;

	MC_IMMSET_RANK_BLK_141.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_141.imm_type = 0;
	MC_IMMSET_RANK_BLK_141._RESERVED = 0;
	MC_IMMSET_RANK_BLK_141.reg_sel = 1;
	MC_IMMSET_RANK_BLK_141.bit_loc = 1;
	MC_IMMSET_RANK_BLK_141.bit_val = 1;

	// [Rank block 25]
	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_200;

	MC_DISDQ_RANK_BLK_200.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_200.last_cmd = 1;
	MC_DISDQ_RANK_BLK_200._RESERVED = 0;
	MC_DISDQ_RANK_BLK_200.disdqset = 1;
	MC_DISDQ_RANK_BLK_200.disdqreset = 0;
	MC_DISDQ_RANK_BLK_200.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_201;

	MC_PAUSEREF_RANK_BLK_201.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_201.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_201._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_201.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_201.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_201.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_201.csn_sel = RANK3_SEL;

	MPC_UCODE_t MC_DQSOSCSTART_RANK_BLK_202;

	MC_DQSOSCSTART_RANK_BLK_202.cmd_code = MPC_CMD;
	MC_DQSOSCSTART_RANK_BLK_202.last_cmd = 1;
	MC_DQSOSCSTART_RANK_BLK_202.op = 7;
	MC_DQSOSCSTART_RANK_BLK_202.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_203;

	MC_PAUSEREF_RANK_BLK_203.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_203.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_203._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_203.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_203.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_203.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_203.csn_sel = RANK3_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_204;

	MC_DISDQ_RANK_BLK_204.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_204.last_cmd = 1;
	MC_DISDQ_RANK_BLK_204._RESERVED = 0;
	MC_DISDQ_RANK_BLK_204.disdqset = 0;
	MC_DISDQ_RANK_BLK_204.disdqreset = 1;
	MC_DISDQ_RANK_BLK_204.csn_sel = RANK3_SEL;

	IMM_BIT_UCODE_t MC_IMMSET_RANK_BLK_205;

	MC_IMMSET_RANK_BLK_205.cmd_code = IMM_BIT_CMD;
	MC_IMMSET_RANK_BLK_205.imm_type = 0;
	MC_IMMSET_RANK_BLK_205._RESERVED = 0;
	MC_IMMSET_RANK_BLK_205.reg_sel = 1;
	MC_IMMSET_RANK_BLK_205.bit_loc = 5;
	MC_IMMSET_RANK_BLK_205.bit_val = 1;

	// [Rank block 4]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_32;

	MC_IMMCLEAR_RANK_BLK_32.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_32.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_32._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_32.reg_sel = 0;
	MC_IMMCLEAR_RANK_BLK_32.bit_loc = 0;
	MC_IMMCLEAR_RANK_BLK_32.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_33;

	MC_DISDQ_RANK_BLK_33.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_33.last_cmd = 1;
	MC_DISDQ_RANK_BLK_33._RESERVED = 0;
	MC_DISDQ_RANK_BLK_33.disdqset = 1;
	MC_DISDQ_RANK_BLK_33.disdqreset = 0;
	MC_DISDQ_RANK_BLK_33.csn_sel = RANK_ALL_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_34;

	MC_PAUSEREF_RANK_BLK_34.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_34.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_34._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_34.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_34.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_34.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_34.csn_sel = RANK0_SEL;

	MPC_UCODE_t MC_ZQCALLATCH_RANK_BLK_35;

	MC_ZQCALLATCH_RANK_BLK_35.cmd_code = MPC_CMD;
	MC_ZQCALLATCH_RANK_BLK_35.last_cmd = 1;
	MC_ZQCALLATCH_RANK_BLK_35.op = 4;
	MC_ZQCALLATCH_RANK_BLK_35.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_36;

	MC_PAUSEREF_RANK_BLK_36.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_36.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_36._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_36.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_36.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_36.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_36.csn_sel = RANK0_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_37;

	MC_DISDQ_RANK_BLK_37.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_37.last_cmd = 1;
	MC_DISDQ_RANK_BLK_37._RESERVED = 0;
	MC_DISDQ_RANK_BLK_37.disdqset = 0;
	MC_DISDQ_RANK_BLK_37.disdqreset = 1;
	MC_DISDQ_RANK_BLK_37.csn_sel = RANK_ALL_SEL;

	// [Rank block 12]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_96;

	MC_IMMCLEAR_RANK_BLK_96.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_96.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_96._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_96.reg_sel = 0;
	MC_IMMCLEAR_RANK_BLK_96.bit_loc = 4;
	MC_IMMCLEAR_RANK_BLK_96.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_97;

	MC_DISDQ_RANK_BLK_97.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_97.last_cmd = 1;
	MC_DISDQ_RANK_BLK_97._RESERVED = 0;
	MC_DISDQ_RANK_BLK_97.disdqset = 1;
	MC_DISDQ_RANK_BLK_97.disdqreset = 0;
	MC_DISDQ_RANK_BLK_97.csn_sel = RANK_ALL_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_98;

	MC_PAUSEREF_RANK_BLK_98.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_98.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_98._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_98.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_98.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_98.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_98.csn_sel = RANK1_SEL;

	MPC_UCODE_t MC_ZQCALLATCH_RANK_BLK_99;

	MC_ZQCALLATCH_RANK_BLK_99.cmd_code = MPC_CMD;
	MC_ZQCALLATCH_RANK_BLK_99.last_cmd = 1;
	MC_ZQCALLATCH_RANK_BLK_99.op = 4;
	MC_ZQCALLATCH_RANK_BLK_99.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_100;

	MC_PAUSEREF_RANK_BLK_100.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_100.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_100._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_100.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_100.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_100.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_100.csn_sel = RANK1_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_101;

	MC_DISDQ_RANK_BLK_101.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_101.last_cmd = 1;
	MC_DISDQ_RANK_BLK_101._RESERVED = 0;
	MC_DISDQ_RANK_BLK_101.disdqset = 0;
	MC_DISDQ_RANK_BLK_101.disdqreset = 1;
	MC_DISDQ_RANK_BLK_101.csn_sel = RANK_ALL_SEL;

	// [Rank block 20]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_160;

	MC_IMMCLEAR_RANK_BLK_160.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_160.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_160._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_160.reg_sel = 1;
	MC_IMMCLEAR_RANK_BLK_160.bit_loc = 0;
	MC_IMMCLEAR_RANK_BLK_160.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_161;

	MC_DISDQ_RANK_BLK_161.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_161.last_cmd = 1;
	MC_DISDQ_RANK_BLK_161._RESERVED = 0;
	MC_DISDQ_RANK_BLK_161.disdqset = 1;
	MC_DISDQ_RANK_BLK_161.disdqreset = 0;
	MC_DISDQ_RANK_BLK_161.csn_sel = RANK_ALL_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_162;

	MC_PAUSEREF_RANK_BLK_162.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_162.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_162._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_162.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_162.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_162.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_162.csn_sel = RANK2_SEL;

	MPC_UCODE_t MC_ZQCALLATCH_RANK_BLK_163;

	MC_ZQCALLATCH_RANK_BLK_163.cmd_code = MPC_CMD;
	MC_ZQCALLATCH_RANK_BLK_163.last_cmd = 1;
	MC_ZQCALLATCH_RANK_BLK_163.op = 4;
	MC_ZQCALLATCH_RANK_BLK_163.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_164;

	MC_PAUSEREF_RANK_BLK_164.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_164.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_164._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_164.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_164.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_164.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_164.csn_sel = RANK2_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_165;

	MC_DISDQ_RANK_BLK_165.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_165.last_cmd = 1;
	MC_DISDQ_RANK_BLK_165._RESERVED = 0;
	MC_DISDQ_RANK_BLK_165.disdqset = 0;
	MC_DISDQ_RANK_BLK_165.disdqreset = 1;
	MC_DISDQ_RANK_BLK_165.csn_sel = RANK_ALL_SEL;

	// [Rank block 28]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_224;

	MC_IMMCLEAR_RANK_BLK_224.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_224.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_224._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_224.reg_sel = 1;
	MC_IMMCLEAR_RANK_BLK_224.bit_loc = 4;
	MC_IMMCLEAR_RANK_BLK_224.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_225;

	MC_DISDQ_RANK_BLK_225.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_225.last_cmd = 1;
	MC_DISDQ_RANK_BLK_225._RESERVED = 0;
	MC_DISDQ_RANK_BLK_225.disdqset = 1;
	MC_DISDQ_RANK_BLK_225.disdqreset = 0;
	MC_DISDQ_RANK_BLK_225.csn_sel = RANK_ALL_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_226;

	MC_PAUSEREF_RANK_BLK_226.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_226.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_226._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_226.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_226.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_226.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_226.csn_sel = RANK3_SEL;

	MPC_UCODE_t MC_ZQCALLATCH_RANK_BLK_227;

	MC_ZQCALLATCH_RANK_BLK_227.cmd_code = MPC_CMD;
	MC_ZQCALLATCH_RANK_BLK_227.last_cmd = 1;
	MC_ZQCALLATCH_RANK_BLK_227.op = 4;
	MC_ZQCALLATCH_RANK_BLK_227.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_228;

	MC_PAUSEREF_RANK_BLK_228.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_228.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_228._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_228.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_228.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_228.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_228.csn_sel = RANK3_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_229;

	MC_DISDQ_RANK_BLK_229.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_229.last_cmd = 1;
	MC_DISDQ_RANK_BLK_229._RESERVED = 0;
	MC_DISDQ_RANK_BLK_229.disdqset = 0;
	MC_DISDQ_RANK_BLK_229.disdqreset = 1;
	MC_DISDQ_RANK_BLK_229.csn_sel = RANK_ALL_SEL;

	// [Rank block 5]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_40;

	MC_IMMCLEAR_RANK_BLK_40.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_40.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_40._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_40.reg_sel = 0;
	MC_IMMCLEAR_RANK_BLK_40.bit_loc = 1;
	MC_IMMCLEAR_RANK_BLK_40.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_41;

	MC_DISDQ_RANK_BLK_41.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_41.last_cmd = 1;
	MC_DISDQ_RANK_BLK_41._RESERVED = 0;
	MC_DISDQ_RANK_BLK_41.disdqset = 1;
	MC_DISDQ_RANK_BLK_41.disdqreset = 0;
	MC_DISDQ_RANK_BLK_41.csn_sel = RANK0_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_42;

	MC_PAUSEREF_RANK_BLK_42.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_42.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_42._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_42.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_42.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_42.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_42.csn_sel = RANK0_SEL;

	MRR_UCODE_t MC_MRR_RANK_BLK_43;

	MC_MRR_RANK_BLK_43.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_43.prank_num = 0;
	MC_MRR_RANK_BLK_43.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_43.prank_sel = 0;
	MC_MRR_RANK_BLK_43.last_cmd = 1;
	MC_MRR_RANK_BLK_43.mra = 46;

	MRR_UCODE_t MC_MRR_RANK_BLK_44;

	MC_MRR_RANK_BLK_44.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_44.prank_num = 0;
	MC_MRR_RANK_BLK_44.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_44.prank_sel = 0;
	MC_MRR_RANK_BLK_44.last_cmd = 1;
	MC_MRR_RANK_BLK_44.mra = 47;

	MRR_UCODE_t MC_MRR_RANK_BLK_45;

	MC_MRR_RANK_BLK_45.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_45.prank_num = 0;
	MC_MRR_RANK_BLK_45.phy_snoop_en = 0;
	MC_MRR_RANK_BLK_45.prank_sel = 0;
	MC_MRR_RANK_BLK_45.last_cmd = 1;
	MC_MRR_RANK_BLK_45.mra = 4;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_46;

	MC_PAUSEREF_RANK_BLK_46.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_46.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_46._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_46.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_46.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_46.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_46.csn_sel = RANK0_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_47;

	MC_DISDQ_RANK_BLK_47.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_47.last_cmd = 1;
	MC_DISDQ_RANK_BLK_47._RESERVED = 0;
	MC_DISDQ_RANK_BLK_47.disdqset = 0;
	MC_DISDQ_RANK_BLK_47.disdqreset = 1;
	MC_DISDQ_RANK_BLK_47.csn_sel = RANK0_SEL;

	// [Rank block 13]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_104;

	MC_IMMCLEAR_RANK_BLK_104.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_104.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_104._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_104.reg_sel = 0;
	MC_IMMCLEAR_RANK_BLK_104.bit_loc = 5;
	MC_IMMCLEAR_RANK_BLK_104.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_105;

	MC_DISDQ_RANK_BLK_105.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_105.last_cmd = 1;
	MC_DISDQ_RANK_BLK_105._RESERVED = 0;
	MC_DISDQ_RANK_BLK_105.disdqset = 1;
	MC_DISDQ_RANK_BLK_105.disdqreset = 0;
	MC_DISDQ_RANK_BLK_105.csn_sel = RANK1_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_106;

	MC_PAUSEREF_RANK_BLK_106.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_106.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_106._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_106.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_106.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_106.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_106.csn_sel = RANK1_SEL;

	MRR_UCODE_t MC_MRR_RANK_BLK_107;

	MC_MRR_RANK_BLK_107.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_107.prank_num = 1;
	MC_MRR_RANK_BLK_107.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_107.prank_sel = 0;
	MC_MRR_RANK_BLK_107.last_cmd = 1;
	MC_MRR_RANK_BLK_107.mra = 46;

	MRR_UCODE_t MC_MRR_RANK_BLK_108;

	MC_MRR_RANK_BLK_108.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_108.prank_num = 1;
	MC_MRR_RANK_BLK_108.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_108.prank_sel = 0;
	MC_MRR_RANK_BLK_108.last_cmd = 1;
	MC_MRR_RANK_BLK_108.mra = 47;

	MRR_UCODE_t MC_MRR_RANK_BLK_109;

	MC_MRR_RANK_BLK_109.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_109.prank_num = 1;
	MC_MRR_RANK_BLK_109.phy_snoop_en = 0;
	MC_MRR_RANK_BLK_109.prank_sel = 0;
	MC_MRR_RANK_BLK_109.last_cmd = 1;
	MC_MRR_RANK_BLK_109.mra = 4;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_110;

	MC_PAUSEREF_RANK_BLK_110.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_110.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_110._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_110.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_110.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_110.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_110.csn_sel = RANK1_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_111;

	MC_DISDQ_RANK_BLK_111.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_111.last_cmd = 1;
	MC_DISDQ_RANK_BLK_111._RESERVED = 0;
	MC_DISDQ_RANK_BLK_111.disdqset = 0;
	MC_DISDQ_RANK_BLK_111.disdqreset = 1;
	MC_DISDQ_RANK_BLK_111.csn_sel = RANK1_SEL;

	// [Rank block 21]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_168;

	MC_IMMCLEAR_RANK_BLK_168.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_168.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_168._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_168.reg_sel = 1;
	MC_IMMCLEAR_RANK_BLK_168.bit_loc = 1;
	MC_IMMCLEAR_RANK_BLK_168.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_169;

	MC_DISDQ_RANK_BLK_169.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_169.last_cmd = 1;
	MC_DISDQ_RANK_BLK_169._RESERVED = 0;
	MC_DISDQ_RANK_BLK_169.disdqset = 1;
	MC_DISDQ_RANK_BLK_169.disdqreset = 0;
	MC_DISDQ_RANK_BLK_169.csn_sel = RANK2_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_170;

	MC_PAUSEREF_RANK_BLK_170.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_170.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_170._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_170.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_170.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_170.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_170.csn_sel = RANK2_SEL;

	MRR_UCODE_t MC_MRR_RANK_BLK_171;

	MC_MRR_RANK_BLK_171.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_171.prank_num = 2;
	MC_MRR_RANK_BLK_171.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_171.prank_sel = 0;
	MC_MRR_RANK_BLK_171.last_cmd = 1;
	MC_MRR_RANK_BLK_171.mra = 46;

	MRR_UCODE_t MC_MRR_RANK_BLK_172;

	MC_MRR_RANK_BLK_172.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_172.prank_num = 2;
	MC_MRR_RANK_BLK_172.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_172.prank_sel = 0;
	MC_MRR_RANK_BLK_172.last_cmd = 1;
	MC_MRR_RANK_BLK_172.mra = 47;

	MRR_UCODE_t MC_MRR_RANK_BLK_173;

	MC_MRR_RANK_BLK_173.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_173.prank_num = 2;
	MC_MRR_RANK_BLK_173.phy_snoop_en = 0;
	MC_MRR_RANK_BLK_173.prank_sel = 0;
	MC_MRR_RANK_BLK_173.last_cmd = 1;
	MC_MRR_RANK_BLK_173.mra = 4;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_174;

	MC_PAUSEREF_RANK_BLK_174.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_174.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_174._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_174.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_174.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_174.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_174.csn_sel = RANK2_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_175;

	MC_DISDQ_RANK_BLK_175.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_175.last_cmd = 1;
	MC_DISDQ_RANK_BLK_175._RESERVED = 0;
	MC_DISDQ_RANK_BLK_175.disdqset = 0;
	MC_DISDQ_RANK_BLK_175.disdqreset = 1;
	MC_DISDQ_RANK_BLK_175.csn_sel = RANK2_SEL;

	// [Rank block 29]
	IMM_BIT_UCODE_t MC_IMMCLEAR_RANK_BLK_232;

	MC_IMMCLEAR_RANK_BLK_232.cmd_code = IMM_BIT_CMD;
	MC_IMMCLEAR_RANK_BLK_232.imm_type = 0;
	MC_IMMCLEAR_RANK_BLK_232._RESERVED = 0;
	MC_IMMCLEAR_RANK_BLK_232.reg_sel = 1;
	MC_IMMCLEAR_RANK_BLK_232.bit_loc = 5;
	MC_IMMCLEAR_RANK_BLK_232.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_233;

	MC_DISDQ_RANK_BLK_233.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_233.last_cmd = 1;
	MC_DISDQ_RANK_BLK_233._RESERVED = 0;
	MC_DISDQ_RANK_BLK_233.disdqset = 1;
	MC_DISDQ_RANK_BLK_233.disdqreset = 0;
	MC_DISDQ_RANK_BLK_233.csn_sel = RANK3_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_234;

	MC_PAUSEREF_RANK_BLK_234.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_234.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_234._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_234.pausereftype = 1;
	MC_PAUSEREF_RANK_BLK_234.pauserefset = 1;
	MC_PAUSEREF_RANK_BLK_234.pauserefreset = 0;
	MC_PAUSEREF_RANK_BLK_234.csn_sel = RANK3_SEL;

	MRR_UCODE_t MC_MRR_RANK_BLK_235;

	MC_MRR_RANK_BLK_235.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_235.prank_num = 3;
	MC_MRR_RANK_BLK_235.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_235.prank_sel = 0;
	MC_MRR_RANK_BLK_235.last_cmd = 1;
	MC_MRR_RANK_BLK_235.mra = 46;

	MRR_UCODE_t MC_MRR_RANK_BLK_236;

	MC_MRR_RANK_BLK_236.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_236.prank_num = 3;
	MC_MRR_RANK_BLK_236.phy_snoop_en = 1;
	MC_MRR_RANK_BLK_236.prank_sel = 0;
	MC_MRR_RANK_BLK_236.last_cmd = 1;
	MC_MRR_RANK_BLK_236.mra = 47;

	MRR_UCODE_t MC_MRR_RANK_BLK_237;

	MC_MRR_RANK_BLK_237.cmd_code = MRR_CMD;
	MC_MRR_RANK_BLK_237.prank_num = 3;
	MC_MRR_RANK_BLK_237.phy_snoop_en = 0;
	MC_MRR_RANK_BLK_237.prank_sel = 0;
	MC_MRR_RANK_BLK_237.last_cmd = 1;
	MC_MRR_RANK_BLK_237.mra = 4;

	PAUSEREF_UCODE_t MC_PAUSEREF_RANK_BLK_238;

	MC_PAUSEREF_RANK_BLK_238.cmd_code = PAUSEREF_CMD;
	MC_PAUSEREF_RANK_BLK_238.last_cmd = 1;
	MC_PAUSEREF_RANK_BLK_238._RESERVED = 0;
	MC_PAUSEREF_RANK_BLK_238.pausereftype = 0;
	MC_PAUSEREF_RANK_BLK_238.pauserefset = 0;
	MC_PAUSEREF_RANK_BLK_238.pauserefreset = 1;
	MC_PAUSEREF_RANK_BLK_238.csn_sel = RANK3_SEL;

	DISDQ_UCODE_t MC_DISDQ_RANK_BLK_239;

	MC_DISDQ_RANK_BLK_239.cmd_code = DISDQ_CMD;
	MC_DISDQ_RANK_BLK_239.last_cmd = 1;
	MC_DISDQ_RANK_BLK_239._RESERVED = 0;
	MC_DISDQ_RANK_BLK_239.disdqset = 0;
	MC_DISDQ_RANK_BLK_239.disdqreset = 1;
	MC_DISDQ_RANK_BLK_239.csn_sel = RANK3_SEL;

	MPC_UCODE_t MC_MANUALECS[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_MANUALECS[i].cmd_code = MPC_CMD;
		MC_MANUALECS[i].last_cmd = 1;
		MC_MANUALECS[i].op = 12; // OP
	}
	MC_MANUALECS[0].csn_sel = RANK0_SEL;
	MC_MANUALECS[1].csn_sel = RANK1_SEL;
	MC_MANUALECS[2].csn_sel = RANK2_SEL;
	MC_MANUALECS[3].csn_sel = RANK3_SEL;
	MC_MANUALECS[4].csn_sel = RANK_R15_SEL;

	MRW1_UCODE_t MC_MRW14_1[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_MRW14_1[i].cmd_code = MRW_CMD;
		MC_MRW14_1[i].last_cmd = 1;
		MC_MRW14_1[i].wait_time = 0;
	}

	MC_MRW14_1[0].csn_sel = RANK0_SEL;
	MC_MRW14_1[1].csn_sel = RANK1_SEL;
	MC_MRW14_1[2].csn_sel = RANK2_SEL;
	MC_MRW14_1[3].csn_sel = RANK3_SEL;
	MC_MRW14_1[4].csn_sel = RANK_R15_SEL;

	MRW2_UCODE_t MC_MRW14_2[4];

	for (uint32_t i = 0; i < 4; i++)
		MC_MRW14_2[i].mra = 14;

	MC_MRW14_2[0].op = 128;
	MC_MRW14_2[1].op = 129;
	MC_MRW14_2[2].op = 130;
	MC_MRW14_2[3].op = 131;

	MRR_UCODE_t MC_MRR46[4][2];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 0; j < 2; j++) {
			MC_MRR46[i][j].cmd_code = MRR_CMD;
			MC_MRR46[i][j].prank_num = i;
			MC_MRR46[i][j].phy_snoop_en = j;
			MC_MRR46[i][j].prank_sel = 0;
			MC_MRR46[i][j].last_cmd = 1;
			MC_MRR46[i][j].mra = 46;
		}
	}

	MRR_UCODE_t MC_MRR47[4][2];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 0; j < 2; j++) {
			MC_MRR47[i][j].cmd_code = MRR_CMD;
			MC_MRR47[i][j].prank_num = i;
			MC_MRR47[i][j].phy_snoop_en = j;
			MC_MRR47[i][j].prank_sel = 0;
			MC_MRR47[i][j].last_cmd = 1;
			MC_MRR47[i][j].mra = 47;
		}
	}

	DES_UCODE_t MC_DES;

	MC_DES.cmd_code = DES_CMD;
	MC_DES.last_cmd = 1;
	MC_DES.unit_sel = 0;
	MC_DES.unit_count = 1;

	IWAIT_REG_UCODE_t MC_IWAITTECSC;

	MC_IWAITTECSC.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTECSC.wait_type = 1;
	MC_IWAITTECSC._RESERVED = 0;
	MC_IWAITTECSC.wait_reg = 0; //tECSC

	IWAIT_REG_UCODE_t MC_IWAITTRKCALCCUR;

	MC_IWAITTRKCALCCUR.cmd_code  = IWAIT_TIME_CMD;
	MC_IWAITTRKCALCCUR.wait_type = 1;
	MC_IWAITTRKCALCCUR._RESERVED = 0;
	MC_IWAITTRKCALCCUR.wait_reg  = 6;

	DISDQ_UCODE_t MC_DISDQ[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_DISDQ[i].cmd_code = DISDQ_CMD;
		MC_DISDQ[i].last_cmd = 1;
		MC_DISDQ[i]._RESERVED = 0;
		MC_DISDQ[i].disdqset = 1;
		MC_DISDQ[i].disdqreset = 0;
	}

	MC_DISDQ[0].csn_sel = RANK0_SEL;
	MC_DISDQ[1].csn_sel = RANK1_SEL;
	MC_DISDQ[2].csn_sel = RANK2_SEL;
	MC_DISDQ[3].csn_sel = RANK3_SEL;
	MC_DISDQ[4].csn_sel = RANK0_1_SEL;
	MC_DISDQ[5].csn_sel = RANK2_3_SEL;
	MC_DISDQ[6].csn_sel = RANK_ALL_SEL;
	MC_DISDQ[7].csn_sel = RANK_R15_SEL;

	DISDQ_UCODE_t MC_ENDQ[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_ENDQ[i].cmd_code = DISDQ_CMD;
		MC_ENDQ[i].last_cmd = 1;
		MC_ENDQ[i]._RESERVED = 0;
		MC_ENDQ[i].disdqset = 0;
		MC_ENDQ[i].disdqreset = 1;
	}

	MC_ENDQ[0].csn_sel = RANK0_SEL;
	MC_ENDQ[1].csn_sel = RANK1_SEL;
	MC_ENDQ[2].csn_sel = RANK2_SEL;
	MC_ENDQ[3].csn_sel = RANK3_SEL;
	MC_ENDQ[4].csn_sel = RANK0_1_SEL;
	MC_ENDQ[5].csn_sel = RANK2_3_SEL;
	MC_ENDQ[6].csn_sel = RANK_ALL_SEL;
	MC_ENDQ[7].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_PAUSEREF[i].cmd_code = PAUSEREF_CMD;
		MC_PAUSEREF[i].last_cmd = 1;
		MC_PAUSEREF[i]._RESERVED = 0;
		MC_PAUSEREF[i].pausereftype = 0;
		MC_PAUSEREF[i].pauserefset = 1;
		MC_PAUSEREF[i].pauserefreset = 0;
	}

	MC_PAUSEREF[0].csn_sel = RANK0_SEL;
	MC_PAUSEREF[1].csn_sel = RANK1_SEL;
	MC_PAUSEREF[2].csn_sel = RANK2_SEL;
	MC_PAUSEREF[3].csn_sel = RANK3_SEL;
	MC_PAUSEREF[4].csn_sel = RANK0_1_SEL;
	MC_PAUSEREF[5].csn_sel = RANK2_3_SEL;
	MC_PAUSEREF[6].csn_sel = RANK_ALL_SEL;
	MC_PAUSEREF[7].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_BLOCKREF[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_BLOCKREF[i].cmd_code = PAUSEREF_CMD;
		MC_BLOCKREF[i].last_cmd = 1;
		MC_BLOCKREF[i]._RESERVED = 0;
		MC_BLOCKREF[i].pausereftype = 1;
		MC_BLOCKREF[i].pauserefset = 1;
		MC_BLOCKREF[i].pauserefreset = 0;
	}

	MC_BLOCKREF[0].csn_sel = RANK0_SEL;
	MC_BLOCKREF[1].csn_sel = RANK1_SEL;
	MC_BLOCKREF[2].csn_sel = RANK2_SEL;
	MC_BLOCKREF[3].csn_sel = RANK3_SEL;
	MC_BLOCKREF[4].csn_sel = RANK0_1_SEL;
	MC_BLOCKREF[5].csn_sel = RANK2_3_SEL;
	MC_BLOCKREF[6].csn_sel = RANK_ALL_SEL;
	MC_BLOCKREF[7].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_RESUMEREF[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_RESUMEREF[i].cmd_code = PAUSEREF_CMD;
		MC_RESUMEREF[i].last_cmd = 1;
		MC_RESUMEREF[i]._RESERVED = 0;
		MC_RESUMEREF[i].pausereftype = 0;
		MC_RESUMEREF[i].pauserefset = 0;
		MC_RESUMEREF[i].pauserefreset = 1;
	}

	MC_RESUMEREF[0].csn_sel = RANK0_SEL;
	MC_RESUMEREF[1].csn_sel = RANK1_SEL;
	MC_RESUMEREF[2].csn_sel = RANK2_SEL;
	MC_RESUMEREF[3].csn_sel = RANK3_SEL;
	MC_RESUMEREF[4].csn_sel = RANK0_1_SEL;
	MC_RESUMEREF[5].csn_sel = RANK2_3_SEL;
	MC_RESUMEREF[6].csn_sel = RANK_ALL_SEL;
	MC_RESUMEREF[7].csn_sel = RANK_R15_SEL;

	PRANK_PREAB_UCODE_t MC_PRANKPREAB[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PRANKPREAB[i].cmd_code = PRANK_PREAB_CMD;
		MC_PRANKPREAB[i].last_cmd = 1;
		MC_PRANKPREAB[i]._RESERVED = 0;
		MC_PRANKPREAB[i].wait_type = 1;
		MC_PRANKPREAB[i].wait_reg = 3; //tRP
	}

	MC_PRANKPREAB[0].csn_sel = RANK0_SEL;
	MC_PRANKPREAB[1].csn_sel = RANK1_SEL;
	MC_PRANKPREAB[2].csn_sel = RANK2_SEL;
	MC_PRANKPREAB[3].csn_sel = RANK3_SEL;
	MC_PRANKPREAB[4].csn_sel = RANK_R15_SEL;

	LOCK_CTRL_UCODE_t MC_UNLOCKCTRL;

	MC_UNLOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_UNLOCKCTRL._RESERVED = 0;
	MC_UNLOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.reset_urgent_flag = 0;
	MC_UNLOCKCTRL.set_urgent_flag = 0;
	MC_UNLOCKCTRL.unlock_ci_bus = 1;
	MC_UNLOCKCTRL.lock_ci_bus = 0;

	LOCK_CTRL_UCODE_t MC_LOCKCTRL;

	MC_LOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_LOCKCTRL._RESERVED = 0;
	MC_LOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.reset_urgent_flag = 0;
	MC_LOCKCTRL.set_urgent_flag = 0;
	MC_LOCKCTRL.unlock_ci_bus = 0;
	MC_LOCKCTRL.lock_ci_bus = 1;

	MOV_UCODE_t MC_MOVR02R15;

	MC_MOVR02R15.cmd_code = MOV_CMD;
	MC_MOVR02R15.mov_dir = 1;
	MC_MOVR02R15.mov_type = 0;
	MC_MOVR02R15._RESERVED = 0;
	MC_MOVR02R15.reg_num = 15;

	MOV_UCODE_t MC_MOVCSn2R0[6];

	MC_MOVCSn2R0[4].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[4].mov_dir = 0;
	MC_MOVCSn2R0[4].mov_type = 1;
	MC_MOVCSn2R0[4]._RESERVED = 0;
	MC_MOVCSn2R0[4].reg_num = 4;
	MC_MOVCSn2R0[5].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[5].mov_dir = 0;
	MC_MOVCSn2R0[5].mov_type = 1;
	MC_MOVCSn2R0[5]._RESERVED = 0;
	MC_MOVCSn2R0[5].reg_num = 5;
	MPC_UCODE_t MC_DQSOSCSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_DQSOSCSTART[i].cmd_code = MPC_CMD;
		MC_DQSOSCSTART[i].last_cmd = 1;
		MC_DQSOSCSTART[i].op = 7; // OP
	}

	MC_DQSOSCSTART[0].csn_sel = RANK0_SEL;
	MC_DQSOSCSTART[1].csn_sel = RANK1_SEL;
	MC_DQSOSCSTART[2].csn_sel = RANK2_SEL;
	MC_DQSOSCSTART[3].csn_sel = RANK3_SEL;
	MC_DQSOSCSTART[4].csn_sel = RANK_R15_SEL;

	IWAIT_SIG_UCODE_t MC_IWAITDQSOSCACK;

	MC_IWAITDQSOSCACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITDQSOSCACK.sig_value = 1;
	MC_IWAITDQSOSCACK.sig_sel = 0;
	MC_IWAITDQSOSCACK.wait_cycle = 0;

	IMM_BIT_UCODE_t MC_STOREDQSOSCSTART;

	MC_STOREDQSOSCSTART.cmd_code = IMM_BIT_CMD;
	MC_STOREDQSOSCSTART.imm_type = 0;
	MC_STOREDQSOSCSTART._RESERVED = 0;
	MC_STOREDQSOSCSTART.reg_sel = 3;
	MC_STOREDQSOSCSTART.bit_loc = 5;
	MC_STOREDQSOSCSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARDQSOSCSTART;

	MC_CLEARDQSOSCSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARDQSOSCSTART.imm_type = 0;
	MC_CLEARDQSOSCSTART._RESERVED = 0;
	MC_CLEARDQSOSCSTART.reg_sel = 3;
	MC_CLEARDQSOSCSTART.bit_loc = 5;
	MC_CLEARDQSOSCSTART.bit_val = 0;

	JPC_UCODE_t MC_JPC4AR[4][9];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 1; j < 9; j++) {
			MC_JPC4AR[i][j].cmd_code = JPC_CMD;
			MC_JPC4AR[i][j].sig_value = 1;
			MC_JPC4AR[i][j].sig_sel = 4 + i;
			MC_JPC4AR[i][j].jmp_dir = 0;
			MC_JPC4AR[i][j].jmp_step = j;
		}
   }

	SRX_DONE_UCODE_t MC_SRXDONETXSDLL[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRXDONETXSDLL[i].cmd_code = SRX_DONE_CMD;
		MC_SRXDONETXSDLL[i].last_cmd = 1;
		MC_SRXDONETXSDLL[i]._RESERVED = 0;
		MC_SRXDONETXSDLL[i].srx_done_txsdll = 1;
		MC_SRXDONETXSDLL[i].srx_done_txs = 0;
	}

	MC_SRXDONETXSDLL[0].csn_sel = RANK0_SEL;
	MC_SRXDONETXSDLL[1].csn_sel = RANK1_SEL;
	MC_SRXDONETXSDLL[2].csn_sel = RANK2_SEL;
	MC_SRXDONETXSDLL[3].csn_sel = RANK3_SEL;
	MC_SRXDONETXSDLL[4].csn_sel = RANK0_1_SEL;
	MC_SRXDONETXSDLL[5].csn_sel = RANK2_3_SEL;
	MC_SRXDONETXSDLL[6].csn_sel = RANK_ALL_SEL;
	MC_SRXDONETXSDLL[7].csn_sel = RANK_R15_SEL;

	IWAIT_REG_UCODE_t MC_IWAITTZQLAT;

	MC_IWAITTZQLAT.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQLAT.wait_type = 1;
	MC_IWAITTZQLAT._RESERVED = 0;
	MC_IWAITTZQLAT.wait_reg = 4;

	IWAIT_REG_UCODE_t MC_IWAITTZQCAL;

	MC_IWAITTZQCAL.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQCAL.wait_type = 1;
	MC_IWAITTZQCAL._RESERVED = 0;
	MC_IWAITTZQCAL.wait_reg = 5;

	CTRLUPD_UCODE_t MC_CTRLUPD;

	MC_CTRLUPD.cmd_code = CTRLUPD_CMD;
	MC_CTRLUPD.last_cmd = 1;
	MC_CTRLUPD.dfi_ctrlupd_req_set = 1;
	MC_CTRLUPD.dfi_ctrlupd_retry_en = 0;
	MC_CTRLUPD.wait_unit = 0;
	MC_CTRLUPD.wait_time = 0;

	MPC_UCODE_t MC_ZQCALSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALSTART[i].cmd_code = MPC_CMD;
		MC_ZQCALSTART[i].last_cmd = 1;
		MC_ZQCALSTART[i].op = 5; // OP (ZQCal Start)
	}

	MC_ZQCALSTART[0].csn_sel = RANK0_SEL;
	MC_ZQCALSTART[1].csn_sel = RANK1_SEL;
	MC_ZQCALSTART[2].csn_sel = RANK2_SEL;
	MC_ZQCALSTART[3].csn_sel = RANK3_SEL;
	MC_ZQCALSTART[4].csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_ZQCALLATCH[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALLATCH[i].cmd_code = MPC_CMD;
		MC_ZQCALLATCH[i].last_cmd = 0;
		MC_ZQCALLATCH[i].op = 4; // OP (ZQCal Latch)
	}

	MC_ZQCALLATCH[0].csn_sel = RANK0_SEL;
	MC_ZQCALLATCH[1].csn_sel = RANK1_SEL;
	MC_ZQCALLATCH[2].csn_sel = RANK2_SEL;
	MC_ZQCALLATCH[3].csn_sel = RANK3_SEL;
	MC_ZQCALLATCH[4].csn_sel = RANK_R15_SEL;

	SNPS_TRACE("Entering");

  for (uint32_t ch = 0; ch < active_channels; ch++) {
		// [Global block 0]
		dwc_ddrctl_cinit_write_du_cmdbuf(0, MC_MOVCSn2R0_GLB_BLK_0.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(1, MC_MOVCSn2R15_GLB_BLK_1.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(2, MC_DISDQ_GLB_BLK_2.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(3, MC_PAUSEREF_GLB_BLK_3.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(4, MC_ZQCALSTART_GLB_BLK_4.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(5, MC_PAUSEREF_GLB_BLK_5.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(6, MC_DISDQ_GLB_BLK_6.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(7, MC_IMMSET_GLB_BLK_7.value, 0, ch);
		// [Global block 1]
		dwc_ddrctl_cinit_write_du_cmdbuf(8, MC_CTRLUPD_GLB_BLK_8.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(9, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(10, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(11, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(12, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(13, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(14, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(15, 0x0, 0, ch);
		// [Global block 4]
		dwc_ddrctl_cinit_write_du_cmdbuf(16, MC_IMMCLEAR_GLB_BLK_32.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(17, MC_MOVCSn2R0_GLB_BLK_33.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(18, MC_MOVCSn2R15_GLB_BLK_34.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(19, MC_DISDQ_GLB_BLK_35.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(20, MC_PAUSEREF_GLB_BLK_36.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(21, MC_ZQCALLATCH_GLB_BLK_37.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(22, MC_PAUSEREF_GLB_BLK_38.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(23, MC_DISDQ_GLB_BLK_39.value, 0, ch);
		// [Global block 5]
		dwc_ddrctl_cinit_write_du_cmdbuf(24, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(25, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(26, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(27, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(28, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(29, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(30, 0x0, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(31, 0x0, 0, ch);
		// [Global block 7]
		dwc_ddrctl_cinit_write_du_cmdbuf(32, MC_MOVCSn2R0[5].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(33, MC_MOVR02R15.value       , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(34, MC_BLOCKREF[7].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(35, MC_DQSOSCSTART[4].value  , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(36, MC_STOREDQSOSCSTART.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(37, MC_RESUMEREF[7].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(38, MC_JPC4AR[3][8].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(39, MC_BLOCKREF[3].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(40, MC_ZQCALSTART[3].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(41, MC_RESUMEREF[3].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(42, MC_IWAITTZQCAL.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(43, MC_BLOCKREF[3].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(44, MC_ZQCALLATCH[3].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(45, MC_RESUMEREF[3].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(46, MC_IWAITTZQLAT.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(47, MC_JPC4AR[2][8].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(48, MC_BLOCKREF[2].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(49, MC_ZQCALSTART[2].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(50, MC_RESUMEREF[2].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(51, MC_IWAITTZQCAL.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(52, MC_BLOCKREF[2].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(53, MC_ZQCALLATCH[2].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(54, MC_RESUMEREF[2].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(55, MC_IWAITTZQLAT.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(56, MC_JPC4AR[1][8].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(57, MC_BLOCKREF[1].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(58, MC_ZQCALSTART[1].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(59, MC_RESUMEREF[1].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(60, MC_IWAITTZQCAL.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(61, MC_BLOCKREF[1].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(62, MC_ZQCALLATCH[1].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(63, MC_RESUMEREF[1].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(64, MC_IWAITTZQLAT.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(65, MC_BLOCKREF[0].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(66, MC_ZQCALSTART[0].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(67, MC_RESUMEREF[0].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(68, MC_IWAITTZQCAL.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(69, MC_BLOCKREF[0].value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(70, MC_ZQCALLATCH[0].value   , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(71, MC_RESUMEREF[0].value    , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(72, MC_IWAITTZQLAT.value     , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(73, MC_IWAITDQSOSCACK.value  , 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(74, MC_CLEARDQSOSCSTART.value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(75, MC_SRXDONETXSDLL[7].value, 0, ch);
		dwc_ddrctl_cinit_write_du_cmdbuf(76, MC_BLOCKREF[7].value     , 0, ch);
		if (dimm_type != DWC_LRDIMM) {
   		dwc_ddrctl_cinit_write_du_cmdbuf(77, MC_JPC4AR[3][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(78, MC_MRR46[3][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(79, MC_MRR47[3][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(80, MC_DES.value             , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(81, MC_JPC4AR[2][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(82, MC_MRR46[2][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(83, MC_MRR47[2][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(84, MC_DES.value             , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(85, MC_JPC4AR[1][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(86, MC_MRR46[1][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(87, MC_MRR47[1][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(88, MC_DES.value             , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(89, MC_MRR46[0][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(90, MC_MRR47[0][1].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(91, MC_DES.value             , 0, ch);
		} else {                                                                    // LRDIMM
   		dwc_ddrctl_cinit_write_du_cmdbuf(77, MC_JPC4AR[3][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(78, MC_MRR46[3][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(79, MC_MRR47[3][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(80, MC_IWAITTRKCALCCUR.value , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(81, MC_JPC4AR[2][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(82, MC_MRR46[2][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(83, MC_MRR47[2][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(84, MC_IWAITTRKCALCCUR.value , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(85, MC_JPC4AR[1][3].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(86, MC_MRR46[1][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(87, MC_MRR47[1][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(88, MC_IWAITTRKCALCCUR.value , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(89, MC_MRR46[0][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(90, MC_MRR47[0][0].value     , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(91, MC_IWAITTRKCALCCUR.value , 0, ch);
   		}
   		dwc_ddrctl_cinit_write_du_cmdbuf(92, MC_RESUMEREF[7].value    , 0, ch);
   		dwc_ddrctl_cinit_write_du_cmdbuf(93, MC_CTRLUPD.value         , 0, ch);

		if (dimm_type != DWC_LRDIMM) {
			// [Rank block 0]
			dwc_ddrctl_cinit_write_du_cmdbuf(0, MC_DISDQ_RANK_BLK_0.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(1, MC_PAUSEREF_RANK_BLK_1.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(2, MC_ZQCALSTART_RANK_BLK_2.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(3, MC_PAUSEREF_RANK_BLK_3.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(4, MC_DISDQ_RANK_BLK_4.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(5, MC_IMMSET_RANK_BLK_5.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(6, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(7, 0x0, 1, ch);
			// [Rank block 1]
			dwc_ddrctl_cinit_write_du_cmdbuf(8 , MC_DISDQ_RANK_BLK_8.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(9 , MC_PAUSEREF_RANK_BLK_9.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(10, MC_DQSOSCSTART_RANK_BLK_10.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(11, MC_PAUSEREF_RANK_BLK_11.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(12, MC_DISDQ_RANK_BLK_12.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(13, MC_IMMSET_RANK_BLK_13.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(14, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(15, 0x0, 1, ch);
			// [Rank block 4]
			dwc_ddrctl_cinit_write_du_cmdbuf(16, MC_IMMCLEAR_RANK_BLK_32.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(17, MC_DISDQ_RANK_BLK_33.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(18, MC_PAUSEREF_RANK_BLK_34.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(19, MC_ZQCALLATCH_RANK_BLK_35.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(20, MC_PAUSEREF_RANK_BLK_36.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(21, MC_DISDQ_RANK_BLK_37.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(22, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(23, 0x0, 1, ch);
			// [Rank block 5]
			dwc_ddrctl_cinit_write_du_cmdbuf(24, MC_IMMCLEAR_RANK_BLK_40.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(25, MC_DISDQ_RANK_BLK_41.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(26, MC_PAUSEREF_RANK_BLK_42.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(27, MC_MRR_RANK_BLK_43.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(28, MC_MRR_RANK_BLK_44.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(29, MC_MRR_RANK_BLK_45.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(30, MC_PAUSEREF_RANK_BLK_46.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(31, MC_DISDQ_RANK_BLK_47.value, 1, ch);
			// [Rank block 6]
			dwc_ddrctl_cinit_write_du_cmdbuf(32, MC_DISDQ[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(33, MC_BLOCKREF[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(34, MC_LOCKCTRL.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(35, MC_PRANKPREAB[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(36, MC_MRW14_1[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(37, MC_MRW14_2[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(38, MC_MANUALECS[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(39, MC_IWAITTECSC.value, 1, ch);
			if (active_logical_ranks == 1 || active_logical_ranks == 2) {
				dwc_ddrctl_cinit_write_du_cmdbuf(40, MC_MRW14_1[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(41, MC_MRW14_2[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(42, MC_MANUALECS[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(43, MC_IWAITTECSC.value, 1, ch);
			} else {
				dwc_ddrctl_cinit_write_du_cmdbuf(40, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(41, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(42, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(43, MC_DES.value, 1, ch);
			}
			if (active_logical_ranks == 2) {
				dwc_ddrctl_cinit_write_du_cmdbuf(44, MC_MRW14_1[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(45, MC_MRW14_2[2].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(46, MC_MANUALECS[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(47, MC_IWAITTECSC.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(48, MC_MRW14_1[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(49, MC_MRW14_2[3].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(50, MC_MANUALECS[0].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(51, MC_IWAITTECSC.value, 1, ch);
			} else {
				dwc_ddrctl_cinit_write_du_cmdbuf(44, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(45, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(46, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(47, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(48, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(49, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(50, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(51, MC_DES.value, 1, ch);
			}
			dwc_ddrctl_cinit_write_du_cmdbuf(52, MC_UNLOCKCTRL.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(53, MC_RESUMEREF[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(54, MC_ENDQ[0].value, 1, ch);

#ifdef MEMC_NUM_RANKS_GT_1
			// [Rank block 8]
			dwc_ddrctl_cinit_write_du_cmdbuf(64, MC_DISDQ_RANK_BLK_64.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(65, MC_PAUSEREF_RANK_BLK_65.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(66, MC_ZQCALSTART_RANK_BLK_66.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(67, MC_PAUSEREF_RANK_BLK_67.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(68, MC_DISDQ_RANK_BLK_68.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(69, MC_IMMSET_RANK_BLK_69.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(70, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(71, 0x0, 1, ch);
			// [Rank block 9]
			dwc_ddrctl_cinit_write_du_cmdbuf(72, MC_DISDQ_RANK_BLK_72.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(73, MC_PAUSEREF_RANK_BLK_73.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(74, MC_DQSOSCSTART_RANK_BLK_74.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(75, MC_PAUSEREF_RANK_BLK_75.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(76, MC_DISDQ_RANK_BLK_76.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(77, MC_IMMSET_RANK_BLK_77.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(78, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(79, 0x0, 1, ch);
			// [Rank block 12]
			dwc_ddrctl_cinit_write_du_cmdbuf(80, MC_IMMCLEAR_RANK_BLK_96.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(81, MC_DISDQ_RANK_BLK_97.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(82, MC_PAUSEREF_RANK_BLK_98.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(83, MC_ZQCALLATCH_RANK_BLK_99.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(84, MC_PAUSEREF_RANK_BLK_100.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(85, MC_DISDQ_RANK_BLK_101.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(86, 0x0, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(87, 0x0, 1, ch);
			// [Rank block 13]
			dwc_ddrctl_cinit_write_du_cmdbuf(88, MC_IMMCLEAR_RANK_BLK_104.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(89, MC_DISDQ_RANK_BLK_105.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(90, MC_PAUSEREF_RANK_BLK_106.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(91, MC_MRR_RANK_BLK_107.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(92, MC_MRR_RANK_BLK_108.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(93, MC_MRR_RANK_BLK_109.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(94, MC_PAUSEREF_RANK_BLK_110.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(95, MC_DISDQ_RANK_BLK_111.value, 1, ch);
			// [Rank block 14]
			dwc_ddrctl_cinit_write_du_cmdbuf(96, MC_DISDQ[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(97, MC_BLOCKREF[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(98, MC_LOCKCTRL.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(99, MC_PRANKPREAB[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(100, MC_MRW14_1[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(101, MC_MRW14_2[0].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(102, MC_MANUALECS[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(103, MC_IWAITTECSC.value, 1, ch);
			if (active_logical_ranks == 1 || active_logical_ranks == 2) {
				dwc_ddrctl_cinit_write_du_cmdbuf(104, MC_MRW14_1[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(105, MC_MRW14_2[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(106, MC_MANUALECS[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(107, MC_IWAITTECSC.value, 1, ch);
			} else {
				dwc_ddrctl_cinit_write_du_cmdbuf(104, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(105, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(106, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(107, MC_DES.value, 1, ch);
			}
			if (active_logical_ranks == 2) {
				dwc_ddrctl_cinit_write_du_cmdbuf(108, MC_MRW14_1[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(109, MC_MRW14_2[2].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(110, MC_MANUALECS[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(111, MC_IWAITTECSC.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(112, MC_MRW14_1[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(113, MC_MRW14_2[3].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(114, MC_MANUALECS[1].value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(115, MC_IWAITTECSC.value, 1, ch);
			} else {
				dwc_ddrctl_cinit_write_du_cmdbuf(108, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(109, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(110, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(111, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(112, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(113, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(114, MC_DES.value, 1, ch);
				dwc_ddrctl_cinit_write_du_cmdbuf(115, MC_DES.value, 1, ch);
			}
			dwc_ddrctl_cinit_write_du_cmdbuf(116, MC_UNLOCKCTRL.value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(117, MC_RESUMEREF[1].value, 1, ch);
			dwc_ddrctl_cinit_write_du_cmdbuf(118, MC_ENDQ[1].value, 1, ch);
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef MEMC_NUM_RANKS_GT_2
            // [Rank block 16]
		    dwc_ddrctl_cinit_write_du_cmdbuf(128, MC_DISDQ_RANK_BLK_128.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(129, MC_PAUSEREF_RANK_BLK_129.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(130, MC_ZQCALSTART_RANK_BLK_130.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(131, MC_PAUSEREF_RANK_BLK_131.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(132, MC_DISDQ_RANK_BLK_132.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(133, MC_IMMSET_RANK_BLK_133.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(134, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(135, 0x0                              , 1, ch);
            // [Rank block 17]
		    dwc_ddrctl_cinit_write_du_cmdbuf(136, MC_DISDQ_RANK_BLK_136.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(137, MC_PAUSEREF_RANK_BLK_137.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(138, MC_DQSOSCSTART_RANK_BLK_138.value, 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(139, MC_PAUSEREF_RANK_BLK_139.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(140, MC_DISDQ_RANK_BLK_140.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(141, MC_IMMSET_RANK_BLK_141.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(142, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(143, 0x0                              , 1, ch);
            // [Rank block 20]
		    dwc_ddrctl_cinit_write_du_cmdbuf(144, MC_IMMCLEAR_RANK_BLK_160.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(145, MC_DISDQ_RANK_BLK_161.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(146, MC_PAUSEREF_RANK_BLK_162.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(147, MC_ZQCALLATCH_RANK_BLK_163.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(148, MC_PAUSEREF_RANK_BLK_164.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(149, MC_DISDQ_RANK_BLK_165.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(150, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(151, 0x0                              , 1, ch);
            // [Rank block 21]
		    dwc_ddrctl_cinit_write_du_cmdbuf(152, MC_IMMCLEAR_RANK_BLK_168.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(153, MC_DISDQ_RANK_BLK_169.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(154, MC_PAUSEREF_RANK_BLK_170.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(155, MC_MRR_RANK_BLK_171.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(156, MC_MRR_RANK_BLK_172.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(157, MC_MRR_RANK_BLK_173.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(158, MC_PAUSEREF_RANK_BLK_174.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(159, MC_DISDQ_RANK_BLK_175.value      , 1, ch);
            // [Rank block 22]
		    dwc_ddrctl_cinit_write_du_cmdbuf(160, MC_DISDQ[2].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(161, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(162, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(163, MC_PRANKPREAB[2].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(164, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(165, MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(166, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(167, MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(168, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(169, MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(170, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(171, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(168, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(169, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(170, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(171, MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(172, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(173, MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(174, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(175, MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(176, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(177, MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(178, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(179, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(172, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(173, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(174, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(175, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(176, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(177, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(178, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(179, MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(180, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(181, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(182, MC_ENDQ[2].value                 , 1, ch);

            // [Rank block 24]
		    dwc_ddrctl_cinit_write_du_cmdbuf(192, MC_DISDQ_RANK_BLK_192.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(193, MC_PAUSEREF_RANK_BLK_193.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(194, MC_ZQCALSTART_RANK_BLK_194.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(195, MC_PAUSEREF_RANK_BLK_195.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(196, MC_DISDQ_RANK_BLK_196.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(197, MC_IMMSET_RANK_BLK_197.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(198, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(199, 0x0                              , 1, ch);
            // [Rank block 25]
		    dwc_ddrctl_cinit_write_du_cmdbuf(200, MC_DISDQ_RANK_BLK_200.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(201, MC_PAUSEREF_RANK_BLK_201.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(202, MC_DQSOSCSTART_RANK_BLK_202.value, 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(203, MC_PAUSEREF_RANK_BLK_203.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(204, MC_DISDQ_RANK_BLK_204.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(205, MC_IMMSET_RANK_BLK_205.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(206, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(207, 0x0                              , 1, ch);
            // [Rank block 28]
		    dwc_ddrctl_cinit_write_du_cmdbuf(208, MC_IMMCLEAR_RANK_BLK_224.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(209, MC_DISDQ_RANK_BLK_225.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(210, MC_PAUSEREF_RANK_BLK_226.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(211, MC_ZQCALLATCH_RANK_BLK_227.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(212, MC_PAUSEREF_RANK_BLK_228.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(213, MC_DISDQ_RANK_BLK_229.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(214, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(215, 0x0                              , 1, ch);
            // [Rank block 29]
		    dwc_ddrctl_cinit_write_du_cmdbuf(216, MC_IMMCLEAR_RANK_BLK_232.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(217, MC_DISDQ_RANK_BLK_233.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(218, MC_PAUSEREF_RANK_BLK_234.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(219, MC_MRR_RANK_BLK_235.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(220, MC_MRR_RANK_BLK_236.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(221, MC_MRR_RANK_BLK_237.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(222, MC_PAUSEREF_RANK_BLK_238.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(223, MC_DISDQ_RANK_BLK_239.value      , 1, ch);
            // [Rank block 30]
		    dwc_ddrctl_cinit_write_du_cmdbuf(224, MC_DISDQ[3].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(225, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(226, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(227, MC_PRANKPREAB[3].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(228, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(229, MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(230, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(231, MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(232, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(233, MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(234, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(235, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(232, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(233, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(234, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(235, MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(236, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(237, MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(238, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(239, MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(240, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(241, MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(242, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(243, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(236, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(237, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(238, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(239, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(240, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(241, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(242, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(243, MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(244, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(245, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(246, MC_ENDQ[3].value                 , 1, ch);
#endif /*MEMC_NUM_RANKS_GT_2*/
        } else {
            // [Rank block 0]
		    dwc_ddrctl_cinit_write_du_cmdbuf(0  , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(1  , MC_BLOCKREF[0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(2  , MC_ZQCALSTART_RANK_BLK_2.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(3  , MC_RESUMEREF[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(4  , MC_ENDQ[4].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(5  , MC_IMMSET_RANK_BLK_5.value       , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(6  , 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(7  , 0x0                              , 1, ch);
            // [Rank block 1]
		    dwc_ddrctl_cinit_write_du_cmdbuf(8  , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(9  , MC_BLOCKREF[0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(10 , MC_DQSOSCSTART_RANK_BLK_10.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(11 , MC_RESUMEREF[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(12 , MC_ENDQ[4].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(13 , MC_IMMSET_RANK_BLK_13.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(14 , 0x0                              , 1, ch);
            // [Rank block 4]
		    dwc_ddrctl_cinit_write_du_cmdbuf(15 , MC_IMMCLEAR_RANK_BLK_32.value    , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(16 , MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(17 , MC_BLOCKREF[0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(18 , MC_ZQCALLATCH_RANK_BLK_35.value  , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(19 , MC_RESUMEREF[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(20 , MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 5]
		    dwc_ddrctl_cinit_write_du_cmdbuf(21 , MC_IMMCLEAR_RANK_BLK_40.value    , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(22 , MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(23 , MC_BLOCKREF[0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(24 , MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(25 , MC_MRR_RANK_BLK_45.value         , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(26 , MC_MRR46[0][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(27 , MC_MRR47[0][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(28 , MC_IWAITTRKCALCCUR.value         , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(29 , MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(30 , MC_RESUMEREF[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(31 , MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 6]
		    dwc_ddrctl_cinit_write_du_cmdbuf(32 , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(33 , MC_BLOCKREF[0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(34 , MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(35 , MC_PRANKPREAB[0].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(36 , MC_MRW14_1[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(37 , MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(38 , MC_MANUALECS[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(39 , MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(40 , MC_MRW14_1[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(41 , MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(42 , MC_MANUALECS[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(43 , MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(40 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(41 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(42 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(43 , MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(44 , MC_MRW14_1[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(45 , MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(46 , MC_MANUALECS[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(47 , MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(48 , MC_MRW14_1[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(49 , MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(50 , MC_MANUALECS[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(51 , MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(44 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(45 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(46 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(47 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(48 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(49 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(50 , MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(51 , MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(52 , MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(53 , MC_RESUMEREF[0].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(54 , MC_ENDQ[4].value                 , 1, ch);

 #ifdef MEMC_NUM_RANKS_GT_1
            // [Rank block 8]
		    dwc_ddrctl_cinit_write_du_cmdbuf(64 , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(65 , MC_BLOCKREF[1].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(66 , MC_ZQCALSTART_RANK_BLK_66.value  , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(67 , MC_RESUMEREF[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(68 , MC_ENDQ[4].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(69 , MC_IMMSET_RANK_BLK_69.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(70 , 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(71 , 0x0                              , 1, ch);
            // [Rank block 9]
		    dwc_ddrctl_cinit_write_du_cmdbuf(72 , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(73 , MC_BLOCKREF[1].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(74 , MC_DQSOSCSTART_RANK_BLK_74.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(75 , MC_RESUMEREF[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(76 , MC_ENDQ[4].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(77 , MC_IMMSET_RANK_BLK_77.value      , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(78 , 0x0                              , 1, ch);
            // [Rank block 12]
		    dwc_ddrctl_cinit_write_du_cmdbuf(79 , MC_IMMCLEAR_RANK_BLK_96.value    , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(80 , MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(81 , MC_BLOCKREF[1].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(82 , MC_ZQCALLATCH_RANK_BLK_99.value  , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(83 , MC_RESUMEREF[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(84 , MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 13]
		    dwc_ddrctl_cinit_write_du_cmdbuf(85 , MC_IMMCLEAR_RANK_BLK_104.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(86 , MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(87 , MC_BLOCKREF[1].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(88 , MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(89 , MC_MRR_RANK_BLK_109.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(90 , MC_MRR46[1][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(91 , MC_MRR47[1][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(92 , MC_IWAITTRKCALCCUR.value         , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(93 , MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(94 , MC_RESUMEREF[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(95 , MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 14]
		    dwc_ddrctl_cinit_write_du_cmdbuf(96 , MC_DISDQ[4].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(97 , MC_BLOCKREF[1].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(98 , MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(99 , MC_PRANKPREAB[1].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(100, MC_MRW14_1[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(101, MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(102, MC_MANUALECS[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(103, MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(104, MC_MRW14_1[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(105, MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(106, MC_MANUALECS[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(107, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(104, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(105, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(106, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(107, MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(108, MC_MRW14_1[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(109, MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(110, MC_MANUALECS[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(111, MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(112, MC_MRW14_1[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(113, MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(114, MC_MANUALECS[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(115, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(108, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(109, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(110, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(111, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(112, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(113, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(114, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(115, MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(116, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(117, MC_RESUMEREF[1].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(118, MC_ENDQ[4].value                 , 1, ch);
#endif /*MEMC_NUM_RANKS_GT_1*/

#ifdef MEMC_NUM_RANKS_GT_2
            // [Rank block 16]
		    dwc_ddrctl_cinit_write_du_cmdbuf(128, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(129, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(130, MC_ZQCALSTART_RANK_BLK_130.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(131, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(132, MC_ENDQ[5].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(133, MC_IMMSET_RANK_BLK_133.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(134, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(135, 0x0                              , 1, ch);
            // [Rank block 17]
		    dwc_ddrctl_cinit_write_du_cmdbuf(136, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(137, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(138, MC_DQSOSCSTART_RANK_BLK_138.value, 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(139, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(140, MC_ENDQ[5].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(141, MC_IMMSET_RANK_BLK_141.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(142, 0x0                              , 1, ch);
            // [Rank block 20]
		    dwc_ddrctl_cinit_write_du_cmdbuf(143, MC_IMMCLEAR_RANK_BLK_160.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(144, MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(145, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(146, MC_ZQCALLATCH_RANK_BLK_163.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(147, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(148, MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 21]
		    dwc_ddrctl_cinit_write_du_cmdbuf(149, MC_IMMCLEAR_RANK_BLK_168.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(150, MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(151, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(152, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(153, MC_MRR_RANK_BLK_173.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(154, MC_MRR46[2][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(155, MC_MRR47[2][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(156, MC_IWAITTRKCALCCUR.value         , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(157, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(158, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(159, MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 22]
		    dwc_ddrctl_cinit_write_du_cmdbuf(160, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(161, MC_BLOCKREF[2].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(162, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(163, MC_PRANKPREAB[2].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(164, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(165, MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(166, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(167, MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(168, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(169, MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(170, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(171, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(168, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(169, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(170, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(171, MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(172, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(173, MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(174, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(175, MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(176, MC_MRW14_1[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(177, MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(178, MC_MANUALECS[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(179, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(172, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(173, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(174, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(175, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(176, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(177, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(178, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(179, MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(180, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(181, MC_RESUMEREF[2].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(182, MC_ENDQ[5].value                 , 1, ch);

            // [Rank block 24]
		    dwc_ddrctl_cinit_write_du_cmdbuf(192, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(193, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(194, MC_ZQCALSTART_RANK_BLK_194.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(195, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(196, MC_ENDQ[5].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(197, MC_IMMSET_RANK_BLK_197.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(198, 0x0                              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(199, 0x0                              , 1, ch);
            // [Rank block 25]
		    dwc_ddrctl_cinit_write_du_cmdbuf(200, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(201, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(202, MC_DQSOSCSTART_RANK_BLK_202.value, 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(203, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(204, MC_ENDQ[5].value                 , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(205, MC_IMMSET_RANK_BLK_205.value     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(206, 0x0                              , 1, ch);
            // [Rank block 28]
		    dwc_ddrctl_cinit_write_du_cmdbuf(207, MC_IMMCLEAR_RANK_BLK_224.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(208, MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(209, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(210, MC_ZQCALLATCH_RANK_BLK_227.value , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(211, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(212, MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 29]
		    dwc_ddrctl_cinit_write_du_cmdbuf(213, MC_IMMCLEAR_RANK_BLK_232.value   , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(214, MC_DISDQ[6].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(215, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(216, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(217, MC_MRR_RANK_BLK_237.value        , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(218, MC_MRR46[3][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(219, MC_MRR47[3][0].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(220, MC_IWAITTRKCALCCUR.value         , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(221, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(222, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(223, MC_ENDQ[6].value                 , 1, ch);
            // [Rank block 30]
		    dwc_ddrctl_cinit_write_du_cmdbuf(224, MC_DISDQ[5].value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(225, MC_BLOCKREF[3].value             , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(226, MC_LOCKCTRL.value                , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(227, MC_PRANKPREAB[3].value           , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(228, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(229, MC_MRW14_2[0].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(230, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(231, MC_IWAITTECSC.value              , 1, ch);
            if((active_logical_ranks == 1) || (active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(232, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(233, MC_MRW14_2[1].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(234, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(235, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(232, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(233, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(234, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(235, MC_DES.value                     , 1, ch);
            }
            if((active_logical_ranks == 2)) {
		    dwc_ddrctl_cinit_write_du_cmdbuf(236, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(237, MC_MRW14_2[2].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(238, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(239, MC_IWAITTECSC.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(240, MC_MRW14_1[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(241, MC_MRW14_2[3].value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(242, MC_MANUALECS[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(243, MC_IWAITTECSC.value              , 1, ch);
            } else {
		    dwc_ddrctl_cinit_write_du_cmdbuf(236, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(237, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(238, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(239, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(240, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(241, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(242, MC_DES.value                     , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(243, MC_DES.value                     , 1, ch);
            }
		    dwc_ddrctl_cinit_write_du_cmdbuf(244, MC_UNLOCKCTRL.value              , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(245, MC_RESUMEREF[3].value            , 1, ch);
		    dwc_ddrctl_cinit_write_du_cmdbuf(246, MC_ENDQ[5].value                 , 1, ch);
#endif /*MEMC_NUM_RANKS_GT_2*/
        }
    }
#endif // DDRCTL_DDR
	SNPS_TRACE("Leaving");
}

#ifdef DDRCTL_DDR
void dwc_ddrctl_cinit_prgm_gblk_cfgbuf(SubsysHdlr_t *cinit_cfg)
{
	uint32_t active_channels=DWC_DDRCTL_NUM_CHANNEL;
    ddr5_pasdu_thres_t *du_thres;

    du_thres = &(cinit_cfg->ddr5_pasdu_thres);

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    if(REGB_DDRC_CH0.chctl.dual_channel_en==0) {
            active_channels=1;
    }
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH

    SNPS_LOG("ucode: Channels %d", active_channels);

  for (uint32_t ch = 0; ch < active_channels; ch++) {
		SNPS_LOG("DDR util config buffer: channel %d all Rank ZQCAL threshold %d",
				  ch, du_thres->all_rank_zqcal_thres[ch]);
		SNPS_LOG("DDR util config buffer: channel %d all Rank ZQLAT threshold %d",
				  ch, du_thres->all_rank_zqlat_thres[ch]);
		SNPS_LOG("DDR util config buffer: channel %d Control Update           %d",
		          ch, du_thres->ctlupd_thres[ch]);

		dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_GBLK_ZQCAL_START, DWC_DDRCTL_GLOBAL_BLK, 0, 0x6, du_thres->all_rank_zqcal_thres[ch], DWC_DDRCTL_MASTER_BLK, ch);
		dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_GBLK_CTRL_UPD, DWC_DDRCTL_GLOBAL_BLK, 0x8, 0, du_thres->ctlupd_thres[ch], DWC_DDRCTL_MASTER_BLK, ch);
		dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_GBLK_ZQCAL_LATCH, DWC_DDRCTL_GLOBAL_BLK, 0x10, 0x7, du_thres->all_rank_zqlat_thres[ch], DWC_DDRCTL_SLAVE_BLK, ch);
		dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_GBLK_SWFFC, DWC_DDRCTL_GLOBAL_BLK, 0x20, 0x3d, 0, DWC_DDRCTL_MASTER_BLK, ch);
	}

	SNPS_TRACE("Leaving");
}

void dwc_ddrctl_cinit_prgm_rank_blk_cfgbuf(SubsysHdlr_t *cinit_cfg)
{
    SNPS_TRACE("Entering");
    uint32_t dimm_type;
    uint32_t active_channels=DWC_DDRCTL_NUM_CHANNEL;
    ddr5_pasdu_thres_t *du_thres;

    dimm_type = cinit_cfg->spdData_m.module_type;

    du_thres = &(cinit_cfg->ddr5_pasdu_thres);

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    if(REGB_DDRC_CH0.chctl.dual_channel_en==0) {
            active_channels=1;
    }
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH

    SNPS_LOG("ucode: Channels %d DIMM %d", active_channels, dimm_type);

  for (uint32_t ch = 0; ch < active_channels; ch++) {
		for (uint32_t rank = 0; rank < MEMC_NUM_RANKS; rank++) {

			SNPS_LOG("DDR util config buffer: channel %d Rank %d ZQCAL threshold   %d",
					  ch, rank, du_thres->per_rank_zqcal_thres[ch][rank]);
			SNPS_LOG("DDR util config buffer: channel %d Rank %d ZQLAT threshold   %d",
					  ch, rank, du_thres->per_rank_zqlat_thres[ch][rank]);
			SNPS_LOG("DDR util config buffer: channel %d Rank %d DQS OSC threshold %d",
					  ch, rank, du_thres->dqsosc_thres[ch][rank]);
			// Temperature-Controlled Refresh Mode Register Read
			SNPS_LOG("DDR util config buffer: channel %d Rank %d TCR MRR threshold %d",
			          ch, rank, du_thres->tcr_mrr_thres[ch][rank]);
			// Error check and scrub threshold
			SNPS_LOG("DDR util config buffer: channel %d Rank %d ECS threshold     %d",
					  ch, rank, du_thres->ecs_thres[ch][rank]);

			switch (rank) {
			case 0:
				if (dimm_type != DWC_LRDIMM) {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x8, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0x10, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x18, 0x7, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0x20, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				} else {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x8, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0xf, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x15, 0xa, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK0_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0x20, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				}
				break;
			case 1:
				if (dimm_type != DWC_LRDIMM) {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0x40, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x48, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0x50, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x58, 0x7, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0x60, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				} else {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0x40, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x48, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0x4f, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x55, 0xa, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK1_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0x60, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				}
				break;
			case 2:
				if (dimm_type != DWC_LRDIMM) {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0x80, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x88, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0x90, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x98, 0x7, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0xa0, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				} else {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0x80, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0x88, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0x8f, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0x95, 0xa, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK2_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0xa0, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				}
				break;
			case 3:
				if (dimm_type != DWC_LRDIMM) {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0xc0, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0xc8, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0xd0, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0xd8, 0x7, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0xe0, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				} else {
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK0_ZQCAL_START, DWC_DDRCTL_RANK_BLK, 0xc0, 0x4, du_thres->per_rank_zqcal_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK1_DQSOSC_START, DWC_DDRCTL_RANK_BLK, 0xc8, 0x4, du_thres->dqsosc_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK4_ZQCAL_LATCH, DWC_DDRCTL_RANK_BLK, 0xcf, 0x5, du_thres->per_rank_zqlat_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK5_TCR_MRR, DWC_DDRCTL_RANK_BLK, 0xd5, 0xa, du_thres->tcr_mrr_thres[ch][rank], DWC_DDRCTL_SLAVE_BLK, ch);
					dwc_ddrctl_cinit_write_du_cfgbuf(DWC_DDRCTL_RANK3_BLK6_MANUAL_ECS, DWC_DDRCTL_RANK_BLK, 0xe0, 0x16, du_thres->ecs_thres[ch][rank], DWC_DDRCTL_MASTER_BLK, ch);
				}
				break;
			}
		}
	}

	SNPS_TRACE("Leaving");
}
#endif /* DDRCTL_DDR */

/** @brief method to program DDR5 microcode to support CA parity retry
 */
void dwc_ddrctl_cinit_prgm_ucode_load_capar(SubsysHdlr_t *cinit_cfg)
{
	SNPS_TRACE("Entering");
#ifdef DDRCTL_DDR
    uint32_t active_ranks;
    uint32_t active_channels=DWC_DDRCTL_NUM_CHANNEL;

#ifdef MEMC_NUM_RANKS_GT_1
    active_ranks = cinit_cfg->memCtrlr_m.static_cfg.active_ranks;
#else /* MEMC_NUM_RANKS_GT_1 */
    active_ranks = 1;
#endif /* MEMC_NUM_RANKS_GT_1 */

#ifdef DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH
    if(REGB_DDRC_CH0.chctl.dual_channel_en==0) {
        active_channels=1;
    }
#endif // DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH

    SNPS_LOG("ucode: Channels %d, Ranks %d", active_channels, active_ranks);
	MPC_UCODE_t MC_ZQCALSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALSTART[i].cmd_code = MPC_CMD;
		MC_ZQCALSTART[i].last_cmd = 1;
		MC_ZQCALSTART[i].op = 5; // OP (ZQCal Start)
	}
	MC_ZQCALSTART[0].csn_sel = RANK0_SEL;
	MC_ZQCALSTART[1].csn_sel = RANK1_SEL;
	MC_ZQCALSTART[2].csn_sel = RANK2_SEL;
	MC_ZQCALSTART[3].csn_sel = RANK3_SEL;
	MC_ZQCALSTART[4].csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_ZQCALLATCH[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ZQCALLATCH[i].cmd_code = MPC_CMD;
		MC_ZQCALLATCH[i].last_cmd = 0;
		MC_ZQCALLATCH[i].op = 4; // OP (ZQCal Latch)
	}
	MC_ZQCALLATCH[0].csn_sel = RANK0_SEL;
	MC_ZQCALLATCH[1].csn_sel = RANK1_SEL;
	MC_ZQCALLATCH[2].csn_sel = RANK2_SEL;
	MC_ZQCALLATCH[3].csn_sel = RANK3_SEL;
	MC_ZQCALLATCH[4].csn_sel = RANK_R15_SEL;

	MPC_UCODE_t MC_DQSOSCSTART[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_DQSOSCSTART[i].cmd_code = MPC_CMD;
		MC_DQSOSCSTART[i].last_cmd = 1;
		MC_DQSOSCSTART[i].op = 7; // OP (DQS OSC Start)
	}
	MC_DQSOSCSTART[0].csn_sel = RANK0_SEL;
	MC_DQSOSCSTART[1].csn_sel = RANK1_SEL;
	MC_DQSOSCSTART[2].csn_sel = RANK2_SEL;
	MC_DQSOSCSTART[3].csn_sel = RANK3_SEL;
	MC_DQSOSCSTART[4].csn_sel = RANK_R15_SEL;

	MRR_UCODE_t MC_MRR[4][48];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 46; j < 48; j++) {
			MC_MRR[i][j].cmd_code = MRR_CMD;
			MC_MRR[i][j].prank_num = i;
			MC_MRR[i][j].phy_snoop_en = 1;
			MC_MRR[i][j].prank_sel = 0;
			MC_MRR[i][j].last_cmd = 1;
			MC_MRR[i][j].mra = j;
		}
	}

	SRE_UCODE_t MC_SRE[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRE[i].cmd_code = SRE_CMD;
		MC_SRE[i].last_cmd = 1;
		MC_SRE[i].freq_change = 0;
		MC_SRE[i].wait_type = 1;
		MC_SRE[i].wait_reg = 0; //tCPDED
	}

	MC_SRE[0].csn_sel = RANK0_SEL;
	MC_SRE[1].csn_sel = RANK1_SEL;
	MC_SRE[2].csn_sel = RANK2_SEL;
	MC_SRE[3].csn_sel = RANK3_SEL;
	MC_SRE[4].csn_sel = RANK0_1_SEL;
	MC_SRE[5].csn_sel = RANK2_3_SEL;
	MC_SRE[6].csn_sel = RANK_ALL_SEL;
	MC_SRE[7].csn_sel = RANK_R15_SEL;

	SRX_UCODE_t MC_SRX[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRX[i].cmd_code = SRX_CMD;
		MC_SRX[i].last_cmd = 1;
		MC_SRX[i].wait_type = 1;
		MC_SRX[i].wait_reg = 5; //tXS
	}

	MC_SRX[0].csn_sel = RANK0_SEL;
	MC_SRX[1].csn_sel = RANK1_SEL;
	MC_SRX[2].csn_sel = RANK2_SEL;
	MC_SRX[3].csn_sel = RANK3_SEL;
	MC_SRX[4].csn_sel = RANK0_1_SEL;
	MC_SRX[5].csn_sel = RANK2_3_SEL;
	MC_SRX[6].csn_sel = RANK_ALL_SEL;
	MC_SRX[7].csn_sel = RANK_R15_SEL;

	PDE_UCODE_t MC_PDE[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDE[i].cmd_code = PDE_CMD;
		MC_PDE[i].last_cmd = 1;
		MC_PDE[i].wait_type = 1;
		MC_PDE[i].wait_cycle = 0; //tCPDED
	}

	MC_PDE[0].csn_sel = RANK0_SEL;
	MC_PDE[1].csn_sel = RANK1_SEL;
	MC_PDE[2].csn_sel = RANK2_SEL;
	MC_PDE[3].csn_sel = RANK3_SEL;
	MC_PDE[4].csn_sel = RANK_R15_SEL;

	PDX_UCODE_t MC_PDX[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDX[i].cmd_code = PDX_CMD;
		MC_PDX[i].last_cmd = 1;
		MC_PDX[i].wait_type = 1;
		MC_PDX[i].wait_reg = 4; //tXP
	}

	MC_PDX[0].csn_sel = RANK0_SEL;
	MC_PDX[1].csn_sel = RANK1_SEL;
	MC_PDX[2].csn_sel = RANK2_SEL;
	MC_PDX[3].csn_sel = RANK3_SEL;
	MC_PDX[4].csn_sel = RANK_R15_SEL;

	NOP_UCODE_t MC_NOP[8][2];

	for (uint32_t i = 0; i < 8; i++) {
		for (uint32_t j = 0; j < 2; j++) {
			MC_NOP[i][j].cmd_code = NOP_CMD;
			MC_NOP[i][j].last_cmd = 1;
			MC_NOP[i][j]._RESERVED = 0;
			MC_NOP[i][j].nop_len = j;
		}
	}

	for (uint32_t i = 0; i < 2; i++) {
		MC_NOP[0][i].csn_sel = RANK0_SEL;
		MC_NOP[1][i].csn_sel = RANK1_SEL;
		MC_NOP[2][i].csn_sel = RANK2_SEL;
		MC_NOP[3][i].csn_sel = RANK3_SEL;
		MC_NOP[4][i].csn_sel = RANK0_1_SEL;
		MC_NOP[5][i].csn_sel = RANK2_3_SEL;
		MC_NOP[6][i].csn_sel = RANK_ALL_SEL;
		MC_NOP[7][i].csn_sel = RANK_R15_SEL;
	}

	DES_UCODE_t MC_DES;

	MC_DES.cmd_code = DES_CMD;
	MC_DES.last_cmd = 1;
	MC_DES.unit_sel = 0;
	MC_DES.unit_count = 1;

	IWAIT_REG_UCODE_t MC_IWAITCAPARRETRYWINDOW;

	MC_IWAITCAPARRETRYWINDOW.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITCAPARRETRYWINDOW.wait_type = 1;
	MC_IWAITCAPARRETRYWINDOW._RESERVED = 0;
	MC_IWAITCAPARRETRYWINDOW.wait_reg = 13;

	IWAIT_REG_UCODE_t MC_IWAITTSTAB;

	MC_IWAITTSTAB.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTSTAB.wait_type = 1;
	MC_IWAITTSTAB._RESERVED = 0;
	MC_IWAITTSTAB.wait_reg = 12;

	IWAIT_REG_UCODE_t MC_IWAITTSRFEXITSTAGGER;

	MC_IWAITTSRFEXITSTAGGER.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTSRFEXITSTAGGER.wait_type = 1;
	MC_IWAITTSRFEXITSTAGGER._RESERVED = 0;
	MC_IWAITTSRFEXITSTAGGER.wait_reg = 11;

	IWAIT_REG_UCODE_t MC_IWAITTCSSR;

	MC_IWAITTCSSR.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTCSSR.wait_type = 1;
	MC_IWAITTCSSR._RESERVED = 0;
	MC_IWAITTCSSR.wait_reg = 10;

	IWAIT_REG_UCODE_t MC_IWAITTCPDED2SRX;

	MC_IWAITTCPDED2SRX.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTCPDED2SRX.wait_type = 1;
	MC_IWAITTCPDED2SRX._RESERVED = 0;
	MC_IWAITTCPDED2SRX.wait_reg = 9;

	IWAIT_REG_UCODE_t MC_IWAITTZQLAT;

	MC_IWAITTZQLAT.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQLAT.wait_type = 1;
	MC_IWAITTZQLAT._RESERVED = 0;
	MC_IWAITTZQLAT.wait_reg = 8;

	IWAIT_REG_UCODE_t MC_IWAITTZQCAL;

	MC_IWAITTZQCAL.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTZQCAL.wait_type = 1;
	MC_IWAITTZQCAL._RESERVED = 0;
	MC_IWAITTZQCAL.wait_reg = 7;

	IWAIT_REG_UCODE_t MC_IWAITTXP;

	MC_IWAITTXP.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTXP.wait_type = 1;
	MC_IWAITTXP._RESERVED = 0;
	MC_IWAITTXP.wait_reg = 4; //tXP

	IWAIT_REG_UCODE_t MC_IWAITTRFC;

	MC_IWAITTRFC.cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTRFC.wait_type = 1;
	MC_IWAITTRFC._RESERVED = 0;
	MC_IWAITTRFC.wait_reg = 1; //tRFC

	IWAIT_TIME_UCODE_t MC_IWAITTIME[2];

	MC_IWAITTIME[0].cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTIME[0].wait_type = 0;
	MC_IWAITTIME[0].wait_unit = 0;
	MC_IWAITTIME[0].wait_time = 0;
	MC_IWAITTIME[1].cmd_code = IWAIT_TIME_CMD;
	MC_IWAITTIME[1].wait_type = 0;
	MC_IWAITTIME[1].wait_unit = 0;
	MC_IWAITTIME[1].wait_time = 1;

	IWAIT_SIG_UCODE_t MC_IWAITTXSDLLACK;

	MC_IWAITTXSDLLACK.cmd_code = IWAIT_SIG_CMD;
	MC_IWAITTXSDLLACK.sig_value = 1;
	MC_IWAITTXSDLLACK.sig_sel = 1;
	MC_IWAITTXSDLLACK.wait_cycle = 0;

	MOV_UCODE_t MC_MOVCSn2R15;

	MC_MOVCSn2R15.cmd_code = MOV_CMD;
	MC_MOVCSn2R15.mov_dir = 1;
	MC_MOVCSn2R15.mov_type = 0;
	MC_MOVCSn2R15._RESERVED = 0;
	MC_MOVCSn2R15.reg_num = 15;

	MOV_UCODE_t MC_MOVCSn2R0[2];

	MC_MOVCSn2R0[0].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[0].mov_dir = 0;
	MC_MOVCSn2R0[0].mov_type = 1;
	MC_MOVCSn2R0[0]._RESERVED = 0;
	MC_MOVCSn2R0[0].reg_num = 0;
	MC_MOVCSn2R0[1].cmd_code = MOV_CMD;
	MC_MOVCSn2R0[1].mov_dir = 0;
	MC_MOVCSn2R0[1].mov_type = 1;
	MC_MOVCSn2R0[1]._RESERVED = 0;
	MC_MOVCSn2R0[1].reg_num = 1;

	IMM_BIT_UCODE_t MC_STORETXSDLLSTART;

	MC_STORETXSDLLSTART.cmd_code = IMM_BIT_CMD;
	MC_STORETXSDLLSTART.imm_type = 0;
	MC_STORETXSDLLSTART._RESERVED = 0;
	MC_STORETXSDLLSTART.reg_sel = 3;
	MC_STORETXSDLLSTART.bit_loc = 3;
	MC_STORETXSDLLSTART.bit_val = 1;

	IMM_BIT_UCODE_t MC_CLEARTXSDLLSTART;

	MC_CLEARTXSDLLSTART.cmd_code = IMM_BIT_CMD;
	MC_CLEARTXSDLLSTART.imm_type = 0;
	MC_CLEARTXSDLLSTART._RESERVED = 0;
	MC_CLEARTXSDLLSTART.reg_sel = 3;
	MC_CLEARTXSDLLSTART.bit_loc = 3;
	MC_CLEARTXSDLLSTART.bit_val = 0;

	DISDQ_UCODE_t MC_DISDQ[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_DISDQ[i].cmd_code = DISDQ_CMD;
		MC_DISDQ[i].last_cmd = 1;
		MC_DISDQ[i]._RESERVED = 0;
		MC_DISDQ[i].disdqset = 1;
		MC_DISDQ[i].disdqreset = 0;
	}

	MC_DISDQ[0].csn_sel = RANK0_SEL;
	MC_DISDQ[1].csn_sel = RANK1_SEL;
	MC_DISDQ[2].csn_sel = RANK2_SEL;
	MC_DISDQ[3].csn_sel = RANK3_SEL;
	MC_DISDQ[4].csn_sel = RANK_R15_SEL;

	DISDQ_UCODE_t MC_ENDQ[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_ENDQ[i].cmd_code = DISDQ_CMD;
		MC_ENDQ[i].last_cmd = 1;
		MC_ENDQ[i]._RESERVED = 0;
		MC_ENDQ[i].disdqset = 0;
		MC_ENDQ[i].disdqreset = 1;
	}

	MC_ENDQ[0].csn_sel = RANK0_SEL;
	MC_ENDQ[1].csn_sel = RANK1_SEL;
	MC_ENDQ[2].csn_sel = RANK2_SEL;
	MC_ENDQ[3].csn_sel = RANK3_SEL;
	MC_ENDQ[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_PAUSEREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PAUSEREF[i].cmd_code = PAUSEREF_CMD;
		MC_PAUSEREF[i].last_cmd = 1;
		MC_PAUSEREF[i]._RESERVED = 0;
		MC_PAUSEREF[i].pausereftype = 0;
		MC_PAUSEREF[i].pauserefset = 1;
		MC_PAUSEREF[i].pauserefreset = 0;
	}

	MC_PAUSEREF[0].csn_sel = RANK0_SEL;
	MC_PAUSEREF[1].csn_sel = RANK1_SEL;
	MC_PAUSEREF[2].csn_sel = RANK2_SEL;
	MC_PAUSEREF[3].csn_sel = RANK3_SEL;
	MC_PAUSEREF[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_BLOCKREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_BLOCKREF[i].cmd_code = PAUSEREF_CMD;
		MC_BLOCKREF[i].last_cmd = 1;
		MC_BLOCKREF[i]._RESERVED = 0;
		MC_BLOCKREF[i].pausereftype = 1;
		MC_BLOCKREF[i].pauserefset = 1;
		MC_BLOCKREF[i].pauserefreset = 0;
	}

	MC_BLOCKREF[0].csn_sel = RANK0_SEL;
	MC_BLOCKREF[1].csn_sel = RANK1_SEL;
	MC_BLOCKREF[2].csn_sel = RANK2_SEL;
	MC_BLOCKREF[3].csn_sel = RANK3_SEL;
	MC_BLOCKREF[4].csn_sel = RANK_R15_SEL;

	PAUSEREF_UCODE_t MC_RESUMEREF[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_RESUMEREF[i].cmd_code = PAUSEREF_CMD;
		MC_RESUMEREF[i].last_cmd = 1;
		MC_RESUMEREF[i]._RESERVED = 0;
		MC_RESUMEREF[i].pausereftype = 0;
		MC_RESUMEREF[i].pauserefset = 0;
		MC_RESUMEREF[i].pauserefreset = 1;
	}

	MC_RESUMEREF[0].csn_sel = RANK0_SEL;
	MC_RESUMEREF[1].csn_sel = RANK1_SEL;
	MC_RESUMEREF[2].csn_sel = RANK2_SEL;
	MC_RESUMEREF[3].csn_sel = RANK3_SEL;
	MC_RESUMEREF[4].csn_sel = RANK_R15_SEL;

	SRX_DONE_UCODE_t MC_SRXDONETXSDLL[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRXDONETXSDLL[i].cmd_code = SRX_DONE_CMD;
		MC_SRXDONETXSDLL[i].last_cmd = 1;
		MC_SRXDONETXSDLL[i]._RESERVED = 0;
		MC_SRXDONETXSDLL[i].srx_done_txsdll = 1;
		MC_SRXDONETXSDLL[i].srx_done_txs = 0;
	}

	MC_SRXDONETXSDLL[0].csn_sel = RANK0_SEL;
	MC_SRXDONETXSDLL[1].csn_sel = RANK1_SEL;
	MC_SRXDONETXSDLL[2].csn_sel = RANK2_SEL;
	MC_SRXDONETXSDLL[3].csn_sel = RANK3_SEL;
	MC_SRXDONETXSDLL[4].csn_sel = RANK0_1_SEL;
	MC_SRXDONETXSDLL[5].csn_sel = RANK2_3_SEL;
	MC_SRXDONETXSDLL[6].csn_sel = RANK_ALL_SEL;
	MC_SRXDONETXSDLL[7].csn_sel = RANK_R15_SEL;

	SRX_DONE_UCODE_t MC_SRXDONETXS[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_SRXDONETXS[i].cmd_code = SRX_DONE_CMD;
		MC_SRXDONETXS[i].last_cmd = 1;
		MC_SRXDONETXS[i]._RESERVED = 0;
		MC_SRXDONETXS[i].srx_done_txsdll = 0;
		MC_SRXDONETXS[i].srx_done_txs = 1;
	}

	MC_SRXDONETXS[0].csn_sel = RANK0_SEL;
	MC_SRXDONETXS[1].csn_sel = RANK1_SEL;
	MC_SRXDONETXS[2].csn_sel = RANK2_SEL;
	MC_SRXDONETXS[3].csn_sel = RANK3_SEL;
	MC_SRXDONETXS[4].csn_sel = RANK0_1_SEL;
	MC_SRXDONETXS[5].csn_sel = RANK2_3_SEL;
	MC_SRXDONETXS[6].csn_sel = RANK_ALL_SEL;
	MC_SRXDONETXS[7].csn_sel = RANK_R15_SEL;

	PDX_MPSMX_DONE_UCODE_t MC_PDXDONE[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PDXDONE[i].cmd_code = PDX_MPSMX_DONE_CMD;
		MC_PDXDONE[i].last_cmd = 1;
		MC_PDXDONE[i]._RESERVED = 0;
		MC_PDXDONE[i].mpsmx_done = 0;
		MC_PDXDONE[i].pdx_done = 1;
	}

	MC_PDXDONE[0].csn_sel = RANK0_SEL;
	MC_PDXDONE[1].csn_sel = RANK1_SEL;
	MC_PDXDONE[2].csn_sel = RANK2_SEL;
	MC_PDXDONE[3].csn_sel = RANK3_SEL;
	MC_PDXDONE[4].csn_sel = RANK_R15_SEL;

	CTRLUPD_UCODE_t MC_CTRLUPD;

	MC_CTRLUPD.cmd_code = CTRLUPD_CMD;
	MC_CTRLUPD.last_cmd = 1;
	MC_CTRLUPD.dfi_ctrlupd_req_set = 1;
	MC_CTRLUPD.dfi_ctrlupd_retry_en = 0;
	MC_CTRLUPD.wait_unit = 0;
	MC_CTRLUPD.wait_time = 0;

	DFILP_UCODE_t MC_DFILPE;

	MC_DFILPE.cmd_code = DFILP_CMD;
	MC_DFILPE.last_cmd = 1;
	MC_DFILPE.dfi_lp_data_req_set = 1;
	MC_DFILPE.dfi_lp_data_req_clr = 0;
	MC_DFILPE.dfi_lp_ctrl_req_set = 1;
	MC_DFILPE.dfi_lp_ctrl_req_clr = 0;
	MC_DFILPE.wakeup_type = 1;
	MC_DFILPE.wait_time = 0;

	DFILP_UCODE_t MC_DFILPX;

	MC_DFILPX.cmd_code = DFILP_CMD;
	MC_DFILPX.last_cmd = 1;
	MC_DFILPX.dfi_lp_data_req_set = 0;
	MC_DFILPX.dfi_lp_data_req_clr = 1;
	MC_DFILPX.dfi_lp_ctrl_req_set = 0;
	MC_DFILPX.dfi_lp_ctrl_req_clr = 1;
	MC_DFILPX.wakeup_type = 1;
	MC_DFILPX.wait_time = 0;

	PRANK_PREAB_UCODE_t MC_PRANKPREAB[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PRANKPREAB[i].cmd_code = PRANK_PREAB_CMD;
		MC_PRANKPREAB[i].last_cmd = 1;
		MC_PRANKPREAB[i]._RESERVED = 0;
		MC_PRANKPREAB[i].wait_type = 1;
		MC_PRANKPREAB[i].wait_reg = 3; //tRP
	}

	MC_PRANKPREAB[0].csn_sel = RANK0_SEL;
	MC_PRANKPREAB[1].csn_sel = RANK1_SEL;
	MC_PRANKPREAB[2].csn_sel = RANK2_SEL;
	MC_PRANKPREAB[3].csn_sel = RANK3_SEL;
	MC_PRANKPREAB[4].csn_sel = RANK_R15_SEL;

	PRANK_REFAB_UCODE_t MC_PRANKREFAB[5];

	for (uint32_t i = 0; i < 5; i++) {
		MC_PRANKREFAB[i].cmd_code = PRANK_REFAB_CMD;
		MC_PRANKREFAB[i].last_cmd = 1;
		MC_PRANKREFAB[i]._RESERVED = 0;
		MC_PRANKREFAB[i].wait_type = 1;
		MC_PRANKREFAB[i].wait_reg = 2; //tRFC_DLR
	}

	MC_PRANKREFAB[0].csn_sel = RANK0_SEL;
	MC_PRANKREFAB[1].csn_sel = RANK1_SEL;
	MC_PRANKREFAB[2].csn_sel = RANK2_SEL;
	MC_PRANKREFAB[3].csn_sel = RANK3_SEL;
	MC_PRANKREFAB[4].csn_sel = RANK_R15_SEL;

	FORCE_CS_UCODE_t MC_FORCECSX[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_FORCECSX[i].cmd_code = FORCE_CS_CMD;
		MC_FORCECSX[i].last_cmd = 1;
		MC_FORCECSX[i]._RESERVED = 0;
		MC_FORCECSX[i].force_csx = 1;
		MC_FORCECSX[i].force_cse = 0;
	}

	MC_FORCECSX[0].csn_sel = RANK0_SEL;
	MC_FORCECSX[1].csn_sel = RANK1_SEL;
	MC_FORCECSX[2].csn_sel = RANK2_SEL;
	MC_FORCECSX[3].csn_sel = RANK3_SEL;
	MC_FORCECSX[4].csn_sel = RANK0_1_SEL;
	MC_FORCECSX[5].csn_sel = RANK2_3_SEL;
	MC_FORCECSX[6].csn_sel = RANK_ALL_SEL;
	MC_FORCECSX[7].csn_sel = RANK_R15_SEL;

	FORCE_CS_UCODE_t MC_FORCECSE[8];

	for (uint32_t i = 0; i < 8; i++) {
		MC_FORCECSE[i].cmd_code = FORCE_CS_CMD;
		MC_FORCECSE[i].last_cmd = 1;
		MC_FORCECSE[i]._RESERVED = 0;
		MC_FORCECSE[i].force_csx = 0;
		MC_FORCECSE[i].force_cse = 1;
	}

	MC_FORCECSE[0].csn_sel = RANK0_SEL;
	MC_FORCECSE[1].csn_sel = RANK1_SEL;
	MC_FORCECSE[2].csn_sel = RANK2_SEL;
	MC_FORCECSE[3].csn_sel = RANK3_SEL;
	MC_FORCECSE[4].csn_sel = RANK0_1_SEL;
	MC_FORCECSE[5].csn_sel = RANK2_3_SEL;
	MC_FORCECSE[6].csn_sel = RANK_ALL_SEL;
	MC_FORCECSE[7].csn_sel = RANK_R15_SEL;

	LOCK_CTRL_UCODE_t MC_UNLOCKCTRL;

	MC_UNLOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_UNLOCKCTRL._RESERVED = 0;
	MC_UNLOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_UNLOCKCTRL.reset_urgent_flag = 0;
	MC_UNLOCKCTRL.set_urgent_flag = 0;
	MC_UNLOCKCTRL.unlock_ci_bus = 1;
	MC_UNLOCKCTRL.lock_ci_bus = 0;

	LOCK_CTRL_UCODE_t MC_LOCKCTRL;

	MC_LOCKCTRL.cmd_code = LOCK_CTRL_CMD;
	MC_LOCKCTRL._RESERVED = 0;
	MC_LOCKCTRL.reset_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.set_ucode_seq_ongoing_flag = 0;
	MC_LOCKCTRL.reset_urgent_flag = 0;
	MC_LOCKCTRL.set_urgent_flag = 0;
	MC_LOCKCTRL.unlock_ci_bus = 0;
	MC_LOCKCTRL.lock_ci_bus = 1;

	DFICLK_UCODE_t MC_DFICLKENCTRL;

	MC_DFICLKENCTRL.cmd_code = DFI_CLK_CMD;
	MC_DFICLKENCTRL.last_cmd = 1;
	MC_DFICLKENCTRL.csn_sel = RANK_ALL_SEL;
	MC_DFICLKENCTRL._RESERVED = 0;
	MC_DFICLKENCTRL.dfi_ck_disable_clear = 1;
	MC_DFICLKENCTRL.dfi_ck_disable_set = 0;

	DFICLK_UCODE_t MC_DFICLKDISCTRL;

	MC_DFICLKDISCTRL.cmd_code = DFI_CLK_CMD;
	MC_DFICLKDISCTRL.last_cmd = 1;
	MC_DFICLKDISCTRL.csn_sel = RANK_ALL_SEL;
	MC_DFICLKDISCTRL._RESERVED = 0;
	MC_DFICLKDISCTRL.dfi_ck_disable_clear = 0;
	MC_DFICLKDISCTRL.dfi_ck_disable_set = 1;

	NTODT_CTRL_UCODE_t MC_NTODTENCTRL[4];

	for (uint32_t i = 0; i < 4; i++) {
		MC_NTODTENCTRL[i].cmd_code = NTODT_CTRL_CMD;
		MC_NTODTENCTRL[i].last_cmd = 1;
		MC_NTODTENCTRL[i]._RESERVED = 0;
		MC_NTODTENCTRL[i].ntodt_dis_ctrl = 0;
		MC_NTODTENCTRL[i].ntodt_en_ctrl = 1;
	}

	MC_NTODTENCTRL[0].csn_sel = RANK0_SEL;
	MC_NTODTENCTRL[1].csn_sel = RANK1_SEL;
	MC_NTODTENCTRL[2].csn_sel = RANK2_SEL;
	MC_NTODTENCTRL[3].csn_sel = RANK3_SEL;

	JPC_UCODE_t MC_JPC4ISSELFREF[3];

	MC_JPC4ISSELFREF[1].cmd_code = JPC_CMD;
	MC_JPC4ISSELFREF[1].sig_value = 1;
	MC_JPC4ISSELFREF[1].sig_sel = 16;
	MC_JPC4ISSELFREF[1].jmp_dir = 0;
	MC_JPC4ISSELFREF[1].jmp_step = 4;
	MC_JPC4ISSELFREF[2].cmd_code = JPC_CMD;
	MC_JPC4ISSELFREF[2].sig_value = 1;
	MC_JPC4ISSELFREF[2].sig_sel = 17;
	MC_JPC4ISSELFREF[2].jmp_dir = 0;
	MC_JPC4ISSELFREF[2].jmp_step = 17;

	JPC_UCODE_t MC_JPC4MPSMRETRYRDIMM[24];

	for (uint32_t i = 1; i < 24; i++) {
		MC_JPC4MPSMRETRYRDIMM[i].cmd_code = JPC_CMD;
		MC_JPC4MPSMRETRYRDIMM[i].sig_value = 1;
		MC_JPC4MPSMRETRYRDIMM[i].sig_sel = 4;
		MC_JPC4MPSMRETRYRDIMM[i].jmp_dir = 0;
		MC_JPC4MPSMRETRYRDIMM[i].jmp_step = i;
	}

	JPC_UCODE_t MC_JPC4AR[4][6];

	for (uint32_t i = 0; i < 4; i++) {
		for (uint32_t j = 1; j < 6; j++) {
			MC_JPC4AR[i][j].cmd_code = JPC_CMD;
			MC_JPC4AR[i][j].sig_value = 1;
			MC_JPC4AR[i][j].sig_sel = i + 4;
			MC_JPC4AR[i][j].jmp_dir = 0;
			MC_JPC4AR[i][j].jmp_step = j;
		}
	}

	SNPS_TRACE("Entering");

    // [Channel 0 & 1 Powerdown]
    for (uint32_t ch = 0; ch < active_channels; ch++) {
        dwc_ddrctl_cinit_write_capar_cmdbuf(0  , MC_DFILPX.value                , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(1  , MC_MOVCSn2R0[1].value          , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(2  , MC_MOVCSn2R15.value            , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(3  , MC_JPC4ISSELFREF[2].value      , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(4  , MC_JPC4ISSELFREF[1].value      , ch);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_capar_cmdbuf(5  , MC_NOP[4][0].value             , ch);
        } else {
        dwc_ddrctl_cinit_write_capar_cmdbuf(5  , MC_NOP[6][0].value             , ch);
        }
        dwc_ddrctl_cinit_write_capar_cmdbuf(6  , MC_IWAITTCPDED2SRX.value       , ch);
        if((active_ranks == 1) || (active_ranks == 3)) {
        dwc_ddrctl_cinit_write_capar_cmdbuf(7  , MC_SRX[4].value                , ch);
        } else {
        dwc_ddrctl_cinit_write_capar_cmdbuf(7  , MC_SRX[6].value                , ch);
        }
        dwc_ddrctl_cinit_write_capar_cmdbuf(8  , MC_SRXDONETXS[6].value         , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(9  , MC_STORETXSDLLSTART.value      , ch);
        dwc_ddrctl_cinit_write_capar_cmdbuf(10 , MC_JPC4MPSMRETRYRDIMM[7].value , ch);
#ifdef UMCTL2_CID_EN
		dwc_ddrctl_cinit_write_capar_cmdbuf(11, MC_JPC4AR[3][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(12, MC_PRANKREFAB[3].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(13, MC_JPC4AR[2][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(14, MC_PRANKREFAB[2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(15, MC_JPC4AR[1][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(16, MC_PRANKREFAB[1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(17, MC_PRANKREFAB[0].value, ch);
#else /* UMCTL2_CID_EN */
		dwc_ddrctl_cinit_write_capar_cmdbuf(11, MC_PRANKREFAB[4].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(12, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(13, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(14, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(15, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(16, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(17, MC_IWAITTIME[0].value, ch);
#endif /* UMCTL2_CID_EN */
		dwc_ddrctl_cinit_write_capar_cmdbuf(18 , MC_IWAITTXSDLLACK.value        , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(19 , MC_CLEARTXSDLLSTART.value      , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(20 , MC_SRXDONETXSDLL[6].value      , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(21 , MC_JPC4MPSMRETRYRDIMM[22].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(22 , MC_IWAITTRFC.value             , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(23 , MC_NOP[7][0].value             , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(24 , MC_IWAITTXP.value              , ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(25 , MC_PDXDONE[4].value            , ch);
#ifdef UMCTL2_CID_EN
		dwc_ddrctl_cinit_write_capar_cmdbuf(26, MC_JPC4AR[3][2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(27, MC_PRANKPREAB[3].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(28, MC_PRANKREFAB[3].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(29, MC_JPC4AR[2][2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(30, MC_PRANKPREAB[2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(31, MC_PRANKREFAB[2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(32, MC_JPC4AR[1][2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(33, MC_PRANKPREAB[1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(34, MC_PRANKREFAB[1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(35, MC_PRANKPREAB[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(36, MC_PRANKREFAB[0].value, ch);
#else /* UMCTL2_CID_EN */
		dwc_ddrctl_cinit_write_capar_cmdbuf(26, MC_JPC4AR[3][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(27, MC_PRANKPREAB[3].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(28, MC_JPC4AR[2][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(29, MC_PRANKPREAB[2].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(30, MC_JPC4AR[1][1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(31, MC_PRANKPREAB[1].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(32, MC_PRANKPREAB[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(33, MC_PRANKREFAB[4].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(34, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(35, MC_IWAITTIME[0].value, ch);
		dwc_ddrctl_cinit_write_capar_cmdbuf(36, MC_IWAITTIME[0].value, ch);
#endif /* UMCTL2_CID_EN */
#ifdef UMCTL2_CID_EN
	        dwc_ddrctl_cinit_write_capar_cmdbuf(37 , MC_JPC4AR[3][1].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(38 , MC_PRANKREFAB[3].value         , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(39 , MC_JPC4AR[2][1].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(40 , MC_PRANKREFAB[2].value         , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(41 , MC_JPC4AR[1][1].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(42 , MC_PRANKREFAB[1].value         , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(43 , MC_PRANKREFAB[0].value         , ch);
#else  /* UMCTL2_CID_EN */
	        dwc_ddrctl_cinit_write_capar_cmdbuf(37 , MC_PRANKREFAB[4].value         , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(38 , MC_IWAITTIME[0].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(39 , MC_IWAITTIME[0].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(40 , MC_IWAITTIME[0].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(41 , MC_IWAITTIME[0].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(42 , MC_IWAITTIME[0].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(43 , MC_IWAITTIME[0].value          , ch);
#endif /* UMCTL2_CID_EN */
	        dwc_ddrctl_cinit_write_capar_cmdbuf(44 , MC_CTRLUPD.value               , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(45 , MC_RESUMEREF[4].value          , ch);
	        dwc_ddrctl_cinit_write_capar_cmdbuf(46 , MC_ENDQ[4].value               , ch);
	    }

#endif // DDRCTL_DDR
	SNPS_TRACE("Leaving");
}


/** @brief top level method to program microcode
 */
void dwc_ddrctl_cinit_prgm_ucode(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_DDR
	dwc_ddrctl_cinit_prgm_ucode_load_lp(cinit_cfg);
	dwc_ddrctl_cinit_prgm_ucode_load_du(cinit_cfg);
#ifdef DDRCTL_CAPAR_RETRY
	dwc_ddrctl_cinit_prgm_ucode_load_capar(cinit_cfg);
#endif /* DDRCTL_CAPAR_RETRY */
#endif /* DDRCTL_DDR */
}


/** @brief top level method to program DDR5 PAS configuration buffer
 */
void dwc_ddrctl_cinit_prgm_cfgbuf(SubsysHdlr_t *cinit_cfg)
{
#ifdef DDRCTL_DDR
	dwc_ddrctl_cinit_prgm_gblk_cfgbuf(cinit_cfg);
	dwc_ddrctl_cinit_prgm_rank_blk_cfgbuf(cinit_cfg);
#endif /* DDRCTL_DDR */
};

