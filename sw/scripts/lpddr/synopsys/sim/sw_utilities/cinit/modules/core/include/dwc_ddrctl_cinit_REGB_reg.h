// coreBuilder: This is an automated C header file. DO NOT EDIT.

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


#ifndef __DWC_DDRCTL_CINIT_REGB_REG_H__
#define __DWC_DDRCTL_CINIT_REGB_REG_H__

#include "dwc_cinit_io.h"

typedef union tag_MSTR0 {
	uint32_t value;
	struct {
		uint32_t ddr4							: 1;	// [00]
		uint32_t lpddr4							: 1;	// [01]
		uint32_t ddr5							: 1;	// [02]
		uint32_t lpddr5							: 1;	// [03]
		uint32_t bank_config						: 2;	// [04 ... 05]
		uint32_t bg_config						: 2;	// [06 ... 07]
		uint32_t burst_mode						: 1;	// [08]
		uint32_t burstchop						: 1;	// [09]
		uint32_t en_2t_timing_mode					: 1;	// [10]
		uint32_t lpddr5x						: 1;	// [11]
		uint32_t data_bus_width						: 2;	// [12 ... 13]
		const uint32_t _RESERVED0					: 1;	// [14]
		uint32_t dll_off_mode						: 1;	// [15]
		uint32_t burst_rdwr						: 5;	// [16 ... 20]
		uint32_t active_logical_ranks					: 3;	// [21 ... 23]
		uint32_t active_ranks						: 6;	// [24 ... 29]
		uint32_t device_config						: 2;	// [30 ... 31]
	};
} MSTR0_t;

typedef union tag_MSTR1 {
	uint32_t value;
	struct {
		uint32_t rank_tmgreg_sel					: 4;	// [00 ... 03]
		uint32_t bank_config_2						: 2;	// [04 ... 05]
		uint32_t bg_config_2						: 2;	// [06 ... 07]
		uint32_t rfc_tmgreg_sel						: 8;	// [08 ... 15]
		uint32_t alt_addrmap_en						: 1;	// [16]
		const uint32_t _RESERVED0					: 4;	// [17 ... 20]
		uint32_t active_logical_ranks_2					: 3;	// [21 ... 23]
		const uint32_t _RESERVED1					: 6;	// [24 ... 29]
		uint32_t device_config_2					: 2;	// [30 ... 31]
	};
} MSTR1_t;

typedef union tag_MSTR2 {
	uint32_t value;
	struct {
		uint32_t target_frequency					: 32;	// [00 ... 31]
	};
} MSTR2_t;

typedef union tag_MSTR3 {
	uint32_t value;
	struct {
		uint32_t geardown_mode						: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t rank_tmgset_sel					: 4;	// [04 ... 07]
		uint32_t rank_dev_cfg_sel					: 24;	// [08 ... 31]
	};
} MSTR3_t;

typedef union tag_MSTR4 {
	uint32_t value;
	struct {
		uint32_t wck_on							: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t wck_suspend_en						: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t ws_off_en						: 1;	// [08]
		const uint32_t _RESERVED2					: 23;	// [09 ... 31]
	};
} MSTR4_t;

typedef union tag_STAT {
	uint32_t value;
	struct {
		const uint32_t operating_mode					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t selfref_type					: 8;	// [04 ... 11]
		const uint32_t selfref_state					: 3;	// [12 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		const uint32_t selfref_cam_not_empty				: 1;	// [16]
		const uint32_t _RESERVED2					: 3;	// [17 ... 19]
		const uint32_t powerdown_state					: 4;	// [20 ... 23]
		const uint32_t mpsm_state					: 6;	// [24 ... 29]
		const uint32_t dfi_lp_state					: 1;	// [30]
		const uint32_t _RESERVED3					: 1;	// [31]
	};
} STAT_t;

typedef union tag_STAT2 {
	uint32_t value;
	struct {
		const uint32_t glb_blk_events_ongoing				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 16;	// [08 ... 23]
		const uint32_t selfref_ongoing					: 4;	// [24 ... 27]
		const uint32_t powerdown_ongoing				: 4;	// [28 ... 31]
	};
} STAT2_t;

typedef union tag_STAT3 {
	uint32_t value;
	struct {
		const uint32_t rank_blk_events_ongoing				: 32;	// [00 ... 31]
	};
} STAT3_t;

typedef union tag_MRCTRL0 {
	uint32_t value;
	struct {
		uint32_t mr_type						: 1;	// [00]
		uint32_t mpr_en							: 1;	// [01]
		uint32_t pda_en							: 1;	// [02]
		uint32_t sw_init_int						: 1;	// [03]
		uint32_t mr_rank						: 8;	// [04 ... 11]
		uint32_t mr_addr						: 4;	// [12 ... 15]
		uint32_t mr_cid							: 8;	// [16 ... 23]
		uint32_t mrr_done_clr						: 1;	// [24]
		const uint32_t _RESERVED0					: 2;	// [25 ... 26]
		uint32_t dis_mrrw_trfc						: 1;	// [27]
		uint32_t ppr_en							: 1;	// [28]
		uint32_t ppr_pgmpst_en						: 1;	// [29]
		uint32_t pba_mode						: 1;	// [30]
		uint32_t mr_wr							: 1;	// [31]
	};
} MRCTRL0_t;

typedef union tag_MRCTRL1 {
	uint32_t value;
	struct {
		uint32_t mr_data						: 32;	// [00 ... 31]
	};
} MRCTRL1_t;

typedef union tag_MRCTRL2 {
	uint32_t value;
	struct {
		uint32_t mr_device_sel						: 32;	// [00 ... 31]
	};
} MRCTRL2_t;

typedef union tag_MRSTAT {
	uint32_t value;
	struct {
		const uint32_t mr_wr_busy					: 1;	// [00]
		const uint32_t _RESERVED0					: 7;	// [01 ... 07]
		const uint32_t pda_done						: 1;	// [08]
		const uint32_t _RESERVED1					: 7;	// [09 ... 15]
		const uint32_t mrr_done						: 1;	// [16]
		const uint32_t ppr_done						: 1;	// [17]
		const uint32_t _RESERVED2					: 14;	// [18 ... 31]
	};
} MRSTAT_t;

typedef union tag_MRRDATA0 {
	uint32_t value;
	struct {
		const uint32_t mrr_data_lwr					: 32;	// [00 ... 31]
	};
} MRRDATA0_t;

typedef union tag_MRRDATA1 {
	uint32_t value;
	struct {
		const uint32_t mrr_data_upr					: 32;	// [00 ... 31]
	};
} MRRDATA1_t;

typedef union tag_DERATECTL0 {
	uint32_t value;
	struct {
		uint32_t derate_enable						: 1;	// [00]
		uint32_t lpddr4_refresh_mode					: 1;	// [01]
		uint32_t derate_mr4_pause_fc					: 1;	// [02]
		uint32_t dis_trefi_x6x8						: 1;	// [03]
		uint32_t dis_trefi_x0125					: 1;	// [04]
		uint32_t use_slow_rm_in_low_temp				: 1;	// [05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} DERATECTL0_t;

typedef union tag_DERATECTL1 {
	uint32_t value;
	struct {
		uint32_t active_derate_byte_rank0				: 32;	// [00 ... 31]
	};
} DERATECTL1_t;

typedef union tag_DERATECTL2 {
	uint32_t value;
	struct {
		uint32_t active_derate_byte_rank1				: 32;	// [00 ... 31]
	};
} DERATECTL2_t;

typedef union tag_DERATECTL3 {
	uint32_t value;
	struct {
		uint32_t active_derate_byte_rank2				: 32;	// [00 ... 31]
	};
} DERATECTL3_t;

typedef union tag_DERATECTL4 {
	uint32_t value;
	struct {
		uint32_t active_derate_byte_rank3				: 32;	// [00 ... 31]
	};
} DERATECTL4_t;

typedef union tag_DERATECTL5 {
	uint32_t value;
	struct {
		uint32_t derate_temp_limit_intr_en				: 1;	// [00]
		uint32_t derate_temp_limit_intr_clr				: 1;	// [01]
		uint32_t derate_temp_limit_intr_force				: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} DERATECTL5_t;

typedef union tag_DERATECTL6 {
	uint32_t value;
	struct {
		uint32_t derate_mr4_tuf_dis					: 1;	// [00]
		uint32_t dis_mrr4_tcr_srx					: 1;	// [01]
		uint32_t derate_temp_limit_intr_normal_en			: 1;	// [02]
		uint32_t derate_temp_limit_intr_high_en				: 1;	// [03]
		uint32_t derate_temp_limit_intr_low_en				: 1;	// [04]
		const uint32_t _RESERVED0					: 11;	// [05 ... 15]
		uint32_t derate_low_temp_limit					: 3;	// [16 ... 18]
		const uint32_t _RESERVED1					: 1;	// [19]
		uint32_t derate_high_temp_limit					: 3;	// [20 ... 22]
		const uint32_t _RESERVED2					: 9;	// [23 ... 31]
	};
} DERATECTL6_t;

typedef union tag_DERATECTL7 {
	uint32_t value;
	struct {
		uint32_t derate_temp_limit_intr_clr_rank0			: 1;	// [00]
		uint32_t derate_temp_limit_intr_clr_rank1			: 1;	// [01]
		uint32_t derate_temp_limit_intr_clr_rank2			: 1;	// [02]
		uint32_t derate_temp_limit_intr_clr_rank3			: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} DERATECTL7_t;

typedef union tag_DERATESTAT0 {
	uint32_t value;
	struct {
		const uint32_t derate_temp_limit_intr				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DERATESTAT0_t;

typedef union tag_DERATESTAT1 {
	uint32_t value;
	struct {
		const uint32_t refresh_rate_rank0				: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t refresh_rate_rank1				: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t refresh_rate_rank2				: 3;	// [08 ... 10]
		const uint32_t _RESERVED2					: 1;	// [11]
		const uint32_t refresh_rate_rank3				: 3;	// [12 ... 14]
		const uint32_t _RESERVED3					: 1;	// [15]
		const uint32_t derate_temp_limit_intr_sts_rank0			: 4;	// [16 ... 19]
		const uint32_t derate_temp_limit_intr_sts_rank1			: 4;	// [20 ... 23]
		const uint32_t derate_temp_limit_intr_sts_rank2			: 4;	// [24 ... 27]
		const uint32_t derate_temp_limit_intr_sts_rank3			: 4;	// [28 ... 31]
	};
} DERATESTAT1_t;

typedef union tag_DERATEDBGCTL {
	uint32_t value;
	struct {
		uint32_t dbg_mr4_grp_sel					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t dbg_mr4_rank_sel					: 2;	// [04 ... 05]
		const uint32_t _RESERVED1					: 26;	// [06 ... 31]
	};
} DERATEDBGCTL_t;

typedef union tag_DERATEDBGSTAT {
	uint32_t value;
	struct {
		const uint32_t dbg_mr4_byte0					: 8;	// [00 ... 07]
		const uint32_t dbg_mr4_byte1					: 8;	// [08 ... 15]
		const uint32_t dbg_mr4_byte2					: 8;	// [16 ... 23]
		const uint32_t dbg_mr4_byte3					: 8;	// [24 ... 31]
	};
} DERATEDBGSTAT_t;

typedef union tag_PWRCTL {
	uint32_t value;
	struct {
		uint32_t selfref_en						: 4;	// [00 ... 03]
		uint32_t powerdown_en						: 4;	// [04 ... 07]
		uint32_t actv_pd_en						: 1;	// [08]
		uint32_t en_dfi_dram_clk_disable				: 1;	// [09]
		uint32_t mpsm_en						: 1;	// [10]
		uint32_t selfref_sw						: 1;	// [11]
		const uint32_t _RESERVED0					: 3;	// [12 ... 14]
		uint32_t stay_in_selfref					: 1;	// [15]
		uint32_t dis_cam_drain_selfref					: 1;	// [16]
		uint32_t lpddr4_sr_allowed					: 1;	// [17]
		uint32_t dsm_en							: 1;	// [18]
		const uint32_t _RESERVED1					: 1;	// [19]
		uint32_t mpsm_pd_en						: 4;	// [20 ... 23]
		uint32_t mpsm_deep_pd_en					: 8;	// [24 ... 31]
	};
} PWRCTL_t;

typedef union tag_HWLPCTL {
	uint32_t value;
	struct {
		uint32_t hw_lp_en						: 1;	// [00]
		uint32_t hw_lp_exit_idle_en					: 1;	// [01]
		uint32_t hw_lp_ctrl						: 1;	// [02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		uint32_t hw_lp_accept_wait_window				: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 20;	// [12 ... 31]
	};
} HWLPCTL_t;

typedef union tag_HWLPCTL2 {
	uint32_t value;
	struct {
		uint32_t cactive_in_mask					: 32;	// [00 ... 31]
	};
} HWLPCTL2_t;

typedef union tag_CLKGATECTL {
	uint32_t value;
	struct {
		uint32_t bsm_clk_on						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} CLKGATECTL_t;

typedef union tag_RFSHMOD0 {
	uint32_t value;
	struct {
		uint32_t refresh_burst						: 6;	// [00 ... 05]
		uint32_t auto_refab_en						: 2;	// [06 ... 07]
		uint32_t per_bank_refresh					: 1;	// [08]
		uint32_t per_bank_refresh_opt_en				: 1;	// [09]
		uint32_t refresh_burst_2x					: 6;	// [10 ... 15]
		uint32_t mixed_refsb_hi_thr					: 4;	// [16 ... 19]
		const uint32_t _RESERVED0					: 4;	// [20 ... 23]
		uint32_t fixed_crit_refpb_bank_en				: 1;	// [24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} RFSHMOD0_t;

typedef union tag_RFSHMOD1 {
	uint32_t value;
	struct {
		uint32_t same_bank_refresh					: 2;	// [00 ... 01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t tcr_refab_thr						: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		uint32_t fgr_mode						: 3;	// [08 ... 10]
		const uint32_t _RESERVED2					: 21;	// [11 ... 31]
	};
} RFSHMOD1_t;

typedef union tag_RFSHCTL0 {
	uint32_t value;
	struct {
		uint32_t dis_auto_refresh					: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t refresh_update_level					: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t ref_3ds_burst_limit_en					: 1;	// [08]
		uint32_t ref_3ds_burst_limit_thr				: 6;	// [09 ... 14]
		const uint32_t _RESERVED2					: 1;	// [15]
		uint32_t rank_dis_refresh					: 16;	// [16 ... 31]
	};
} RFSHCTL0_t;

typedef union tag_RFMMOD0 {
	uint32_t value;
	struct {
		uint32_t rfm_en							: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t rfmsbc							: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t raaimt							: 5;	// [08 ... 12]
		const uint32_t _RESERVED2					: 3;	// [13 ... 15]
		uint32_t raamult						: 2;	// [16 ... 17]
		uint32_t raadec							: 2;	// [18 ... 19]
		const uint32_t _RESERVED3					: 4;	// [20 ... 23]
		uint32_t rfmth_rm_thr						: 5;	// [24 ... 28]
		const uint32_t _RESERVED4					: 3;	// [29 ... 31]
	};
} RFMMOD0_t;

typedef union tag_RFMMOD1 {
	uint32_t value;
	struct {
		uint32_t init_raa_cnt						: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 21;	// [11 ... 31]
	};
} RFMMOD1_t;

typedef union tag_RFMCTL {
	uint32_t value;
	struct {
		uint32_t dbg_raa_rank						: 4;	// [00 ... 03]
		uint32_t dbg_raa_bg_bank					: 28;	// [04 ... 31]
	};
} RFMCTL_t;

typedef union tag_RFMSTAT {
	uint32_t value;
	struct {
		const uint32_t rank_raa_cnt_gt0					: 16;	// [00 ... 15]
		const uint32_t dbg_raa_cnt					: 11;	// [16 ... 26]
		const uint32_t _RESERVED0					: 5;	// [27 ... 31]
	};
} RFMSTAT_t;

typedef union tag_ZQCTL0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 28;	// [00 ... 27]
		uint32_t dis_mpsmx_zqcl						: 1;	// [28]
		uint32_t zq_resistor_shared					: 1;	// [29]
		const uint32_t _RESERVED1					: 1;	// [30]
		uint32_t dis_auto_zq						: 1;	// [31]
	};
} ZQCTL0_t;

typedef union tag_ZQCTL1 {
	uint32_t value;
	struct {
		uint32_t zq_reset						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} ZQCTL1_t;

typedef union tag_ZQCTL2 {
	uint32_t value;
	struct {
		uint32_t dis_srx_zqcl						: 1;	// [00]
		uint32_t dis_srx_zqcl_hwffc					: 1;	// [01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} ZQCTL2_t;

typedef union tag_ZQSTAT {
	uint32_t value;
	struct {
		const uint32_t zq_reset_busy					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} ZQSTAT_t;

typedef union tag_DQSOSCRUNTIME {
	uint32_t value;
	struct {
		uint32_t dqsosc_runtime						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t wck2dqo_runtime					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} DQSOSCRUNTIME_t;

typedef union tag_DQSOSCSTAT0 {
	uint32_t value;
	struct {
		const uint32_t dqsosc_state					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t dqsosc_per_rank_stat				: 28;	// [04 ... 31]
	};
} DQSOSCSTAT0_t;

typedef union tag_DQSOSCCFG0 {
	uint32_t value;
	struct {
		uint32_t dis_dqsosc_srx						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DQSOSCCFG0_t;

typedef union tag_DQSOSCTMG0 {
	uint32_t value;
	struct {
		uint32_t t_oscs							: 14;	// [00 ... 13]
		const uint32_t _RESERVED0					: 2;	// [14 ... 15]
		uint32_t t_trkcalccur						: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} DQSOSCTMG0_t;

typedef union tag_SCHED0 {
	uint32_t value;
	struct {
		uint32_t dis_opt_wrecc_collision_flush				: 1;	// [00]
		uint32_t prefer_write						: 1;	// [01]
		uint32_t pageclose						: 1;	// [02]
		uint32_t rdwr_switch_policy_sel					: 1;	// [03]
		uint32_t opt_wrcam_fill_level					: 1;	// [04]
		uint32_t dis_opt_ntt_by_act					: 1;	// [05]
		uint32_t dis_opt_ntt_by_pre					: 1;	// [06]
		uint32_t autopre_rmw						: 1;	// [07]
		uint32_t lpr_num_entries					: 7;	// [08 ... 14]
		uint32_t lpddr4_opt_act_timing					: 1;	// [15]
		uint32_t lpddr5_opt_act_timing					: 1;	// [16]
		const uint32_t _RESERVED0					: 7;	// [17 ... 23]
		uint32_t w_starve_free_running					: 1;	// [24]
		uint32_t dis_prefer_col_by_act					: 1;	// [25]
		uint32_t dis_prefer_col_by_pre					: 1;	// [26]
		uint32_t opt_act_lat						: 1;	// [27]
		uint32_t en_count_every_wr					: 1;	// [28]
		uint32_t prefer_read						: 1;	// [29]
		uint32_t dis_speculative_act					: 1;	// [30]
		uint32_t opt_vprw_sch						: 1;	// [31]
	};
} SCHED0_t;

typedef union tag_SCHED1 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 12;	// [00 ... 11]
		uint32_t delay_switch_write					: 4;	// [12 ... 15]
		uint32_t visible_window_limit_wr				: 3;	// [16 ... 18]
		const uint32_t _RESERVED1					: 1;	// [19]
		uint32_t visible_window_limit_rd				: 3;	// [20 ... 22]
		const uint32_t _RESERVED2					: 1;	// [23]
		uint32_t page_hit_limit_wr					: 3;	// [24 ... 26]
		const uint32_t _RESERVED3					: 1;	// [27]
		uint32_t page_hit_limit_rd					: 3;	// [28 ... 30]
		uint32_t opt_hit_gt_hpr						: 1;	// [31]
	};
} SCHED1_t;

typedef union tag_SCHED2 {
	uint32_t value;
	struct {
		uint32_t dyn_bsm_mode						: 1;	// [00]
		uint32_t max_num_alloc_bsm_clr					: 1;	// [01]
		uint32_t max_num_unalloc_entries_clr				: 1;	// [02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t bank_hit_limit						: 4;	// [04 ... 07]
		uint32_t dealloc_bsm_thr					: 8;	// [08 ... 15]
		uint32_t dealloc_num_bsm_m1					: 16;	// [16 ... 31]
	};
} SCHED2_t;

typedef union tag_SCHED3 {
	uint32_t value;
	struct {
		uint32_t wrcam_lowthresh					: 8;	// [00 ... 07]
		uint32_t wrcam_highthresh					: 8;	// [08 ... 15]
		uint32_t wr_pghit_num_thresh					: 8;	// [16 ... 23]
		uint32_t rd_pghit_num_thresh					: 8;	// [24 ... 31]
	};
} SCHED3_t;

typedef union tag_SCHED4 {
	uint32_t value;
	struct {
		uint32_t rd_act_idle_gap					: 8;	// [00 ... 07]
		uint32_t wr_act_idle_gap					: 8;	// [08 ... 15]
		uint32_t rd_page_exp_cycles					: 8;	// [16 ... 23]
		uint32_t wr_page_exp_cycles					: 8;	// [24 ... 31]
	};
} SCHED4_t;

typedef union tag_SCHED5 {
	uint32_t value;
	struct {
		uint32_t wrecc_cam_lowthresh					: 8;	// [00 ... 07]
		uint32_t wrecc_cam_highthresh					: 20;	// [08 ... 27]
		uint32_t dis_opt_loaded_wrecc_cam_fill_level			: 1;	// [28]
		uint32_t dis_opt_valid_wrecc_cam_fill_level			: 1;	// [29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} SCHED5_t;

typedef union tag_HWFFCCTL {
	uint32_t value;
	struct {
		uint32_t hwffc_en						: 2;	// [00 ... 01]
		uint32_t hwffc_odt_en						: 1;	// [02]
		uint32_t hwffc_vref_en						: 1;	// [03]
		uint32_t init_fsp						: 1;	// [04]
		uint32_t init_vrcg						: 1;	// [05]
		uint32_t target_vrcg						: 1;	// [06]
		uint32_t cke_power_down_mode					: 1;	// [07]
		uint32_t power_saving_ctrl_word					: 4;	// [08 ... 11]
		uint32_t ctrl_word_num						: 4;	// [12 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t skip_mrw_odtvref					: 1;	// [24]
		uint32_t skip_zq_stop_start					: 1;	// [25]
		uint32_t zq_interval						: 2;	// [26 ... 27]
		const uint32_t _RESERVED1					: 3;	// [28 ... 30]
		uint32_t hwffc_mode						: 1;	// [31]
	};
} HWFFCCTL_t;

typedef union tag_HWFFCSTAT {
	uint32_t value;
	struct {
		const uint32_t hwffc_in_progress				: 1;	// [00]
		const uint32_t hwffc_operating_mode				: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		const uint32_t current_frequency				: 4;	// [04 ... 07]
		const uint32_t current_fsp					: 1;	// [08]
		const uint32_t current_vrcg					: 1;	// [09]
		const uint32_t _RESERVED1					: 22;	// [10 ... 31]
	};
} HWFFCSTAT_t;

typedef union tag_HWFFC_MRWBUF_CTRL0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t hwffc_mrwbuf_addr					: 8;	// [16 ... 23]
		uint32_t hwffc_mrwbuf_select					: 6;	// [24 ... 29]
		uint32_t hwffc_mrwbuf_rw_type					: 1;	// [30]
		uint32_t hwffc_mrwbuf_rw_start					: 1;	// [31]
	};
} HWFFC_MRWBUF_CTRL0_t;

typedef union tag_HWFFC_MRWBUF_CTRL1 {
	uint32_t value;
	struct {
		uint32_t hwffc_mrwbuf_wdata					: 32;	// [00 ... 31]
	};
} HWFFC_MRWBUF_CTRL1_t;

typedef union tag_HWFFC_MRWBUF_STAT {
	uint32_t value;
	struct {
		const uint32_t hwffc_mrwbuf_rdata				: 32;	// [00 ... 31]
	};
} HWFFC_MRWBUF_STAT_t;

typedef union tag_DQMAP0 {
	uint32_t value;
	struct {
		uint32_t dq_nibble_map_0_3					: 8;	// [00 ... 07]
		uint32_t dq_nibble_map_4_7					: 8;	// [08 ... 15]
		uint32_t dq_nibble_map_8_11					: 8;	// [16 ... 23]
		uint32_t dq_nibble_map_12_15					: 8;	// [24 ... 31]
	};
} DQMAP0_t;

typedef union tag_DQMAP1 {
	uint32_t value;
	struct {
		uint32_t dq_nibble_map_16_19					: 8;	// [00 ... 07]
		uint32_t dq_nibble_map_20_23					: 8;	// [08 ... 15]
		uint32_t dq_nibble_map_24_27					: 8;	// [16 ... 23]
		uint32_t dq_nibble_map_28_31					: 8;	// [24 ... 31]
	};
} DQMAP1_t;

typedef union tag_DQMAP2 {
	uint32_t value;
	struct {
		uint32_t dq_nibble_map_32_35					: 8;	// [00 ... 07]
		uint32_t dq_nibble_map_36_39					: 8;	// [08 ... 15]
		uint32_t dq_nibble_map_40_43					: 8;	// [16 ... 23]
		uint32_t dq_nibble_map_44_47					: 8;	// [24 ... 31]
	};
} DQMAP2_t;

typedef union tag_DQMAP3 {
	uint32_t value;
	struct {
		uint32_t dq_nibble_map_48_51					: 8;	// [00 ... 07]
		uint32_t dq_nibble_map_52_55					: 8;	// [08 ... 15]
		uint32_t dq_nibble_map_56_59					: 8;	// [16 ... 23]
		uint32_t dq_nibble_map_60_63					: 8;	// [24 ... 31]
	};
} DQMAP3_t;

typedef union tag_DQMAP4 {
	uint32_t value;
	struct {
		uint32_t dq_nibble_map_cb_0_3					: 8;	// [00 ... 07]
		uint32_t dq_nibble_map_cb_4_7					: 8;	// [08 ... 15]
		uint32_t dq_nibble_map_cb_8_11					: 8;	// [16 ... 23]
		uint32_t dq_nibble_map_cb_12_15					: 8;	// [24 ... 31]
	};
} DQMAP4_t;

typedef union tag_DQMAP5 {
	uint32_t value;
	struct {
		uint32_t dis_dq_rank_swap					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DQMAP5_t;

typedef union tag_DFILPCFG0 {
	uint32_t value;
	struct {
		uint32_t dfi_lp_en_pd						: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t dfi_lp_en_sr						: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t dfi_lp_en_dsm						: 1;	// [08]
		const uint32_t _RESERVED2					: 3;	// [09 ... 11]
		uint32_t dfi_lp_en_mpsm						: 1;	// [12]
		const uint32_t _RESERVED3					: 3;	// [13 ... 15]
		uint32_t dfi_lp_en_data						: 1;	// [16]
		const uint32_t _RESERVED4					: 3;	// [17 ... 19]
		uint32_t dfi_lp_data_req_en					: 1;	// [20]
		const uint32_t _RESERVED5					: 3;	// [21 ... 23]
		uint32_t dfi_lp_extra_gap					: 4;	// [24 ... 27]
		uint32_t extra_gap_for_dfi_lp_data				: 2;	// [28 ... 29]
		const uint32_t _RESERVED6					: 2;	// [30 ... 31]
	};
} DFILPCFG0_t;

typedef union tag_DFIUPD0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 15;	// [00 ... 14]
		uint32_t dfi_phyupd_en						: 1;	// [15]
		const uint32_t _RESERVED1					: 13;	// [16 ... 28]
		uint32_t ctrlupd_pre_srx					: 1;	// [29]
		uint32_t dis_auto_ctrlupd_srx					: 1;	// [30]
		uint32_t dis_auto_ctrlupd					: 1;	// [31]
	};
} DFIUPD0_t;

typedef union tag_DFIUPD1 {
	uint32_t value;
	struct {
		uint32_t dfi_phyupd_type0_wait_idle				: 1;	// [00]
		const uint32_t _RESERVED0					: 7;	// [01 ... 07]
		uint32_t dfi_phyupd_type1_wait_idle				: 1;	// [08]
		const uint32_t _RESERVED1					: 7;	// [09 ... 15]
		uint32_t dfi_phyupd_type2_wait_idle				: 1;	// [16]
		const uint32_t _RESERVED2					: 7;	// [17 ... 23]
		uint32_t dfi_phyupd_type3_wait_idle				: 1;	// [24]
		const uint32_t _RESERVED3					: 7;	// [25 ... 31]
	};
} DFIUPD1_t;

typedef union tag_DFIMISC {
	uint32_t value;
	struct {
		uint32_t dfi_init_complete_en					: 1;	// [00]
		uint32_t phy_dbi_mode						: 1;	// [01]
		uint32_t dfi_data_cs_polarity					: 1;	// [02]
		uint32_t share_dfi_dram_clk_disable				: 1;	// [03]
		uint32_t dfi_reset_n						: 1;	// [04]
		uint32_t dfi_init_start						: 1;	// [05]
		uint32_t dis_dyn_adr_tri					: 1;	// [06]
		uint32_t lp_optimized_write					: 1;	// [07]
		uint32_t dfi_frequency						: 5;	// [08 ... 12]
		const uint32_t _RESERVED0					: 1;	// [13]
		uint32_t dfi_freq_fsp						: 2;	// [14 ... 15]
		uint32_t dfi_channel_mode					: 2;	// [16 ... 17]
		const uint32_t _RESERVED1					: 14;	// [18 ... 31]
	};
} DFIMISC_t;

typedef union tag_DFISTAT {
	uint32_t value;
	struct {
		const uint32_t dfi_init_complete				: 1;	// [00]
		const uint32_t dfi_lp_ctrl_ack_stat				: 1;	// [01]
		const uint32_t dfi_lp_data_ack_stat				: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} DFISTAT_t;

typedef union tag_DFIPHYMSTR {
	uint32_t value;
	struct {
		uint32_t dfi_phymstr_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 23;	// [01 ... 23]
		uint32_t dfi_phymstr_blk_ref_x32				: 8;	// [24 ... 31]
	};
} DFIPHYMSTR_t;

typedef union tag_DFI0MSGCTL0 {
	uint32_t value;
	struct {
		uint32_t dfi0_ctrlmsg_data					: 16;	// [00 ... 15]
		uint32_t dfi0_ctrlmsg_cmd					: 8;	// [16 ... 23]
		uint32_t dfi0_ctrlmsg_tout_clr					: 1;	// [24]
		const uint32_t _RESERVED0					: 6;	// [25 ... 30]
		uint32_t dfi0_ctrlmsg_req					: 1;	// [31]
	};
} DFI0MSGCTL0_t;

typedef union tag_DFI0MSGSTAT0 {
	uint32_t value;
	struct {
		const uint32_t dfi0_ctrlmsg_req_busy				: 1;	// [00]
		const uint32_t _RESERVED0					: 15;	// [01 ... 15]
		const uint32_t dfi0_ctrlmsg_resp_tout				: 1;	// [16]
		const uint32_t _RESERVED1					: 15;	// [17 ... 31]
	};
} DFI0MSGSTAT0_t;

typedef union tag_DFISBINTRPTCFG {
	uint32_t value;
	struct {
		uint32_t dfi_sideband_timer_err_intr_en				: 1;	// [00]
		uint32_t dfi_sideband_timer_err_intr_clr			: 1;	// [01]
		uint32_t dfi_sideband_timer_err_intr_force			: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} DFISBINTRPTCFG_t;

typedef union tag_DFISBPOISONCFG {
	uint32_t value;
	struct {
		uint32_t dfi_tctrlupd_min_poison_err_inj			: 1;	// [00]
		uint32_t dfi_tctrlupd_max_poison_err_inj			: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t dfi_tinit_start_poison_err_inj				: 1;	// [04]
		uint32_t dfi_tinit_complete_poison_err_inj			: 1;	// [05]
		const uint32_t _RESERVED1					: 2;	// [06 ... 07]
		uint32_t dfi_tlp_ctrl_resp_poison_err_inj			: 1;	// [08]
		uint32_t dfi_tlp_data_resp_poison_err_inj			: 1;	// [09]
		uint32_t dfi_tlp_ctrl_wakeup_poison_err_inj			: 1;	// [10]
		uint32_t dfi_tlp_data_wakeup_poison_err_inj			: 1;	// [11]
		const uint32_t _RESERVED2					: 4;	// [12 ... 15]
		uint32_t dfi_tctrlupd_min_poison_margin				: 4;	// [16 ... 19]
		uint32_t dfi_tinit_start_poison_margin				: 4;	// [20 ... 23]
		uint32_t dfi_tlp_ctrl_resp_poison_margin			: 4;	// [24 ... 27]
		uint32_t dfi_tlp_data_resp_poison_margin			: 4;	// [28 ... 31]
	};
} DFISBPOISONCFG_t;

typedef union tag_DFISBTIMERSTAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 1;	// [00]
		const uint32_t dfi_tctrlupd_min_error				: 1;	// [01]
		const uint32_t dfi_tctrlupd_max_error				: 1;	// [02]
		const uint32_t _RESERVED1					: 1;	// [03]
		const uint32_t dfi_tinit_start_error				: 1;	// [04]
		const uint32_t dfi_tinit_complete_error				: 1;	// [05]
		const uint32_t _RESERVED2					: 2;	// [06 ... 07]
		const uint32_t dfi_tlp_ctrl_resp_error				: 1;	// [08]
		const uint32_t dfi_tlp_data_resp_error				: 1;	// [09]
		const uint32_t dfi_tlp_ctrl_wakeup_error			: 1;	// [10]
		const uint32_t dfi_tlp_data_wakeup_error			: 1;	// [11]
		const uint32_t _RESERVED3					: 20;	// [12 ... 31]
	};
} DFISBTIMERSTAT_t;

typedef union tag_DFISBTIMERSTAT1 {
	uint32_t value;
	struct {
		const uint32_t dfi_sideband_timer_err_intr			: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DFISBTIMERSTAT1_t;

typedef union tag_DFIERRINTRPTCFG {
	uint32_t value;
	struct {
		uint32_t dfi_error_intr_en					: 1;	// [00]
		uint32_t dfi_error_intr_clr					: 1;	// [01]
		uint32_t dfi_error_intr_force					: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} DFIERRINTRPTCFG_t;

typedef union tag_DFIERRORSTAT {
	uint32_t value;
	struct {
		const uint32_t dfi_error_intr					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DFIERRORSTAT_t;

typedef union tag_DFIERRORSTAT1 {
	uint32_t value;
	struct {
		const uint32_t dfi_error_info					: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} DFIERRORSTAT1_t;

typedef union tag_POISONCFG {
	uint32_t value;
	struct {
		uint32_t wr_poison_slverr_en					: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t wr_poison_intr_en					: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t wr_poison_intr_clr					: 1;	// [08]
		const uint32_t _RESERVED2					: 7;	// [09 ... 15]
		uint32_t rd_poison_slverr_en					: 1;	// [16]
		const uint32_t _RESERVED3					: 3;	// [17 ... 19]
		uint32_t rd_poison_intr_en					: 1;	// [20]
		const uint32_t _RESERVED4					: 3;	// [21 ... 23]
		uint32_t rd_poison_intr_clr					: 1;	// [24]
		const uint32_t _RESERVED5					: 7;	// [25 ... 31]
	};
} POISONCFG_t;

typedef union tag_POISONSTAT {
	uint32_t value;
	struct {
		const uint32_t wr_poison_intr_0					: 1;	// [00]
		const uint32_t wr_poison_intr_1					: 1;	// [01]
		const uint32_t wr_poison_intr_2					: 1;	// [02]
		const uint32_t wr_poison_intr_3					: 1;	// [03]
		const uint32_t wr_poison_intr_4					: 1;	// [04]
		const uint32_t wr_poison_intr_5					: 1;	// [05]
		const uint32_t wr_poison_intr_6					: 1;	// [06]
		const uint32_t wr_poison_intr_7					: 1;	// [07]
		const uint32_t wr_poison_intr_8					: 1;	// [08]
		const uint32_t wr_poison_intr_9					: 1;	// [09]
		const uint32_t wr_poison_intr_10				: 1;	// [10]
		const uint32_t wr_poison_intr_11				: 1;	// [11]
		const uint32_t wr_poison_intr_12				: 1;	// [12]
		const uint32_t wr_poison_intr_13				: 1;	// [13]
		const uint32_t wr_poison_intr_14				: 1;	// [14]
		const uint32_t wr_poison_intr_15				: 1;	// [15]
		const uint32_t rd_poison_intr_0					: 1;	// [16]
		const uint32_t rd_poison_intr_1					: 1;	// [17]
		const uint32_t rd_poison_intr_2					: 1;	// [18]
		const uint32_t rd_poison_intr_3					: 1;	// [19]
		const uint32_t rd_poison_intr_4					: 1;	// [20]
		const uint32_t rd_poison_intr_5					: 1;	// [21]
		const uint32_t rd_poison_intr_6					: 1;	// [22]
		const uint32_t rd_poison_intr_7					: 1;	// [23]
		const uint32_t rd_poison_intr_8					: 1;	// [24]
		const uint32_t rd_poison_intr_9					: 1;	// [25]
		const uint32_t rd_poison_intr_10				: 1;	// [26]
		const uint32_t rd_poison_intr_11				: 1;	// [27]
		const uint32_t rd_poison_intr_12				: 1;	// [28]
		const uint32_t rd_poison_intr_13				: 1;	// [29]
		const uint32_t rd_poison_intr_14				: 1;	// [30]
		const uint32_t rd_poison_intr_15				: 1;	// [31]
	};
} POISONSTAT_t;

typedef union tag_ECCCFG0 {
	uint32_t value;
	struct {
		uint32_t ecc_mode						: 3;	// [00 ... 02]
		uint32_t test_mode						: 1;	// [03]
		uint32_t ecc_type						: 2;	// [04 ... 05]
		uint32_t ecc_ap_en						: 1;	// [06]
		uint32_t ecc_region_remap_en					: 1;	// [07]
		uint32_t ecc_region_map						: 7;	// [08 ... 14]
		const uint32_t _RESERVED0					: 1;	// [15]
		uint32_t blk_channel_idle_time_x32				: 6;	// [16 ... 21]
		const uint32_t _RESERVED1					: 2;	// [22 ... 23]
		uint32_t ecc_ap_err_threshold					: 5;	// [24 ... 28]
		uint32_t ecc_region_map_other					: 1;	// [29]
		uint32_t ecc_region_map_granu					: 2;	// [30 ... 31]
	};
} ECCCFG0_t;

typedef union tag_ECCCFG1 {
	uint32_t value;
	struct {
		uint32_t data_poison_en						: 1;	// [00]
		uint32_t data_poison_bit					: 1;	// [01]
		uint32_t poison_chip_en						: 1;	// [02]
		uint32_t ecc_ap_mode						: 1;	// [03]
		uint32_t ecc_region_parity_lock					: 1;	// [04]
		uint32_t ecc_region_waste_lock					: 1;	// [05]
		uint32_t med_ecc_en						: 1;	// [06]
		uint32_t blk_channel_active_term				: 1;	// [07]
		uint32_t active_blk_channel					: 5;	// [08 ... 12]
		const uint32_t _RESERVED0					: 2;	// [13 ... 14]
		uint32_t poison_advecc_kbd					: 1;	// [15]
		uint32_t poison_num_dfi_beat					: 4;	// [16 ... 19]
		uint32_t prop_rd_ecc_err					: 2;	// [20 ... 21]
		const uint32_t _RESERVED1					: 10;	// [22 ... 31]
	};
} ECCCFG1_t;

typedef union tag_ECCSTAT {
	uint32_t value;
	struct {
		const uint32_t ecc_corrected_bit_num				: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		const uint32_t ecc_corrected_err				: 8;	// [08 ... 15]
		const uint32_t ecc_uncorrected_err				: 8;	// [16 ... 23]
		const uint32_t sbr_read_ecc_ce					: 1;	// [24]
		const uint32_t sbr_read_ecc_ue					: 1;	// [25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} ECCSTAT_t;

typedef union tag_ECCCTL {
	uint32_t value;
	struct {
		uint32_t ecc_corrected_err_clr					: 1;	// [00]
		uint32_t ecc_uncorrected_err_clr				: 1;	// [01]
		uint32_t ecc_corr_err_cnt_clr					: 1;	// [02]
		uint32_t ecc_uncorr_err_cnt_clr					: 1;	// [03]
		uint32_t ecc_ap_err_intr_clr					: 1;	// [04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t ecc_corrected_err_intr_en				: 1;	// [08]
		uint32_t ecc_uncorrected_err_intr_en				: 1;	// [09]
		uint32_t ecc_ap_err_intr_en					: 1;	// [10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t ecc_corrected_err_intr_force				: 1;	// [16]
		uint32_t ecc_uncorrected_err_intr_force				: 1;	// [17]
		uint32_t ecc_ap_err_intr_force					: 1;	// [18]
		const uint32_t _RESERVED2					: 13;	// [19 ... 31]
	};
} ECCCTL_t;

typedef union tag_ECCERRCNT {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_err_cnt					: 16;	// [00 ... 15]
		const uint32_t ecc_uncorr_err_cnt				: 16;	// [16 ... 31]
	};
} ECCERRCNT_t;

typedef union tag_ECCCADDR0 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_row					: 24;	// [00 ... 23]
		const uint32_t ecc_corr_rank					: 8;	// [24 ... 31]
	};
} ECCCADDR0_t;

typedef union tag_ECCCADDR1 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_col					: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t ecc_corr_bank					: 8;	// [16 ... 23]
		const uint32_t ecc_corr_bg					: 4;	// [24 ... 27]
		const uint32_t ecc_corr_cid					: 4;	// [28 ... 31]
	};
} ECCCADDR1_t;

typedef union tag_ECCCSYN0 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_syndromes_31_0				: 32;	// [00 ... 31]
	};
} ECCCSYN0_t;

typedef union tag_ECCCSYN1 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_syndromes_63_32				: 32;	// [00 ... 31]
	};
} ECCCSYN1_t;

typedef union tag_ECCCSYN2 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_syndromes_71_64				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t cb_corr_syndrome					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} ECCCSYN2_t;

typedef union tag_ECCBITMASK0 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_bit_mask_31_0				: 32;	// [00 ... 31]
	};
} ECCBITMASK0_t;

typedef union tag_ECCBITMASK1 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_bit_mask_63_32				: 32;	// [00 ... 31]
	};
} ECCBITMASK1_t;

typedef union tag_ECCBITMASK2 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_bit_mask_71_64				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} ECCBITMASK2_t;

typedef union tag_ECCUADDR0 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_row					: 24;	// [00 ... 23]
		const uint32_t ecc_uncorr_rank					: 8;	// [24 ... 31]
	};
} ECCUADDR0_t;

typedef union tag_ECCUADDR1 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_col					: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t ecc_uncorr_bank					: 8;	// [16 ... 23]
		const uint32_t ecc_uncorr_bg					: 4;	// [24 ... 27]
		const uint32_t ecc_uncorr_cid					: 4;	// [28 ... 31]
	};
} ECCUADDR1_t;

typedef union tag_ECCUSYN0 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_syndromes_31_0			: 32;	// [00 ... 31]
	};
} ECCUSYN0_t;

typedef union tag_ECCUSYN1 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_syndromes_63_32			: 32;	// [00 ... 31]
	};
} ECCUSYN1_t;

typedef union tag_ECCUSYN2 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_syndromes_71_64			: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t cb_uncorr_syndrome				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} ECCUSYN2_t;

typedef union tag_ECCPOISONADDR0 {
	uint32_t value;
	struct {
		uint32_t ecc_poison_col						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t ecc_poison_cid						: 8;	// [16 ... 23]
		uint32_t ecc_poison_rank					: 8;	// [24 ... 31]
	};
} ECCPOISONADDR0_t;

typedef union tag_ECCPOISONADDR1 {
	uint32_t value;
	struct {
		uint32_t ecc_poison_row						: 24;	// [00 ... 23]
		uint32_t ecc_poison_bank					: 4;	// [24 ... 27]
		uint32_t ecc_poison_bg						: 4;	// [28 ... 31]
	};
} ECCPOISONADDR1_t;

typedef union tag_ADVECCINDEX {
	uint32_t value;
	struct {
		uint32_t ecc_syndrome_sel					: 3;	// [00 ... 02]
		uint32_t ecc_err_symbol_sel					: 2;	// [03 ... 04]
		uint32_t ecc_poison_beats_sel					: 4;	// [05 ... 08]
		const uint32_t _RESERVED0					: 23;	// [09 ... 31]
	};
} ADVECCINDEX_t;

typedef union tag_ADVECCSTAT {
	uint32_t value;
	struct {
		const uint32_t advecc_corrected_err				: 1;	// [00]
		const uint32_t advecc_uncorrected_err				: 1;	// [01]
		const uint32_t advecc_num_err_symbol				: 3;	// [02 ... 04]
		const uint32_t advecc_err_symbol_pos				: 11;	// [05 ... 15]
		const uint32_t advecc_err_symbol_bits				: 8;	// [16 ... 23]
		const uint32_t advecc_ce_kbd_stat				: 4;	// [24 ... 27]
		const uint32_t advecc_ue_kbd_stat				: 2;	// [28 ... 29]
		const uint32_t sbr_read_advecc_ce				: 1;	// [30]
		const uint32_t sbr_read_advecc_ue				: 1;	// [31]
	};
} ADVECCSTAT_t;

typedef union tag_ECCPOISONPAT0 {
	uint32_t value;
	struct {
		uint32_t ecc_poison_data_31_0					: 32;	// [00 ... 31]
	};
} ECCPOISONPAT0_t;

typedef union tag_ECCPOISONPAT1 {
	uint32_t value;
	struct {
		uint32_t ecc_poison_data_63_32					: 32;	// [00 ... 31]
	};
} ECCPOISONPAT1_t;

typedef union tag_ECCPOISONPAT2 {
	uint32_t value;
	struct {
		uint32_t ecc_poison_data_71_64					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} ECCPOISONPAT2_t;

typedef union tag_ECCAPSTAT {
	uint32_t value;
	struct {
		const uint32_t ecc_ap_err					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} ECCAPSTAT_t;

typedef union tag_ECCCFG2 {
	uint32_t value;
	struct {
		uint32_t bypass_internal_ecc					: 1;	// [00]
		uint32_t kbd_en							: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t dis_rmw_ue_propagation					: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t eapar_en						: 1;	// [08]
		const uint32_t _RESERVED2					: 7;	// [09 ... 15]
		uint32_t flip_bit_pos0						: 7;	// [16 ... 22]
		const uint32_t _RESERVED3					: 1;	// [23]
		uint32_t flip_bit_pos1						: 7;	// [24 ... 30]
		const uint32_t _RESERVED4					: 1;	// [31]
	};
} ECCCFG2_t;

typedef union tag_ECCCDATA0 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_data_31_0				: 32;	// [00 ... 31]
	};
} ECCCDATA0_t;

typedef union tag_ECCCDATA1 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_data_63_32				: 32;	// [00 ... 31]
	};
} ECCCDATA1_t;

typedef union tag_ECCUDATA0 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_data_31_0				: 32;	// [00 ... 31]
	};
} ECCUDATA0_t;

typedef union tag_ECCUDATA1 {
	uint32_t value;
	struct {
		const uint32_t ecc_uncorr_data_63_32				: 32;	// [00 ... 31]
	};
} ECCUDATA1_t;

typedef union tag_ECCSYMBOL {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_sym_71_64				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t ecc_uncorr_sym_71_64				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} ECCSYMBOL_t;

typedef union tag_OCPARCFG0 {
	uint32_t value;
	struct {
		uint32_t oc_parity_en						: 1;	// [00]
		uint32_t oc_parity_type						: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t par_wdata_err_intr_en					: 1;	// [04]
		uint32_t par_wdata_slverr_en					: 1;	// [05]
		uint32_t par_wdata_err_intr_clr					: 1;	// [06]
		uint32_t par_wdata_err_intr_force				: 1;	// [07]
		uint32_t par_wdata_axi_check_bypass_en				: 1;	// [08]
		const uint32_t _RESERVED1					: 3;	// [09 ... 11]
		uint32_t par_rdata_slverr_en					: 1;	// [12]
		uint32_t par_rdata_err_intr_en					: 1;	// [13]
		uint32_t par_rdata_err_intr_clr					: 1;	// [14]
		uint32_t par_rdata_err_intr_force				: 1;	// [15]
		const uint32_t _RESERVED2					: 4;	// [16 ... 19]
		uint32_t par_addr_slverr_en					: 1;	// [20]
		uint32_t par_waddr_err_intr_en					: 1;	// [21]
		uint32_t par_waddr_err_intr_clr					: 1;	// [22]
		uint32_t par_raddr_err_intr_en					: 1;	// [23]
		uint32_t par_raddr_err_intr_clr					: 1;	// [24]
		uint32_t par_waddr_err_intr_force				: 1;	// [25]
		uint32_t par_raddr_err_intr_force				: 1;	// [26]
		const uint32_t _RESERVED3					: 5;	// [27 ... 31]
	};
} OCPARCFG0_t;

typedef union tag_OCPARCFG1 {
	uint32_t value;
	struct {
		uint32_t par_poison_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 1;	// [01]
		uint32_t par_poison_loc_rd_dfi					: 1;	// [02]
		uint32_t par_poison_loc_rd_iecc_type				: 1;	// [03]
		uint32_t par_poison_loc_rd_port					: 4;	// [04 ... 07]
		uint32_t par_poison_loc_wr_port					: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 4;	// [12 ... 15]
		uint32_t par_poison_byte_num					: 16;	// [16 ... 31]
	};
} OCPARCFG1_t;

typedef union tag_OCPARSTAT0 {
	uint32_t value;
	struct {
		const uint32_t par_waddr_err_intr_0				: 1;	// [00]
		const uint32_t par_waddr_err_intr_1				: 1;	// [01]
		const uint32_t par_waddr_err_intr_2				: 1;	// [02]
		const uint32_t par_waddr_err_intr_3				: 1;	// [03]
		const uint32_t par_waddr_err_intr_4				: 1;	// [04]
		const uint32_t par_waddr_err_intr_5				: 1;	// [05]
		const uint32_t par_waddr_err_intr_6				: 1;	// [06]
		const uint32_t par_waddr_err_intr_7				: 1;	// [07]
		const uint32_t par_waddr_err_intr_8				: 1;	// [08]
		const uint32_t par_waddr_err_intr_9				: 1;	// [09]
		const uint32_t par_waddr_err_intr_10				: 1;	// [10]
		const uint32_t par_waddr_err_intr_11				: 1;	// [11]
		const uint32_t par_waddr_err_intr_12				: 1;	// [12]
		const uint32_t par_waddr_err_intr_13				: 1;	// [13]
		const uint32_t par_waddr_err_intr_14				: 1;	// [14]
		const uint32_t par_waddr_err_intr_15				: 1;	// [15]
		const uint32_t par_raddr_err_intr_0				: 1;	// [16]
		const uint32_t par_raddr_err_intr_1				: 1;	// [17]
		const uint32_t par_raddr_err_intr_2				: 1;	// [18]
		const uint32_t par_raddr_err_intr_3				: 1;	// [19]
		const uint32_t par_raddr_err_intr_4				: 1;	// [20]
		const uint32_t par_raddr_err_intr_5				: 1;	// [21]
		const uint32_t par_raddr_err_intr_6				: 1;	// [22]
		const uint32_t par_raddr_err_intr_7				: 1;	// [23]
		const uint32_t par_raddr_err_intr_8				: 1;	// [24]
		const uint32_t par_raddr_err_intr_9				: 1;	// [25]
		const uint32_t par_raddr_err_intr_10				: 1;	// [26]
		const uint32_t par_raddr_err_intr_11				: 1;	// [27]
		const uint32_t par_raddr_err_intr_12				: 1;	// [28]
		const uint32_t par_raddr_err_intr_13				: 1;	// [29]
		const uint32_t par_raddr_err_intr_14				: 1;	// [30]
		const uint32_t par_raddr_err_intr_15				: 1;	// [31]
	};
} OCPARSTAT0_t;

typedef union tag_OCPARSTAT1 {
	uint32_t value;
	struct {
		const uint32_t par_wdata_in_err_intr_0				: 1;	// [00]
		const uint32_t par_wdata_in_err_intr_1				: 1;	// [01]
		const uint32_t par_wdata_in_err_intr_2				: 1;	// [02]
		const uint32_t par_wdata_in_err_intr_3				: 1;	// [03]
		const uint32_t par_wdata_in_err_intr_4				: 1;	// [04]
		const uint32_t par_wdata_in_err_intr_5				: 1;	// [05]
		const uint32_t par_wdata_in_err_intr_6				: 1;	// [06]
		const uint32_t par_wdata_in_err_intr_7				: 1;	// [07]
		const uint32_t par_wdata_in_err_intr_8				: 1;	// [08]
		const uint32_t par_wdata_in_err_intr_9				: 1;	// [09]
		const uint32_t par_wdata_in_err_intr_10				: 1;	// [10]
		const uint32_t par_wdata_in_err_intr_11				: 1;	// [11]
		const uint32_t par_wdata_in_err_intr_12				: 1;	// [12]
		const uint32_t par_wdata_in_err_intr_13				: 1;	// [13]
		const uint32_t par_wdata_in_err_intr_14				: 1;	// [14]
		const uint32_t par_wdata_in_err_intr_15				: 1;	// [15]
		const uint32_t par_rdata_err_intr_0				: 1;	// [16]
		const uint32_t par_rdata_err_intr_1				: 1;	// [17]
		const uint32_t par_rdata_err_intr_2				: 1;	// [18]
		const uint32_t par_rdata_err_intr_3				: 1;	// [19]
		const uint32_t par_rdata_err_intr_4				: 1;	// [20]
		const uint32_t par_rdata_err_intr_5				: 1;	// [21]
		const uint32_t par_rdata_err_intr_6				: 1;	// [22]
		const uint32_t par_rdata_err_intr_7				: 1;	// [23]
		const uint32_t par_rdata_err_intr_8				: 1;	// [24]
		const uint32_t par_rdata_err_intr_9				: 1;	// [25]
		const uint32_t par_rdata_err_intr_10				: 1;	// [26]
		const uint32_t par_rdata_err_intr_11				: 1;	// [27]
		const uint32_t par_rdata_err_intr_12				: 1;	// [28]
		const uint32_t par_rdata_err_intr_13				: 1;	// [29]
		const uint32_t par_rdata_err_intr_14				: 1;	// [30]
		const uint32_t par_rdata_err_intr_15				: 1;	// [31]
	};
} OCPARSTAT1_t;

typedef union tag_OCPARSTAT2 {
	uint32_t value;
	struct {
		const uint32_t par_wdata_out_err_intr				: 4;	// [00 ... 03]
		const uint32_t par_rdata_in_err_ecc_intr			: 1;	// [04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		const uint32_t par_rdata_log_port_num				: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 20;	// [12 ... 31]
	};
} OCPARSTAT2_t;

typedef union tag_OCPARSTAT3 {
	uint32_t value;
	struct {
		const uint32_t par_rdata_log_byte_num				: 32;	// [00 ... 31]
	};
} OCPARSTAT3_t;

typedef union tag_OCPARSTAT4 {
	uint32_t value;
	struct {
		const uint32_t par_waddr_log_low				: 32;	// [00 ... 31]
	};
} OCPARSTAT4_t;

typedef union tag_OCPARSTAT5 {
	uint32_t value;
	struct {
		const uint32_t par_waddr_log_high				: 28;	// [00 ... 27]
		const uint32_t par_waddr_log_port_num				: 4;	// [28 ... 31]
	};
} OCPARSTAT5_t;

typedef union tag_OCPARSTAT6 {
	uint32_t value;
	struct {
		const uint32_t par_raddr_log_low				: 32;	// [00 ... 31]
	};
} OCPARSTAT6_t;

typedef union tag_OCPARSTAT7 {
	uint32_t value;
	struct {
		const uint32_t par_raddr_log_high				: 28;	// [00 ... 27]
		const uint32_t par_raddr_log_port_num				: 4;	// [28 ... 31]
	};
} OCPARSTAT7_t;

typedef union tag_OCPARSTAT8 {
	uint32_t value;
	struct {
		const uint32_t par_rdata_log_high_byte_num			: 32;	// [00 ... 31]
	};
} OCPARSTAT8_t;

typedef union tag_OCSAPCFG0 {
	uint32_t value;
	struct {
		uint32_t ocsap_par_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 7;	// [01 ... 07]
		uint32_t ocsap_poison_en					: 1;	// [08]
		const uint32_t _RESERVED1					: 3;	// [09 ... 11]
		uint32_t wdataram_addr_poison_loc				: 1;	// [12]
		uint32_t rdataram_addr_poison_loc				: 1;	// [13]
		const uint32_t _RESERVED2					: 2;	// [14 ... 15]
		uint32_t wdataram_addr_poison_ctl				: 3;	// [16 ... 18]
		const uint32_t _RESERVED3					: 5;	// [19 ... 23]
		uint32_t rdataram_addr_poison_ctl				: 3;	// [24 ... 26]
		const uint32_t _RESERVED4					: 1;	// [27]
		uint32_t rdataram_addr_poison_port				: 4;	// [28 ... 31]
	};
} OCSAPCFG0_t;

typedef union tag_OCECCCFG0 {
	uint32_t value;
	struct {
		uint32_t ocecc_en						: 1;	// [00]
		uint32_t ocecc_fec_en						: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t ocecc_uncorrected_err_intr_en				: 1;	// [04]
		uint32_t ocecc_wdata_slverr_en					: 1;	// [05]
		uint32_t ocecc_uncorrected_err_intr_clr				: 1;	// [06]
		uint32_t ocecc_uncorrected_err_intr_force			: 1;	// [07]
		const uint32_t _RESERVED1					: 4;	// [08 ... 11]
		uint32_t ocecc_corrected_err_intr_en				: 1;	// [12]
		uint32_t ocecc_rdata_slverr_en					: 1;	// [13]
		uint32_t ocecc_corrected_err_intr_clr				: 1;	// [14]
		uint32_t ocecc_corrected_err_intr_force				: 1;	// [15]
		const uint32_t _RESERVED2					: 16;	// [16 ... 31]
	};
} OCECCCFG0_t;

typedef union tag_OCECCCFG1 {
	uint32_t value;
	struct {
		uint32_t ocecc_poison_en					: 1;	// [00]
		uint32_t ocecc_poison_egen_mr_rd_0				: 1;	// [01]
		uint32_t ocecc_poison_egen_mr_rd_0_byte_num			: 5;	// [02 ... 06]
		uint32_t ocecc_poison_egen_xpi_rd_out				: 1;	// [07]
		uint32_t ocecc_poison_port_num					: 4;	// [08 ... 11]
		uint32_t ocecc_poison_egen_mr_rd_1				: 1;	// [12]
		uint32_t ocecc_poison_egen_mr_rd_1_byte_num			: 5;	// [13 ... 17]
		uint32_t ocecc_poison_egen_xpi_rd_0				: 1;	// [18]
		uint32_t ocecc_poison_ecc_corr_uncorr				: 2;	// [19 ... 20]
		uint32_t ocecc_poison_pgen_rd					: 1;	// [21]
		uint32_t ocecc_poison_pgen_mr_wdata				: 1;	// [22]
		uint32_t ocecc_poison_pgen_mr_ecc				: 1;	// [23]
		const uint32_t _RESERVED0					: 8;	// [24 ... 31]
	};
} OCECCCFG1_t;

typedef union tag_OCECCSTAT0 {
	uint32_t value;
	struct {
		const uint32_t ocecc_uncorrected_err				: 1;	// [00]
		const uint32_t ocecc_corrected_err				: 1;	// [01]
		const uint32_t _RESERVED0					: 15;	// [02 ... 16]
		const uint32_t ocecc_err_ddrc_mr_rd				: 1;	// [17]
		const uint32_t par_err_mr_wdata					: 1;	// [18]
		const uint32_t par_err_mr_ecc					: 1;	// [19]
		const uint32_t par_err_rd					: 1;	// [20]
		const uint32_t _RESERVED1					: 11;	// [21 ... 31]
	};
} OCECCSTAT0_t;

typedef union tag_OCECCSTAT1 {
	uint32_t value;
	struct {
		const uint32_t ocecc_err_xpi_wr_in_0				: 1;	// [00]
		const uint32_t ocecc_err_xpi_wr_in_1				: 1;	// [01]
		const uint32_t ocecc_err_xpi_wr_in_2				: 1;	// [02]
		const uint32_t ocecc_err_xpi_wr_in_3				: 1;	// [03]
		const uint32_t ocecc_err_xpi_wr_in_4				: 1;	// [04]
		const uint32_t ocecc_err_xpi_wr_in_5				: 1;	// [05]
		const uint32_t ocecc_err_xpi_wr_in_6				: 1;	// [06]
		const uint32_t ocecc_err_xpi_wr_in_7				: 1;	// [07]
		const uint32_t ocecc_err_xpi_wr_in_8				: 1;	// [08]
		const uint32_t ocecc_err_xpi_wr_in_9				: 1;	// [09]
		const uint32_t ocecc_err_xpi_wr_in_10				: 1;	// [10]
		const uint32_t ocecc_err_xpi_wr_in_11				: 1;	// [11]
		const uint32_t ocecc_err_xpi_wr_in_12				: 1;	// [12]
		const uint32_t ocecc_err_xpi_wr_in_13				: 1;	// [13]
		const uint32_t ocecc_err_xpi_wr_in_14				: 1;	// [14]
		const uint32_t ocecc_err_xpi_wr_in_15				: 1;	// [15]
		const uint32_t ocecc_err_xpi_rd_0				: 1;	// [16]
		const uint32_t ocecc_err_xpi_rd_1				: 1;	// [17]
		const uint32_t ocecc_err_xpi_rd_2				: 1;	// [18]
		const uint32_t ocecc_err_xpi_rd_3				: 1;	// [19]
		const uint32_t ocecc_err_xpi_rd_4				: 1;	// [20]
		const uint32_t ocecc_err_xpi_rd_5				: 1;	// [21]
		const uint32_t ocecc_err_xpi_rd_6				: 1;	// [22]
		const uint32_t ocecc_err_xpi_rd_7				: 1;	// [23]
		const uint32_t ocecc_err_xpi_rd_8				: 1;	// [24]
		const uint32_t ocecc_err_xpi_rd_9				: 1;	// [25]
		const uint32_t ocecc_err_xpi_rd_10				: 1;	// [26]
		const uint32_t ocecc_err_xpi_rd_11				: 1;	// [27]
		const uint32_t ocecc_err_xpi_rd_12				: 1;	// [28]
		const uint32_t ocecc_err_xpi_rd_13				: 1;	// [29]
		const uint32_t ocecc_err_xpi_rd_14				: 1;	// [30]
		const uint32_t ocecc_err_xpi_rd_15				: 1;	// [31]
	};
} OCECCSTAT1_t;

typedef union tag_OCECCSTAT2 {
	uint32_t value;
	struct {
		const uint32_t ocecc_err_ddrc_mr_rd_byte_num			: 32;	// [00 ... 31]
	};
} OCECCSTAT2_t;

typedef union tag_OCCAPCFG {
	uint32_t value;
	struct {
		uint32_t occap_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 15;	// [01 ... 15]
		uint32_t occap_arb_intr_en					: 1;	// [16]
		uint32_t occap_arb_intr_clr					: 1;	// [17]
		uint32_t occap_arb_intr_force					: 1;	// [18]
		const uint32_t _RESERVED1					: 5;	// [19 ... 23]
		uint32_t occap_arb_cmp_poison_seq				: 1;	// [24]
		uint32_t occap_arb_cmp_poison_parallel				: 1;	// [25]
		uint32_t occap_arb_cmp_poison_err_inj				: 1;	// [26]
		uint32_t occap_arb_raq_poison_en				: 1;	// [27]
		const uint32_t _RESERVED2					: 4;	// [28 ... 31]
	};
} OCCAPCFG_t;

typedef union tag_OCCAPSTAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		const uint32_t occap_arb_err_intr				: 1;	// [16]
		const uint32_t occap_arb_cmp_poison_complete			: 1;	// [17]
		const uint32_t _RESERVED1					: 6;	// [18 ... 23]
		const uint32_t occap_arb_cmp_poison_seq_err			: 1;	// [24]
		const uint32_t occap_arb_cmp_poison_parallel_err		: 1;	// [25]
		const uint32_t _RESERVED2					: 6;	// [26 ... 31]
	};
} OCCAPSTAT_t;

typedef union tag_OCCAPCFG1 {
	uint32_t value;
	struct {
		uint32_t occap_ddrc_data_intr_en				: 1;	// [00]
		uint32_t occap_ddrc_data_intr_clr				: 1;	// [01]
		uint32_t occap_ddrc_data_intr_force				: 1;	// [02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		uint32_t occap_ddrc_data_poison_seq				: 1;	// [08]
		uint32_t occap_ddrc_data_poison_parallel			: 1;	// [09]
		uint32_t occap_ddrc_data_poison_err_inj				: 1;	// [10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t occap_ddrc_ctrl_intr_en				: 1;	// [16]
		uint32_t occap_ddrc_ctrl_intr_clr				: 1;	// [17]
		uint32_t occap_ddrc_ctrl_intr_force				: 1;	// [18]
		const uint32_t _RESERVED2					: 5;	// [19 ... 23]
		uint32_t occap_ddrc_ctrl_poison_seq				: 1;	// [24]
		uint32_t occap_ddrc_ctrl_poison_parallel			: 1;	// [25]
		uint32_t occap_ddrc_ctrl_poison_err_inj				: 1;	// [26]
		const uint32_t _RESERVED3					: 5;	// [27 ... 31]
	};
} OCCAPCFG1_t;

typedef union tag_OCCAPSTAT1 {
	uint32_t value;
	struct {
		const uint32_t occap_ddrc_data_err_intr				: 1;	// [00]
		const uint32_t occap_ddrc_data_poison_complete			: 1;	// [01]
		const uint32_t _RESERVED0					: 6;	// [02 ... 07]
		const uint32_t occap_ddrc_data_poison_seq_err			: 1;	// [08]
		const uint32_t occap_ddrc_data_poison_parallel_err		: 1;	// [09]
		const uint32_t _RESERVED1					: 6;	// [10 ... 15]
		const uint32_t occap_ddrc_ctrl_err_intr				: 1;	// [16]
		const uint32_t occap_ddrc_ctrl_poison_complete			: 1;	// [17]
		const uint32_t _RESERVED2					: 6;	// [18 ... 23]
		const uint32_t occap_ddrc_ctrl_poison_seq_err			: 1;	// [24]
		const uint32_t occap_ddrc_ctrl_poison_parallel_err		: 1;	// [25]
		const uint32_t _RESERVED3					: 6;	// [26 ... 31]
	};
} OCCAPSTAT1_t;

typedef union tag_OCCAPCFG2 {
	uint32_t value;
	struct {
		uint32_t occap_dfiic_intr_en					: 1;	// [00]
		uint32_t occap_dfiic_intr_clr					: 1;	// [01]
		uint32_t occap_dfiic_intr_force					: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} OCCAPCFG2_t;

typedef union tag_OCCAPSTAT2 {
	uint32_t value;
	struct {
		const uint32_t occap_dfiic_err_intr				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} OCCAPSTAT2_t;

typedef union tag_CRCPARCTL0 {
	uint32_t value;
	struct {
		uint32_t capar_err_intr_en					: 1;	// [00]
		uint32_t capar_err_intr_clr					: 1;	// [01]
		uint32_t capar_err_intr_force					: 1;	// [02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t capar_err_max_reached_intr_en				: 1;	// [04]
		uint32_t capar_err_max_reached_intr_clr				: 1;	// [05]
		uint32_t capar_err_max_reached_intr_force			: 1;	// [06]
		uint32_t capar_err_cnt_clr					: 1;	// [07]
		uint32_t wr_crc_err_intr_en					: 1;	// [08]
		uint32_t wr_crc_err_intr_clr					: 1;	// [09]
		uint32_t wr_crc_err_intr_force					: 1;	// [10]
		const uint32_t _RESERVED1					: 1;	// [11]
		uint32_t wr_crc_err_max_reached_intr_en				: 1;	// [12]
		uint32_t wr_crc_err_max_reached_intr_clr			: 1;	// [13]
		uint32_t wr_crc_err_max_reached_intr_force			: 1;	// [14]
		uint32_t wr_crc_err_cnt_clr					: 1;	// [15]
		const uint32_t _RESERVED2					: 4;	// [16 ... 19]
		uint32_t rd_crc_err_max_reached_int_en				: 1;	// [20]
		uint32_t rd_crc_err_max_reached_int_clr				: 1;	// [21]
		uint32_t rd_crc_err_cnt_clr					: 1;	// [22]
		uint32_t rd_crc_err_max_reached_intr_force			: 1;	// [23]
		uint32_t capar_fatl_err_intr_en					: 1;	// [24]
		uint32_t capar_fatl_err_intr_clr				: 1;	// [25]
		uint32_t capar_fatl_err_intr_force				: 1;	// [26]
		const uint32_t _RESERVED3					: 5;	// [27 ... 31]
	};
} CRCPARCTL0_t;

typedef union tag_CRCPARCTL1 {
	uint32_t value;
	struct {
		uint32_t parity_enable						: 1;	// [00]
		uint32_t bypass_internal_crc					: 1;	// [01]
		const uint32_t _RESERVED0					: 1;	// [02]
		uint32_t rd_crc_enable						: 1;	// [03]
		uint32_t wr_crc_enable						: 1;	// [04]
		const uint32_t _RESERVED1					: 1;	// [05]
		uint32_t dis_rd_crc_ecc_upr_nibble				: 1;	// [06]
		uint32_t crc_inc_dm						: 1;	// [07]
		const uint32_t _RESERVED2					: 4;	// [08 ... 11]
		uint32_t caparity_disable_before_sr				: 1;	// [12]
		const uint32_t _RESERVED3					: 2;	// [13 ... 14]
		uint32_t dfi_alert_async_mode					: 1;	// [15]
		uint32_t capar_err_max_reached_th				: 12;	// [16 ... 27]
		const uint32_t _RESERVED4					: 4;	// [28 ... 31]
	};
} CRCPARCTL1_t;

typedef union tag_CRCPARCTL2 {
	uint32_t value;
	struct {
		uint32_t wr_crc_err_max_reached_th				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t rd_crc_err_max_reached_th				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCPARCTL2_t;

typedef union tag_CRCPARSTAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		const uint32_t capar_err_intr					: 1;	// [16]
		const uint32_t capar_err_max_reached_intr			: 1;	// [17]
		const uint32_t capar_fatl_err_intr				: 1;	// [18]
		const uint32_t _RESERVED1					: 5;	// [19 ... 23]
		const uint32_t wr_crc_err_intr					: 1;	// [24]
		const uint32_t wr_crc_err_max_reached_intr			: 1;	// [25]
		const uint32_t wr_crc_retry_limit_intr				: 1;	// [26]
		const uint32_t rd_retry_limit_intr				: 1;	// [27]
		const uint32_t capar_retry_limit_reached_intr			: 1;	// [28]
		const uint32_t _RESERVED2					: 3;	// [29 ... 31]
	};
} CRCPARSTAT_t;

typedef union tag_CAPARPOISONCTL {
	uint32_t value;
	struct {
		uint32_t capar_poison_inject_en					: 1;	// [00]
		const uint32_t _RESERVED0					: 7;	// [01 ... 07]
		uint32_t capar_poison_cmdtype					: 2;	// [08 ... 09]
		const uint32_t _RESERVED1					: 2;	// [10 ... 11]
		uint32_t capar_poison_position					: 8;	// [12 ... 19]
		const uint32_t _RESERVED2					: 12;	// [20 ... 31]
	};
} CAPARPOISONCTL_t;

typedef union tag_CAPARPOISONSTAT {
	uint32_t value;
	struct {
		const uint32_t capar_poison_complete				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} CAPARPOISONSTAT_t;

typedef union tag_CRCPOISONCTL0 {
	uint32_t value;
	struct {
		uint32_t crc_poison_inject_en					: 1;	// [00]
		uint32_t crc_poison_type					: 1;	// [01]
		const uint32_t _RESERVED0					: 6;	// [02 ... 07]
		uint32_t crc_poison_nibble					: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t crc_poison_times					: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 11;	// [21 ... 31]
	};
} CRCPOISONCTL0_t;

typedef union tag_CRCPOISONSTAT {
	uint32_t value;
	struct {
		const uint32_t crc_poison_complete				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} CRCPOISONSTAT_t;

typedef union tag_RDCRCERRADDR0 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_row					: 24;	// [00 ... 23]
		const uint32_t rd_crc_err_rank					: 8;	// [24 ... 31]
	};
} RDCRCERRADDR0_t;

typedef union tag_RDCRCERRADDR1 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_col					: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t rd_crc_err_bank					: 8;	// [16 ... 23]
		const uint32_t rd_crc_err_bg					: 4;	// [24 ... 27]
		const uint32_t rd_crc_err_cid					: 4;	// [28 ... 31]
	};
} RDCRCERRADDR1_t;

typedef union tag_RDCRCERRSTAT0 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_max_reached_int_nibble		: 20;	// [00 ... 19]
		const uint32_t _RESERVED0					: 11;	// [20 ... 30]
		const uint32_t rd_crc_err_max_reached_int			: 1;	// [31]
	};
} RDCRCERRSTAT0_t;

typedef union tag_CRCSTAT0 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_0				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_1				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT0_t;

typedef union tag_CRCSTAT1 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_2				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_3				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT1_t;

typedef union tag_CRCSTAT2 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_4				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_5				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT2_t;

typedef union tag_CRCSTAT3 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_6				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_7				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT3_t;

typedef union tag_CRCSTAT4 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_8				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_9				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT4_t;

typedef union tag_CRCSTAT5 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_10				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_11				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT5_t;

typedef union tag_CRCSTAT6 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_12				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_13				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT6_t;

typedef union tag_CRCSTAT7 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_14				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_15				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT7_t;

typedef union tag_CRCSTAT8 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_16				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_17				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT8_t;

typedef union tag_CRCSTAT9 {
	uint32_t value;
	struct {
		const uint32_t rd_crc_err_cnt_nibble_18				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		const uint32_t rd_crc_err_cnt_nibble_19				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} CRCSTAT9_t;

typedef union tag_CRCSTAT10 {
	uint32_t value;
	struct {
		const uint32_t wr_crc_err_cnt					: 12;	// [00 ... 11]
		const uint32_t capar_err_cnt					: 12;	// [12 ... 23]
		const uint32_t _RESERVED0					: 8;	// [24 ... 31]
	};
} CRCSTAT10_t;

typedef union tag_REGPARCFG {
	uint32_t value;
	struct {
		uint32_t reg_par_en						: 1;	// [00]
		uint32_t reg_par_err_intr_en					: 1;	// [01]
		uint32_t reg_par_err_intr_clr					: 1;	// [02]
		uint32_t reg_par_err_intr_force					: 1;	// [03]
		const uint32_t _RESERVED0					: 4;	// [04 ... 07]
		uint32_t reg_par_poison_en					: 1;	// [08]
		const uint32_t _RESERVED1					: 23;	// [09 ... 31]
	};
} REGPARCFG_t;

typedef union tag_REGPARSTAT {
	uint32_t value;
	struct {
		const uint32_t reg_par_err_intr					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} REGPARSTAT_t;

typedef union tag_RETRYCTL0 {
	uint32_t value;
	struct {
		uint32_t capar_retry_enable					: 1;	// [00]
		uint32_t rd_ue_retry_enable					: 1;	// [01]
		uint32_t rd_crc_retry_enable					: 1;	// [02]
		uint32_t wr_crc_retry_enable					: 1;	// [03]
		const uint32_t _RESERVED0					: 4;	// [04 ... 07]
		uint32_t wr_crc_retry_limiter					: 3;	// [08 ... 10]
		uint32_t rd_crc_retry_limiter					: 3;	// [11 ... 13]
		uint32_t rd_ue_retry_limiter					: 3;	// [14 ... 16]
		uint32_t capar_retry_limiter					: 3;	// [17 ... 19]
		uint32_t wr_crc_retry_limit_intr_en				: 1;	// [20]
		uint32_t wr_crc_retry_limit_intr_clr				: 1;	// [21]
		uint32_t wr_crc_retry_limit_intr_force				: 1;	// [22]
		uint32_t rd_retry_limit_intr_en					: 1;	// [23]
		uint32_t rd_retry_limit_intr_clr				: 1;	// [24]
		uint32_t rd_retry_limit_intr_force				: 1;	// [25]
		uint32_t capar_retry_limit_intr_en				: 1;	// [26]
		uint32_t capar_retry_limit_intr_clr				: 1;	// [27]
		uint32_t capar_retry_limit_intr_force				: 1;	// [28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} RETRYCTL0_t;

typedef union tag_RETRYCTL1 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 29;	// [00 ... 28]
		uint32_t make_multi_retry_fatl_err				: 1;	// [29]
		uint32_t dis_capar_selfref_retry				: 1;	// [30]
		uint32_t dis_capar_powerdown_retry				: 1;	// [31]
	};
} RETRYCTL1_t;

typedef union tag_RETRYSTAT0 {
	uint32_t value;
	struct {
		const uint32_t retry_stat					: 2;	// [00 ... 01]
		const uint32_t _RESERVED0					: 5;	// [02 ... 06]
		const uint32_t retry_fifo_fill_level				: 8;	// [07 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		const uint32_t rd_ue_retry_limit_reached			: 1;	// [16]
		const uint32_t rd_crc_retry_limit_reached			: 1;	// [17]
		const uint32_t _RESERVED2					: 6;	// [18 ... 23]
		const uint32_t capar_fatl_err_code				: 6;	// [24 ... 29]
		const uint32_t _RESERVED3					: 2;	// [30 ... 31]
	};
} RETRYSTAT0_t;

typedef union tag_LNKECCCTL1 {
	uint32_t value;
	struct {
		uint32_t rd_link_ecc_corr_intr_en				: 1;	// [00]
		uint32_t rd_link_ecc_corr_intr_clr				: 1;	// [01]
		uint32_t rd_link_ecc_corr_cnt_clr				: 1;	// [02]
		uint32_t rd_link_ecc_corr_intr_force				: 1;	// [03]
		uint32_t rd_link_ecc_uncorr_intr_en				: 1;	// [04]
		uint32_t rd_link_ecc_uncorr_intr_clr				: 1;	// [05]
		uint32_t rd_link_ecc_uncorr_cnt_clr				: 1;	// [06]
		uint32_t rd_link_ecc_uncorr_intr_force				: 1;	// [07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} LNKECCCTL1_t;

typedef union tag_LNKECCPOISONCTL0 {
	uint32_t value;
	struct {
		uint32_t linkecc_poison_inject_en				: 1;	// [00]
		uint32_t linkecc_poison_type					: 1;	// [01]
		uint32_t linkecc_poison_rw					: 1;	// [02]
		const uint32_t _RESERVED0					: 13;	// [03 ... 15]
		uint32_t linkecc_poison_dmi_sel					: 8;	// [16 ... 23]
		uint32_t linkecc_poison_byte_sel				: 8;	// [24 ... 31]
	};
} LNKECCPOISONCTL0_t;

typedef union tag_LNKECCPOISONSTAT {
	uint32_t value;
	struct {
		const uint32_t linkecc_poison_complete				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} LNKECCPOISONSTAT_t;

typedef union tag_LNKECCINDEX {
	uint32_t value;
	struct {
		uint32_t rd_link_ecc_err_byte_sel				: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t rd_link_ecc_err_rank_sel				: 2;	// [04 ... 05]
		const uint32_t _RESERVED1					: 26;	// [06 ... 31]
	};
} LNKECCINDEX_t;

typedef union tag_LNKECCERRCNT0 {
	uint32_t value;
	struct {
		const uint32_t rd_link_ecc_err_syndrome				: 9;	// [00 ... 08]
		const uint32_t _RESERVED0					: 7;	// [09 ... 15]
		const uint32_t rd_link_ecc_corr_cnt				: 8;	// [16 ... 23]
		const uint32_t rd_link_ecc_uncorr_cnt				: 8;	// [24 ... 31]
	};
} LNKECCERRCNT0_t;

typedef union tag_LNKECCERRSTAT {
	uint32_t value;
	struct {
		const uint32_t rd_link_ecc_corr_err_int				: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 4;	// [04 ... 07]
		const uint32_t rd_link_ecc_uncorr_err_int			: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 20;	// [12 ... 31]
	};
} LNKECCERRSTAT_t;

typedef union tag_EAPARCTL0 {
	uint32_t value;
	struct {
		uint32_t eapar_err_intr_en					: 1;	// [00]
		uint32_t eapar_err_intr_clr					: 1;	// [01]
		uint32_t eapar_err_intr_force					: 1;	// [02]
		uint32_t eapar_err_cnt_clr					: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} EAPARCTL0_t;

typedef union tag_EAPARSTAT0 {
	uint32_t value;
	struct {
		const uint32_t eapar_error					: 16;	// [00 ... 15]
		const uint32_t eapar_err_sbr_rd					: 1;	// [16]
		const uint32_t _RESERVED0					: 15;	// [17 ... 31]
	};
} EAPARSTAT0_t;

typedef union tag_EAPARERRCNT {
	uint32_t value;
	struct {
		const uint32_t eapar_err_cnt					: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} EAPARERRCNT_t;

typedef union tag_EAPARADDR0 {
	uint32_t value;
	struct {
		const uint32_t eapar_err_row					: 24;	// [00 ... 23]
		const uint32_t eapar_err_rank					: 8;	// [24 ... 31]
	};
} EAPARADDR0_t;

typedef union tag_EAPARADDR1 {
	uint32_t value;
	struct {
		const uint32_t eapar_err_col					: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t eapar_err_bank					: 8;	// [16 ... 23]
		const uint32_t eapar_err_bg					: 4;	// [24 ... 27]
		const uint32_t eapar_err_cid					: 4;	// [28 ... 31]
	};
} EAPARADDR1_t;

typedef union tag_EAPARSYN0 {
	uint32_t value;
	struct {
		const uint32_t eapar_err_syndromes_31_0				: 32;	// [00 ... 31]
	};
} EAPARSYN0_t;

typedef union tag_EAPARSYN1 {
	uint32_t value;
	struct {
		const uint32_t eapar_err_syndromes_63_32			: 32;	// [00 ... 31]
	};
} EAPARSYN1_t;

typedef union tag_EAPARSYN2 {
	uint32_t value;
	struct {
		const uint32_t eapar_err_syndromes_71_64			: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t eapar_err_cb_syndrome				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} EAPARSYN2_t;

typedef union tag_LNKECCCADDR0 {
	uint32_t value;
	struct {
		const uint32_t link_ecc_corr_row				: 24;	// [00 ... 23]
		const uint32_t link_ecc_corr_rank				: 8;	// [24 ... 31]
	};
} LNKECCCADDR0_t;

typedef union tag_LNKECCCADDR1 {
	uint32_t value;
	struct {
		const uint32_t link_ecc_corr_col				: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t link_ecc_corr_bank				: 8;	// [16 ... 23]
		const uint32_t link_ecc_corr_bg					: 8;	// [24 ... 31]
	};
} LNKECCCADDR1_t;

typedef union tag_LNKECCUADDR0 {
	uint32_t value;
	struct {
		const uint32_t link_ecc_uncorr_row				: 24;	// [00 ... 23]
		const uint32_t link_ecc_uncorr_rank				: 8;	// [24 ... 31]
	};
} LNKECCUADDR0_t;

typedef union tag_LNKECCUADDR1 {
	uint32_t value;
	struct {
		const uint32_t link_ecc_uncorr_col				: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 5;	// [11 ... 15]
		const uint32_t link_ecc_uncorr_bank				: 8;	// [16 ... 23]
		const uint32_t link_ecc_uncorr_bg				: 8;	// [24 ... 31]
	};
} LNKECCUADDR1_t;

typedef union tag_PASCTL0 {
	uint32_t value;
	struct {
		uint32_t init_done						: 1;	// [00]
		uint32_t dbg_st_en						: 1;	// [01]
		uint32_t bist_st_en						: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} PASCTL0_t;

typedef union tag_PASCTL1 {
	uint32_t value;
	struct {
		uint32_t pre_sb_enable						: 1;	// [00]
		uint32_t pre_ab_enable						: 1;	// [01]
		uint32_t pre_slot_config					: 2;	// [02 ... 03]
		uint32_t wr_min_gap						: 4;	// [04 ... 07]
		uint32_t rd_min_gap						: 4;	// [08 ... 11]
		uint32_t rank_switch_gap_unit_sel				: 1;	// [12]
		uint32_t mrr_des_timing_unit_sel				: 2;	// [13 ... 14]
		const uint32_t _RESERVED0					: 3;	// [15 ... 17]
		uint32_t selfref_wo_ref_pending					: 1;	// [18]
		uint32_t dfi_alert_assertion_mode				: 1;	// [19]
		uint32_t speculative_ref_pri_sel				: 1;	// [20]
		uint32_t dyn_pre_pri_dis					: 1;	// [21]
		uint32_t fixed_pre_pri_sel					: 1;	// [22]
		uint32_t blk_act_en						: 1;	// [23]
		uint32_t act2rda_cnt_mask					: 1;	// [24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} PASCTL1_t;

typedef union tag_PASCTL2 {
	uint32_t value;
	struct {
		uint32_t dyn_pre_pri_hi_win_size				: 8;	// [00 ... 07]
		uint32_t dyn_pre_pri_lo_wait_thr				: 8;	// [08 ... 15]
		uint32_t lrank_rd2rd_gap					: 3;	// [16 ... 18]
		uint32_t lrank_wr2wr_gap					: 3;	// [19 ... 21]
		const uint32_t _RESERVED0					: 2;	// [22 ... 23]
		uint32_t refsb_hi_wait_thr					: 6;	// [24 ... 29]
		uint32_t t_ppd_cnt_en						: 1;	// [30]
		const uint32_t _RESERVED1					: 1;	// [31]
	};
} PASCTL2_t;

typedef union tag_PASCTL3 {
	uint32_t value;
	struct {
		uint32_t dimm_t_dcaw						: 8;	// [00 ... 07]
		uint32_t dimm_n_dcac_m1						: 5;	// [08 ... 12]
		const uint32_t _RESERVED0					: 1;	// [13]
		uint32_t dimm_dcaw_en						: 2;	// [14 ... 15]
		uint32_t enable_trfc_dpr					: 3;	// [16 ... 18]
		const uint32_t _RESERVED1					: 13;	// [19 ... 31]
	};
} PASCTL3_t;

typedef union tag_PASCTL4 {
	uint32_t value;
	struct {
		uint32_t ci_mrr_des1						: 4;	// [00 ... 03]
		uint32_t ci_mrr_des2						: 4;	// [04 ... 07]
		uint32_t ci_mrw_des1						: 4;	// [08 ... 11]
		uint32_t ci_mrw_des2						: 4;	// [12 ... 15]
		uint32_t ci_mpc_des1						: 4;	// [16 ... 19]
		uint32_t ci_mpc_des2						: 4;	// [20 ... 23]
		uint32_t ci_rfm_des1						: 4;	// [24 ... 27]
		uint32_t ci_rfm_des2						: 4;	// [28 ... 31]
	};
} PASCTL4_t;

typedef union tag_PASCTL5 {
	uint32_t value;
	struct {
		uint32_t base_timer_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} PASCTL5_t;

typedef union tag_PASCTL6 {
	uint32_t value;
	struct {
		uint32_t base_timer						: 32;	// [00 ... 31]
	};
} PASCTL6_t;

typedef union tag_PASCTL7 {
	uint32_t value;
	struct {
		uint32_t glb_blk0_en						: 1;	// [00]
		uint32_t glb_blk1_en						: 1;	// [01]
		uint32_t glb_blk2_en						: 1;	// [02]
		uint32_t glb_blk3_en						: 1;	// [03]
		uint32_t glb_blk4_en						: 1;	// [04]
		uint32_t glb_blk5_en						: 1;	// [05]
		uint32_t glb_blk6_en						: 1;	// [06]
		uint32_t glb_blk7_en						: 1;	// [07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} PASCTL7_t;

typedef union tag_PASCTL8 {
	uint32_t value;
	struct {
		uint32_t rank_blk0_en						: 1;	// [00]
		uint32_t rank_blk1_en						: 1;	// [01]
		uint32_t rank_blk2_en						: 1;	// [02]
		uint32_t rank_blk3_en						: 1;	// [03]
		uint32_t rank_blk4_en						: 1;	// [04]
		uint32_t rank_blk5_en						: 1;	// [05]
		uint32_t rank_blk6_en						: 1;	// [06]
		uint32_t rank_blk7_en						: 1;	// [07]
		uint32_t rank_blk8_en						: 1;	// [08]
		uint32_t rank_blk9_en						: 1;	// [09]
		uint32_t rank_blk10_en						: 1;	// [10]
		uint32_t rank_blk11_en						: 1;	// [11]
		uint32_t rank_blk12_en						: 1;	// [12]
		uint32_t rank_blk13_en						: 1;	// [13]
		uint32_t rank_blk14_en						: 1;	// [14]
		uint32_t rank_blk15_en						: 1;	// [15]
		uint32_t rank_blk16_en						: 1;	// [16]
		uint32_t rank_blk17_en						: 1;	// [17]
		uint32_t rank_blk18_en						: 1;	// [18]
		uint32_t rank_blk19_en						: 1;	// [19]
		uint32_t rank_blk20_en						: 1;	// [20]
		uint32_t rank_blk21_en						: 1;	// [21]
		uint32_t rank_blk22_en						: 1;	// [22]
		uint32_t rank_blk23_en						: 1;	// [23]
		uint32_t rank_blk24_en						: 1;	// [24]
		uint32_t rank_blk25_en						: 1;	// [25]
		uint32_t rank_blk26_en						: 1;	// [26]
		uint32_t rank_blk27_en						: 1;	// [27]
		uint32_t rank_blk28_en						: 1;	// [28]
		uint32_t rank_blk29_en						: 1;	// [29]
		uint32_t rank_blk30_en						: 1;	// [30]
		uint32_t rank_blk31_en						: 1;	// [31]
	};
} PASCTL8_t;

typedef union tag_PASCTL9 {
	uint32_t value;
	struct {
		uint32_t glb_blk0_trig						: 1;	// [00]
		uint32_t glb_blk1_trig						: 1;	// [01]
		uint32_t glb_blk2_trig						: 1;	// [02]
		uint32_t glb_blk3_trig						: 1;	// [03]
		uint32_t glb_blk4_trig						: 1;	// [04]
		uint32_t glb_blk5_trig						: 1;	// [05]
		uint32_t glb_blk6_trig						: 1;	// [06]
		uint32_t glb_blk7_trig						: 1;	// [07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} PASCTL9_t;

typedef union tag_PASCTL10 {
	uint32_t value;
	struct {
		uint32_t rank_blk0_trig						: 1;	// [00]
		uint32_t rank_blk1_trig						: 1;	// [01]
		uint32_t rank_blk2_trig						: 1;	// [02]
		uint32_t rank_blk3_trig						: 1;	// [03]
		uint32_t rank_blk4_trig						: 1;	// [04]
		uint32_t rank_blk5_trig						: 1;	// [05]
		uint32_t rank_blk6_trig						: 1;	// [06]
		uint32_t rank_blk7_trig						: 1;	// [07]
		uint32_t rank_blk8_trig						: 1;	// [08]
		uint32_t rank_blk9_trig						: 1;	// [09]
		uint32_t rank_blk10_trig					: 1;	// [10]
		uint32_t rank_blk11_trig					: 1;	// [11]
		uint32_t rank_blk12_trig					: 1;	// [12]
		uint32_t rank_blk13_trig					: 1;	// [13]
		uint32_t rank_blk14_trig					: 1;	// [14]
		uint32_t rank_blk15_trig					: 1;	// [15]
		uint32_t rank_blk16_trig					: 1;	// [16]
		uint32_t rank_blk17_trig					: 1;	// [17]
		uint32_t rank_blk18_trig					: 1;	// [18]
		uint32_t rank_blk19_trig					: 1;	// [19]
		uint32_t rank_blk20_trig					: 1;	// [20]
		uint32_t rank_blk21_trig					: 1;	// [21]
		uint32_t rank_blk22_trig					: 1;	// [22]
		uint32_t rank_blk23_trig					: 1;	// [23]
		uint32_t rank_blk24_trig					: 1;	// [24]
		uint32_t rank_blk25_trig					: 1;	// [25]
		uint32_t rank_blk26_trig					: 1;	// [26]
		uint32_t rank_blk27_trig					: 1;	// [27]
		uint32_t rank_blk28_trig					: 1;	// [28]
		uint32_t rank_blk29_trig					: 1;	// [29]
		uint32_t rank_blk30_trig					: 1;	// [30]
		uint32_t rank_blk31_trig					: 1;	// [31]
	};
} PASCTL10_t;

typedef union tag_PASCTL11 {
	uint32_t value;
	struct {
		uint32_t powerdown_entry_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_entry_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL11_t;

typedef union tag_PASCTL12 {
	uint32_t value;
	struct {
		uint32_t powerdown_exit_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_exit_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL12_t;

typedef union tag_PASCTL13 {
	uint32_t value;
	struct {
		uint32_t powerdown_entry_ba_1					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_entry_size_1					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL13_t;

typedef union tag_PASCTL14 {
	uint32_t value;
	struct {
		uint32_t powerdown_exit_ba_1					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_exit_size_1					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL14_t;

typedef union tag_PASCTL15 {
	uint32_t value;
	struct {
		uint32_t powerdown_entry_ba_2					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_entry_size_2					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL15_t;

typedef union tag_PASCTL16 {
	uint32_t value;
	struct {
		uint32_t powerdown_exit_ba_2					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_exit_size_2					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL16_t;

typedef union tag_PASCTL17 {
	uint32_t value;
	struct {
		uint32_t powerdown_entry_ba_3					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_entry_size_3					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL17_t;

typedef union tag_PASCTL18 {
	uint32_t value;
	struct {
		uint32_t powerdown_exit_ba_3					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t powerdown_exit_size_3					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL18_t;

typedef union tag_PASCTL19 {
	uint32_t value;
	struct {
		const uint32_t prank0_mode					: 8;	// [00 ... 07]
		const uint32_t prank1_mode					: 8;	// [08 ... 15]
		const uint32_t prank2_mode					: 8;	// [16 ... 23]
		const uint32_t prank3_mode					: 8;	// [24 ... 31]
	};
} PASCTL19_t;

typedef union tag_PASCTL20 {
	uint32_t value;
	struct {
		uint32_t selfref_entry1_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t selfref_entry1_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL20_t;

typedef union tag_PASCTL21 {
	uint32_t value;
	struct {
		uint32_t selfref_entry2_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t selfref_entry2_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL21_t;

typedef union tag_PASCTL22 {
	uint32_t value;
	struct {
		uint32_t selfref_exit1_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t selfref_exit1_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL22_t;

typedef union tag_PASCTL23 {
	uint32_t value;
	struct {
		uint32_t selfref_exit2_ba_0					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t selfref_exit2_size_0					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} PASCTL23_t;

typedef union tag_PASCTL24 {
	uint32_t value;
	struct {
		uint32_t rfm_raa_en						: 4;	// [00 ... 03]
		uint32_t rfm_raa_reset						: 4;	// [04 ... 07]
		uint32_t rfm_raa_use_ecs_refab					: 1;	// [08]
		const uint32_t _RESERVED0					: 7;	// [09 ... 15]
		uint32_t rfm_alert_thr						: 16;	// [16 ... 31]
	};
} PASCTL24_t;

typedef union tag_PASCTL25 {
	uint32_t value;
	struct {
		const uint32_t rfm_cmd_log					: 32;	// [00 ... 31]
	};
} PASCTL25_t;

typedef union tag_PASCTL26 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t capar_retry_size					: 6;	// [16 ... 21]
		const uint32_t _RESERVED1					: 10;	// [22 ... 31]
	};
} PASCTL26_t;

typedef union tag_PASCTL36 {
	uint32_t value;
	struct {
		uint32_t powerdown_idle_ctrl_0					: 2;	// [00 ... 01]
		uint32_t powerdown_idle_ctrl_1					: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} PASCTL36_t;

typedef union tag_PASCTL37 {
	uint32_t value;
	struct {
		uint32_t dch_sync_mode						: 1;	// [00]
		uint32_t dch_ch0_mask						: 1;	// [01]
		const uint32_t _RESERVED0					: 14;	// [02 ... 15]
		uint32_t t_selfref_exit_stagger					: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} PASCTL37_t;

typedef union tag_PASCTL38 {
	uint32_t value;
	struct {
		uint32_t bwl_win_len						: 10;	// [00 ... 09]
		uint32_t bwl_en_len						: 10;	// [10 ... 19]
		const uint32_t _RESERVED0					: 10;	// [20 ... 29]
		uint32_t bwl_ctrl						: 1;	// [30]
		uint32_t bwl_en							: 1;	// [31]
	};
} PASCTL38_t;

typedef union tag_ECSCTL {
	uint32_t value;
	struct {
		uint32_t auto_ecs_refab_en					: 32;	// [00 ... 31]
	};
} ECSCTL_t;

typedef union tag_ECS_STAT_DEV_SEL {
	uint32_t value;
	struct {
		uint32_t target_ecs_mrr_device_idx				: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 27;	// [05 ... 31]
	};
} ECS_STAT_DEV_SEL_t;

typedef union tag_ECS_STAT_MR0 {
	uint32_t value;
	struct {
		const uint32_t ecs_mr16						: 8;	// [00 ... 07]
		const uint32_t ecs_mr17						: 8;	// [08 ... 15]
		const uint32_t ecs_mr18						: 8;	// [16 ... 23]
		const uint32_t ecs_mr19						: 8;	// [24 ... 31]
	};
} ECS_STAT_MR0_t;

typedef union tag_ECS_STAT_MR1 {
	uint32_t value;
	struct {
		const uint32_t ecs_mr20						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} ECS_STAT_MR1_t;

typedef union tag_CMDCFG {
	uint32_t value;
	struct {
		uint32_t cmd_type						: 1;	// [00]
		uint32_t multi_cyc_cs_en					: 1;	// [01]
		uint32_t pde_odt_ctrl						: 1;	// [02]
		uint32_t pd_mrr_nt_odt_en					: 1;	// [03]
		uint32_t cmd_timer_x32						: 12;	// [04 ... 15]
		uint32_t mrr_grp_sel						: 3;	// [16 ... 18]
		const uint32_t _RESERVED0					: 2;	// [19 ... 20]
		uint32_t ctrlupd_retry_thr					: 4;	// [21 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} CMDCFG_t;

typedef union tag_CMDCTL {
	uint32_t value;
	struct {
		uint32_t cmd_ctrl						: 24;	// [00 ... 23]
		uint32_t cmd_code						: 5;	// [24 ... 28]
		uint32_t cmd_seq_ongoing					: 1;	// [29]
		uint32_t cmd_seq_last						: 1;	// [30]
		uint32_t cmd_start						: 1;	// [31]
	};
} CMDCTL_t;

typedef union tag_CMDEXTCTL {
	uint32_t value;
	struct {
		uint32_t cmd_ext_ctrl						: 32;	// [00 ... 31]
	};
} CMDEXTCTL_t;

typedef union tag_CMDSTAT {
	uint32_t value;
	struct {
		const uint32_t mrr_data_vld					: 1;	// [00]
		const uint32_t rd_data_vld					: 1;	// [01]
		const uint32_t ddr5_2n_mode					: 1;	// [02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		const uint32_t swcmd_lock					: 1;	// [08]
		const uint32_t ducmd_lock					: 1;	// [09]
		const uint32_t lccmd_lock					: 1;	// [10]
		const uint32_t _RESERVED1					: 1;	// [11]
		const uint32_t cmd_rslt						: 18;	// [12 ... 29]
		const uint32_t cmd_err						: 1;	// [30]
		const uint32_t cmd_done						: 1;	// [31]
	};
} CMDSTAT_t;

typedef union tag_CMDMRRDATA {
	uint32_t value;
	struct {
		const uint32_t cmd_mrr_data					: 32;	// [00 ... 31]
	};
} CMDMRRDATA_t;

typedef union tag_PASINT {
	uint32_t value;
	struct {
		const uint32_t swcmd_err_intr					: 1;	// [00]
		const uint32_t ducmd_err_intr					: 1;	// [01]
		const uint32_t lccmd_err_intr					: 1;	// [02]
		const uint32_t ctrlupd_err_intr					: 1;	// [03]
		const uint32_t rfm_alert_intr					: 1;	// [04]
		const uint32_t caparcmd_err_intr				: 1;	// [05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} PASINT_t;

typedef union tag_PASINTCTL {
	uint32_t value;
	struct {
		uint32_t swcmd_err_intr_en					: 1;	// [00]
		uint32_t swcmd_err_intr_clr					: 1;	// [01]
		uint32_t swcmd_err_intr_force					: 1;	// [02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t ducmd_err_intr_en					: 1;	// [04]
		uint32_t ducmd_err_intr_clr					: 1;	// [05]
		uint32_t ducmd_err_intr_force					: 1;	// [06]
		const uint32_t _RESERVED1					: 1;	// [07]
		uint32_t lccmd_err_intr_en					: 1;	// [08]
		uint32_t lccmd_err_intr_clr					: 1;	// [09]
		uint32_t lccmd_err_intr_force					: 1;	// [10]
		const uint32_t _RESERVED2					: 1;	// [11]
		uint32_t ctrlupd_err_intr_en					: 1;	// [12]
		uint32_t ctrlupd_err_intr_clr					: 1;	// [13]
		uint32_t ctrlupd_err_intr_force					: 1;	// [14]
		const uint32_t _RESERVED3					: 1;	// [15]
		uint32_t rfm_alert_intr_en					: 1;	// [16]
		uint32_t rfm_alert_intr_clr					: 1;	// [17]
		uint32_t rfm_alert_intr_force					: 1;	// [18]
		const uint32_t _RESERVED4					: 1;	// [19]
		uint32_t caparcmd_err_intr_en					: 1;	// [20]
		uint32_t caparcmd_err_intr_clr					: 1;	// [21]
		uint32_t caparcmd_err_intr_force				: 1;	// [22]
		const uint32_t _RESERVED5					: 9;	// [23 ... 31]
	};
} PASINTCTL_t;

typedef union tag_PASERRSTS {
	uint32_t value;
	struct {
		const uint32_t swcmd_err_sts					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t ducmd_err_sts					: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t lccmd_err_sts					: 3;	// [08 ... 10]
		const uint32_t _RESERVED2					: 1;	// [11]
		const uint32_t caparcmd_err_sts					: 3;	// [12 ... 14]
		const uint32_t _RESERVED3					: 17;	// [15 ... 31]
	};
} PASERRSTS_t;

typedef union tag_DU_CFGBUF_CTRL {
	uint32_t value;
	struct {
		uint32_t du_cfgbuf_wdata					: 16;	// [00 ... 15]
		uint32_t du_cfgbuf_addr						: 8;	// [16 ... 23]
		uint32_t du_cfgbuf_select					: 1;	// [24]
		const uint32_t _RESERVED0					: 4;	// [25 ... 28]
		uint32_t du_cfgbuf_op_mode					: 1;	// [29]
		uint32_t du_cfgbuf_rw_type					: 1;	// [30]
		uint32_t du_cfgbuf_rw_start					: 1;	// [31]
	};
} DU_CFGBUF_CTRL_t;

typedef union tag_DU_CFGBUF_STAT {
	uint32_t value;
	struct {
		const uint32_t du_cfgbuf_rdata					: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} DU_CFGBUF_STAT_t;

typedef union tag_DU_CMDBUF_CTRL {
	uint32_t value;
	struct {
		uint32_t du_cmdbuf_wdata					: 16;	// [00 ... 15]
		uint32_t du_cmdbuf_addr						: 8;	// [16 ... 23]
		uint32_t du_cmdbuf_select					: 1;	// [24]
		const uint32_t _RESERVED0					: 4;	// [25 ... 28]
		uint32_t du_cmdbuf_op_mode					: 1;	// [29]
		uint32_t du_cmdbuf_rw_type					: 1;	// [30]
		uint32_t du_cmdbuf_rw_start					: 1;	// [31]
	};
} DU_CMDBUF_CTRL_t;

typedef union tag_DU_CMDBUF_STAT {
	uint32_t value;
	struct {
		const uint32_t du_cmdbuf_rdata					: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} DU_CMDBUF_STAT_t;

typedef union tag_LP_CMDBUF_CTRL {
	uint32_t value;
	struct {
		uint32_t lp_cmdbuf_wdata					: 16;	// [00 ... 15]
		uint32_t lp_cmdbuf_addr						: 8;	// [16 ... 23]
		const uint32_t _RESERVED0					: 5;	// [24 ... 28]
		uint32_t lp_cmdbuf_op_mode					: 1;	// [29]
		uint32_t lp_cmdbuf_rw_type					: 1;	// [30]
		uint32_t lp_cmdbuf_rw_start					: 1;	// [31]
	};
} LP_CMDBUF_CTRL_t;

typedef union tag_LP_CMDBUF_STAT {
	uint32_t value;
	struct {
		const uint32_t lp_cmdbuf_rdata					: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} LP_CMDBUF_STAT_t;

typedef union tag_RW_CMD_CTRL {
	uint32_t value;
	struct {
		uint32_t wr_data_cb						: 8;	// [00 ... 07]
		uint32_t wr_data_dq_mask					: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 4;	// [16 ... 19]
		uint32_t wr_data_cb_mask					: 1;	// [20]
		uint32_t data_ecc_sel						: 1;	// [21]
		uint32_t rw_ecc_en						: 1;	// [22]
		uint32_t wr_data_sel						: 1;	// [23]
		uint32_t buf_addr						: 4;	// [24 ... 27]
		const uint32_t _RESERVED1					: 2;	// [28 ... 29]
		uint32_t buf_rw_op_type						: 1;	// [30]
		uint32_t buf_rw_start						: 1;	// [31]
	};
} RW_CMD_CTRL_t;

typedef union tag_RW_WR_DATA0 {
	uint32_t value;
	struct {
		uint32_t wr_data_dq0						: 32;	// [00 ... 31]
	};
} RW_WR_DATA0_t;

typedef union tag_RW_WR_DATA1 {
	uint32_t value;
	struct {
		uint32_t wr_data_dq1						: 32;	// [00 ... 31]
	};
} RW_WR_DATA1_t;

typedef union tag_RW_RD_DATA0 {
	uint32_t value;
	struct {
		const uint32_t rd_data_dq0					: 32;	// [00 ... 31]
	};
} RW_RD_DATA0_t;

typedef union tag_RW_RD_DATA1 {
	uint32_t value;
	struct {
		const uint32_t rd_data_dq1					: 32;	// [00 ... 31]
	};
} RW_RD_DATA1_t;

typedef union tag_CAPAR_CMDBUF_CTRL {
	uint32_t value;
	struct {
		uint32_t capar_cmdbuf_wdata					: 16;	// [00 ... 15]
		uint32_t capar_cmdbuf_addr					: 6;	// [16 ... 21]
		const uint32_t _RESERVED0					: 7;	// [22 ... 28]
		uint32_t capar_cmdbuf_op_mode					: 1;	// [29]
		uint32_t capar_cmdbuf_rw_type					: 1;	// [30]
		uint32_t capar_cmdbuf_rw_start					: 1;	// [31]
	};
} CAPAR_CMDBUF_CTRL_t;

typedef union tag_CAPAR_CMDBUF_STAT {
	uint32_t value;
	struct {
		const uint32_t capar_cmdbuf_rdata				: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} CAPAR_CMDBUF_STAT_t;

typedef union tag_OPCTRL0 {
	uint32_t value;
	struct {
		uint32_t dis_wc							: 1;	// [00]
		uint32_t dis_rd_bypass						: 1;	// [01]
		uint32_t dis_act_bypass						: 1;	// [02]
		const uint32_t _RESERVED0					: 3;	// [03 ... 05]
		uint32_t dis_max_rank_rd_opt					: 1;	// [06]
		uint32_t dis_max_rank_wr_opt					: 1;	// [07]
		const uint32_t _RESERVED1					: 24;	// [08 ... 31]
	};
} OPCTRL0_t;

typedef union tag_OPCTRL1 {
	uint32_t value;
	struct {
		uint32_t dis_dq							: 1;	// [00]
		uint32_t dis_hif						: 1;	// [01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} OPCTRL1_t;

typedef union tag_OPCTRLCAM {
	uint32_t value;
	struct {
		const uint32_t dbg_hpr_q_depth					: 8;	// [00 ... 07]
		const uint32_t dbg_lpr_q_depth					: 8;	// [08 ... 15]
		const uint32_t dbg_w_q_depth					: 8;	// [16 ... 23]
		const uint32_t dbg_stall					: 1;	// [24]
		const uint32_t dbg_rd_q_empty					: 1;	// [25]
		const uint32_t dbg_wr_q_empty					: 1;	// [26]
		const uint32_t _RESERVED0					: 1;	// [27]
		const uint32_t rd_data_pipeline_empty				: 1;	// [28]
		const uint32_t wr_data_pipeline_empty				: 1;	// [29]
		const uint32_t dbg_stall_wr					: 1;	// [30]
		const uint32_t dbg_stall_rd					: 1;	// [31]
	};
} OPCTRLCAM_t;

typedef union tag_OPCTRLCMD {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t zq_calib_short						: 1;	// [16]
		uint32_t ctrlupd						: 1;	// [17]
		uint32_t ctrlupd_burst						: 1;	// [18]
		const uint32_t _RESERVED1					: 12;	// [19 ... 30]
		uint32_t hw_ref_zq_en						: 1;	// [31]
	};
} OPCTRLCMD_t;

typedef union tag_OPCTRLSTAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		const uint32_t zq_calib_short_busy				: 1;	// [16]
		const uint32_t ctrlupd_busy					: 1;	// [17]
		const uint32_t ctrlupd_burst_busy				: 1;	// [18]
		const uint32_t _RESERVED1					: 13;	// [19 ... 31]
	};
} OPCTRLSTAT_t;

typedef union tag_OPCTRLCAM1 {
	uint32_t value;
	struct {
		const uint32_t dbg_wrecc_q_depth				: 32;	// [00 ... 31]
	};
} OPCTRLCAM1_t;

typedef union tag_OPREFCTRL0 {
	uint32_t value;
	struct {
		uint32_t rank0_refresh						: 1;	// [00]
		uint32_t rank1_refresh						: 1;	// [01]
		uint32_t rank2_refresh						: 1;	// [02]
		uint32_t rank3_refresh						: 1;	// [03]
		uint32_t rank4_refresh						: 1;	// [04]
		uint32_t rank5_refresh						: 1;	// [05]
		uint32_t rank6_refresh						: 1;	// [06]
		uint32_t rank7_refresh						: 1;	// [07]
		uint32_t rank8_refresh						: 1;	// [08]
		uint32_t rank9_refresh						: 1;	// [09]
		uint32_t rank10_refresh						: 1;	// [10]
		uint32_t rank11_refresh						: 1;	// [11]
		uint32_t rank12_refresh						: 1;	// [12]
		uint32_t rank13_refresh						: 1;	// [13]
		uint32_t rank14_refresh						: 1;	// [14]
		uint32_t rank15_refresh						: 1;	// [15]
		uint32_t rank16_refresh						: 1;	// [16]
		uint32_t rank17_refresh						: 1;	// [17]
		uint32_t rank18_refresh						: 1;	// [18]
		uint32_t rank19_refresh						: 1;	// [19]
		uint32_t rank20_refresh						: 1;	// [20]
		uint32_t rank21_refresh						: 1;	// [21]
		uint32_t rank22_refresh						: 1;	// [22]
		uint32_t rank23_refresh						: 1;	// [23]
		uint32_t rank24_refresh						: 1;	// [24]
		uint32_t rank25_refresh						: 1;	// [25]
		uint32_t rank26_refresh						: 1;	// [26]
		uint32_t rank27_refresh						: 1;	// [27]
		uint32_t rank28_refresh						: 1;	// [28]
		uint32_t rank29_refresh						: 1;	// [29]
		uint32_t rank30_refresh						: 1;	// [30]
		uint32_t rank31_refresh						: 1;	// [31]
	};
} OPREFCTRL0_t;

typedef union tag_OPREFCTRL1 {
	uint32_t value;
	struct {
		uint32_t rank32_refresh						: 1;	// [00]
		uint32_t rank33_refresh						: 1;	// [01]
		uint32_t rank34_refresh						: 1;	// [02]
		uint32_t rank35_refresh						: 1;	// [03]
		uint32_t rank36_refresh						: 1;	// [04]
		uint32_t rank37_refresh						: 1;	// [05]
		uint32_t rank38_refresh						: 1;	// [06]
		uint32_t rank39_refresh						: 1;	// [07]
		uint32_t rank40_refresh						: 1;	// [08]
		uint32_t rank41_refresh						: 1;	// [09]
		uint32_t rank42_refresh						: 1;	// [10]
		uint32_t rank43_refresh						: 1;	// [11]
		uint32_t rank44_refresh						: 1;	// [12]
		uint32_t rank45_refresh						: 1;	// [13]
		uint32_t rank46_refresh						: 1;	// [14]
		uint32_t rank47_refresh						: 1;	// [15]
		uint32_t rank48_refresh						: 1;	// [16]
		uint32_t rank49_refresh						: 1;	// [17]
		uint32_t rank50_refresh						: 1;	// [18]
		uint32_t rank51_refresh						: 1;	// [19]
		uint32_t rank52_refresh						: 1;	// [20]
		uint32_t rank53_refresh						: 1;	// [21]
		uint32_t rank54_refresh						: 1;	// [22]
		uint32_t rank55_refresh						: 1;	// [23]
		uint32_t rank56_refresh						: 1;	// [24]
		uint32_t rank57_refresh						: 1;	// [25]
		uint32_t rank58_refresh						: 1;	// [26]
		uint32_t rank59_refresh						: 1;	// [27]
		uint32_t rank60_refresh						: 1;	// [28]
		uint32_t rank61_refresh						: 1;	// [29]
		uint32_t rank62_refresh						: 1;	// [30]
		uint32_t rank63_refresh						: 1;	// [31]
	};
} OPREFCTRL1_t;

typedef union tag_OPREFSTAT0 {
	uint32_t value;
	struct {
		const uint32_t rank0_refresh_busy				: 1;	// [00]
		const uint32_t rank1_refresh_busy				: 1;	// [01]
		const uint32_t rank2_refresh_busy				: 1;	// [02]
		const uint32_t rank3_refresh_busy				: 1;	// [03]
		const uint32_t rank4_refresh_busy				: 1;	// [04]
		const uint32_t rank5_refresh_busy				: 1;	// [05]
		const uint32_t rank6_refresh_busy				: 1;	// [06]
		const uint32_t rank7_refresh_busy				: 1;	// [07]
		const uint32_t rank8_refresh_busy				: 1;	// [08]
		const uint32_t rank9_refresh_busy				: 1;	// [09]
		const uint32_t rank10_refresh_busy				: 1;	// [10]
		const uint32_t rank11_refresh_busy				: 1;	// [11]
		const uint32_t rank12_refresh_busy				: 1;	// [12]
		const uint32_t rank13_refresh_busy				: 1;	// [13]
		const uint32_t rank14_refresh_busy				: 1;	// [14]
		const uint32_t rank15_refresh_busy				: 1;	// [15]
		const uint32_t rank16_refresh_busy				: 1;	// [16]
		const uint32_t rank17_refresh_busy				: 1;	// [17]
		const uint32_t rank18_refresh_busy				: 1;	// [18]
		const uint32_t rank19_refresh_busy				: 1;	// [19]
		const uint32_t rank20_refresh_busy				: 1;	// [20]
		const uint32_t rank21_refresh_busy				: 1;	// [21]
		const uint32_t rank22_refresh_busy				: 1;	// [22]
		const uint32_t rank23_refresh_busy				: 1;	// [23]
		const uint32_t rank24_refresh_busy				: 1;	// [24]
		const uint32_t rank25_refresh_busy				: 1;	// [25]
		const uint32_t rank26_refresh_busy				: 1;	// [26]
		const uint32_t rank27_refresh_busy				: 1;	// [27]
		const uint32_t rank28_refresh_busy				: 1;	// [28]
		const uint32_t rank29_refresh_busy				: 1;	// [29]
		const uint32_t rank30_refresh_busy				: 1;	// [30]
		const uint32_t rank31_refresh_busy				: 1;	// [31]
	};
} OPREFSTAT0_t;

typedef union tag_OPREFSTAT1 {
	uint32_t value;
	struct {
		const uint32_t rank32_refresh_busy				: 1;	// [00]
		const uint32_t rank33_refresh_busy				: 1;	// [01]
		const uint32_t rank34_refresh_busy				: 1;	// [02]
		const uint32_t rank35_refresh_busy				: 1;	// [03]
		const uint32_t rank36_refresh_busy				: 1;	// [04]
		const uint32_t rank37_refresh_busy				: 1;	// [05]
		const uint32_t rank38_refresh_busy				: 1;	// [06]
		const uint32_t rank39_refresh_busy				: 1;	// [07]
		const uint32_t rank40_refresh_busy				: 1;	// [08]
		const uint32_t rank41_refresh_busy				: 1;	// [09]
		const uint32_t rank42_refresh_busy				: 1;	// [10]
		const uint32_t rank43_refresh_busy				: 1;	// [11]
		const uint32_t rank44_refresh_busy				: 1;	// [12]
		const uint32_t rank45_refresh_busy				: 1;	// [13]
		const uint32_t rank46_refresh_busy				: 1;	// [14]
		const uint32_t rank47_refresh_busy				: 1;	// [15]
		const uint32_t rank48_refresh_busy				: 1;	// [16]
		const uint32_t rank49_refresh_busy				: 1;	// [17]
		const uint32_t rank50_refresh_busy				: 1;	// [18]
		const uint32_t rank51_refresh_busy				: 1;	// [19]
		const uint32_t rank52_refresh_busy				: 1;	// [20]
		const uint32_t rank53_refresh_busy				: 1;	// [21]
		const uint32_t rank54_refresh_busy				: 1;	// [22]
		const uint32_t rank55_refresh_busy				: 1;	// [23]
		const uint32_t rank56_refresh_busy				: 1;	// [24]
		const uint32_t rank57_refresh_busy				: 1;	// [25]
		const uint32_t rank58_refresh_busy				: 1;	// [26]
		const uint32_t rank59_refresh_busy				: 1;	// [27]
		const uint32_t rank60_refresh_busy				: 1;	// [28]
		const uint32_t rank61_refresh_busy				: 1;	// [29]
		const uint32_t rank62_refresh_busy				: 1;	// [30]
		const uint32_t rank63_refresh_busy				: 1;	// [31]
	};
} OPREFSTAT1_t;

typedef union tag_OPDPSTAT0 {
	uint32_t value;
	struct {
		const uint32_t dfi_cmd_delay					: 32;	// [00 ... 31]
	};
} OPDPSTAT0_t;

typedef union tag_OPCTRLWRCAM {
	uint32_t value;
	struct {
		const uint32_t dbg_w_q_depth_extend				: 32;	// [00 ... 31]
	};
} OPCTRLWRCAM_t;

typedef union tag_OPCTRLRDCAM {
	uint32_t value;
	struct {
		const uint32_t dbg_hpr_q_depth_extend				: 16;	// [00 ... 15]
		const uint32_t dbg_lpr_q_depth_extend				: 16;	// [16 ... 31]
	};
} OPCTRLRDCAM_t;

typedef union tag_SCHED6 {
	uint32_t value;
	struct {
		uint32_t lpr_num_entries_extend					: 32;	// [00 ... 31]
	};
} SCHED6_t;

typedef union tag_SCHED7 {
	uint32_t value;
	struct {
		uint32_t wrcam_lowthresh_extend					: 10;	// [00 ... 09]
		uint32_t wrcam_highthresh_extend				: 10;	// [10 ... 19]
		uint32_t wr_pghit_num_thresh_extend				: 12;	// [20 ... 31]
	};
} SCHED7_t;

typedef union tag_SWCTL {
	uint32_t value;
	struct {
		uint32_t sw_done						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} SWCTL_t;

typedef union tag_SWSTAT {
	uint32_t value;
	struct {
		const uint32_t sw_done_ack					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} SWSTAT_t;

typedef union tag_DIMMCTL {
	uint32_t value;
	struct {
		uint32_t dimm_stagger_cs_en					: 1;	// [00]
		uint32_t dimm_addr_mirr_en					: 1;	// [01]
		uint32_t dimm_output_inv_en					: 1;	// [02]
		uint32_t mrs_a17_en						: 1;	// [03]
		uint32_t mrs_bg1_en						: 1;	// [04]
		uint32_t dimm_dis_bg_mirroring					: 1;	// [05]
		uint32_t lrdimm_bcom_cmd_prot					: 1;	// [06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t rcd_num						: 2;	// [08 ... 09]
		uint32_t dimm_type						: 2;	// [10 ... 11]
		uint32_t rcd_weak_drive						: 1;	// [12]
		uint32_t rcd_a_output_disabled					: 1;	// [13]
		uint32_t rcd_b_output_disabled					: 1;	// [14]
		uint32_t dimm_selfref_clock_stop_mode				: 1;	// [15]
		const uint32_t _RESERVED1					: 16;	// [16 ... 31]
	};
} DIMMCTL_t;

typedef union tag_CHCTL {
	uint32_t value;
	struct {
		uint32_t dual_channel_en					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} CHCTL_t;

typedef union tag_RANKCTL {
	uint32_t value;
	struct {
		uint32_t max_rank_rd						: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 8;	// [04 ... 11]
		uint32_t max_rank_wr						: 4;	// [12 ... 15]
		uint32_t max_logical_rank_rd					: 4;	// [16 ... 19]
		uint32_t max_logical_rank_wr					: 4;	// [20 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} RANKCTL_t;

typedef union tag_DBICTL {
	uint32_t value;
	struct {
		uint32_t dm_en							: 1;	// [00]
		uint32_t wr_dbi_en						: 1;	// [01]
		uint32_t rd_dbi_en						: 1;	// [02]
		const uint32_t _RESERVED0					: 29;	// [03 ... 31]
	};
} DBICTL_t;

typedef union tag_DYNBSMSTAT {
	uint32_t value;
	struct {
		const uint32_t num_alloc_bsm					: 8;	// [00 ... 07]
		const uint32_t max_num_alloc_bsm				: 8;	// [08 ... 15]
		const uint32_t max_num_unalloc_entries				: 16;	// [16 ... 31]
	};
} DYNBSMSTAT_t;

typedef union tag_ODTMAP {
	uint32_t value;
	struct {
		uint32_t rank0_wr_odt						: 4;	// [00 ... 03]
		uint32_t rank0_rd_odt						: 4;	// [04 ... 07]
		uint32_t rank1_wr_odt						: 4;	// [08 ... 11]
		uint32_t rank1_rd_odt						: 4;	// [12 ... 15]
		uint32_t rank2_wr_odt						: 4;	// [16 ... 19]
		uint32_t rank2_rd_odt						: 4;	// [20 ... 23]
		uint32_t rank3_wr_odt						: 4;	// [24 ... 27]
		uint32_t rank3_rd_odt						: 4;	// [28 ... 31]
	};
} ODTMAP_t;

typedef union tag_DATACTL0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t rd_data_copy_en					: 1;	// [16]
		uint32_t wr_data_copy_en					: 1;	// [17]
		uint32_t wr_data_x_en						: 1;	// [18]
		const uint32_t _RESERVED1					: 13;	// [19 ... 31]
	};
} DATACTL0_t;

typedef union tag_SWCTLSTATIC {
	uint32_t value;
	struct {
		uint32_t sw_static_unlock					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} SWCTLSTATIC_t;

typedef union tag_CGCTL {
	uint32_t value;
	struct {
		uint32_t force_clk_te_en					: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t force_clk_arb_en					: 1;	// [04]
		const uint32_t _RESERVED1					: 27;	// [05 ... 31]
	};
} CGCTL_t;

typedef union tag_INITTMG0 {
	uint32_t value;
	struct {
		uint32_t pre_cke_x1024						: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t post_cke_x1024						: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 4;	// [26 ... 29]
		uint32_t skip_dram_init						: 2;	// [30 ... 31]
	};
} INITTMG0_t;

typedef union tag_INITTMG2 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t dev_zqinit_x32						: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} INITTMG2_t;

typedef union tag_DS_DBG_CTRL0 {
	uint32_t value;
	struct {
		uint32_t dbg_bsm_sel_ctrl					: 16;	// [00 ... 15]
		uint32_t dbg_lrsm_sel_ctrl					: 16;	// [16 ... 31]
	};
} DS_DBG_CTRL0_t;

typedef union tag_DS_DBG_STAT0 {
	uint32_t value;
	struct {
		const uint32_t dbg_stat0					: 32;	// [00 ... 31]
	};
} DS_DBG_STAT0_t;

typedef union tag_DS_DBG_STAT1 {
	uint32_t value;
	struct {
		const uint32_t dbg_stat1					: 32;	// [00 ... 31]
	};
} DS_DBG_STAT1_t;

typedef union tag_DS_DBG_STAT2 {
	uint32_t value;
	struct {
		const uint32_t dbg_stat2					: 32;	// [00 ... 31]
	};
} DS_DBG_STAT2_t;

typedef union tag_DS_DBG_STAT3 {
	uint32_t value;
	struct {
		const uint32_t dbg_stat3					: 32;	// [00 ... 31]
	};
} DS_DBG_STAT3_t;

typedef union tag_DU_DBG_STAT0 {
	uint32_t value;
	struct {
		const uint32_t du_cur_blk_ucode					: 16;	// [00 ... 15]
		const uint32_t du_cur_blk_addr					: 8;	// [16 ... 23]
		const uint32_t du_cur_blk_index					: 5;	// [24 ... 28]
		const uint32_t du_cur_blk_set					: 1;	// [29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} DU_DBG_STAT0_t;

typedef union tag_DU_DBG_STAT1 {
	uint32_t value;
	struct {
		const uint32_t du_main_fsm_state				: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t du_sceu_fsm_state				: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t du_mceu_fsm_state				: 3;	// [08 ... 10]
		const uint32_t _RESERVED2					: 21;	// [11 ... 31]
	};
} DU_DBG_STAT1_t;

typedef union tag_LC_DBG_STAT0 {
	uint32_t value;
	struct {
		const uint32_t dbg_rank_ctrl_mc_addr_0				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t dbg_rank_ctrl_mc_code_0				: 16;	// [16 ... 31]
	};
} LC_DBG_STAT0_t;

typedef union tag_LC_DBG_STAT1 {
	uint32_t value;
	struct {
		const uint32_t dbg_rank_ctrl_mc_addr_1				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t dbg_rank_ctrl_mc_code_1				: 16;	// [16 ... 31]
	};
} LC_DBG_STAT1_t;

typedef union tag_LC_DBG_STAT2 {
	uint32_t value;
	struct {
		const uint32_t dbg_rank_ctrl_mc_addr_2				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t dbg_rank_ctrl_mc_code_2				: 16;	// [16 ... 31]
	};
} LC_DBG_STAT2_t;

typedef union tag_LC_DBG_STAT3 {
	uint32_t value;
	struct {
		const uint32_t dbg_rank_ctrl_mc_addr_3				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		const uint32_t dbg_rank_ctrl_mc_code_3				: 16;	// [16 ... 31]
	};
} LC_DBG_STAT3_t;

typedef union tag_LC_DBG_STAT4 {
	uint32_t value;
	struct {
		const uint32_t dbg_sceu_ctrl_state_sceu_0			: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t dbg_mceu_ctrl_state_mceu_0			: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t dbg_rank_ctrl_state_rsm_0			: 4;	// [08 ... 11]
		const uint32_t _RESERVED2					: 4;	// [12 ... 15]
		const uint32_t dbg_sceu_ctrl_state_sceu_1			: 3;	// [16 ... 18]
		const uint32_t _RESERVED3					: 1;	// [19]
		const uint32_t dbg_mceu_ctrl_state_mceu_1			: 3;	// [20 ... 22]
		const uint32_t _RESERVED4					: 1;	// [23]
		const uint32_t dbg_rank_ctrl_state_rsm_1			: 4;	// [24 ... 27]
		const uint32_t _RESERVED5					: 4;	// [28 ... 31]
	};
} LC_DBG_STAT4_t;

typedef union tag_LC_DBG_STAT5 {
	uint32_t value;
	struct {
		const uint32_t dbg_sceu_ctrl_state_sceu_2			: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t dbg_mceu_ctrl_state_mceu_2			: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t dbg_rank_ctrl_state_rsm_2			: 4;	// [08 ... 11]
		const uint32_t _RESERVED2					: 4;	// [12 ... 15]
		const uint32_t dbg_sceu_ctrl_state_sceu_3			: 3;	// [16 ... 18]
		const uint32_t _RESERVED3					: 1;	// [19]
		const uint32_t dbg_mceu_ctrl_state_mceu_3			: 3;	// [20 ... 22]
		const uint32_t _RESERVED4					: 1;	// [23]
		const uint32_t dbg_rank_ctrl_state_rsm_3			: 4;	// [24 ... 27]
		const uint32_t _RESERVED5					: 4;	// [28 ... 31]
	};
} LC_DBG_STAT5_t;

typedef union tag_LC_DBG_STAT6 {
	uint32_t value;
	struct {
		const uint32_t dbg_dfi_lp_state_dsm				: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t dbg_dfi_lp_data_ack				: 1;	// [04]
		const uint32_t dbg_dfi_lp_ctrl_ack				: 1;	// [05]
		const uint32_t _RESERVED1					: 2;	// [06 ... 07]
		const uint32_t dbg_hw_lp_state_hsm				: 3;	// [08 ... 10]
		const uint32_t _RESERVED2					: 21;	// [11 ... 31]
	};
} LC_DBG_STAT6_t;

typedef union tag_CAPAR_DBG_STAT0 {
	uint32_t value;
	struct {
		const uint32_t dbg_capar_retry_mc_addr				: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 10;	// [06 ... 15]
		const uint32_t dbg_capar_retry_mc_code				: 16;	// [16 ... 31]
	};
} CAPAR_DBG_STAT0_t;

typedef union tag_CAPAR_DBG_STAT1 {
	uint32_t value;
	struct {
		const uint32_t dbg_capar_retry_state_sceu			: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t dbg_capar_retry_state_mceu			: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t dbg_capar_retry_state_csm			: 2;	// [08 ... 09]
		const uint32_t _RESERVED2					: 22;	// [10 ... 31]
	};
} CAPAR_DBG_STAT1_t;

typedef union tag_CAPAR_CMDFIFO_CTRL {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t cmdfifo_rd_addr					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} CAPAR_CMDFIFO_CTRL_t;

typedef union tag_CAPAR_CMDFIFO_STAT {
	uint32_t value;
	struct {
		const uint32_t cmdfifo_rd_data					: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 19;	// [13 ... 31]
	};
} CAPAR_CMDFIFO_STAT_t;

typedef union tag_CAPAR_CMDFIFO_LOG {
	uint32_t value;
	struct {
		const uint32_t cmdfifo_window_cmd_num				: 9;	// [00 ... 08]
		const uint32_t _RESERVED0					: 7;	// [09 ... 15]
		const uint32_t cmdfifo_recorded_cmd_num				: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 6;	// [25 ... 30]
		const uint32_t cmdfifo_overflow					: 1;	// [31]
	};
} CAPAR_CMDFIFO_LOG_t;

typedef union tag_ECCERRCNTCTL {
	uint32_t value;
	struct {
		uint32_t ecc_corr_threshold					: 16;	// [00 ... 15]
		uint32_t ecc_corr_err_cnt_clr_rank0				: 1;	// [16]
		uint32_t ecc_corr_err_cnt_clr_rank1				: 1;	// [17]
		uint32_t ecc_corr_err_cnt_clr_rank2				: 1;	// [18]
		uint32_t ecc_corr_err_cnt_clr_rank3				: 1;	// [19]
		uint32_t ecc_uncorr_err_log_mode				: 2;	// [20 ... 21]
		uint32_t ecc_corr_err_log_mode					: 6;	// [22 ... 27]
		uint32_t ecc_corr_err_per_rank_intr_en				: 4;	// [28 ... 31]
	};
} ECCERRCNTCTL_t;

typedef union tag_ECCERRCNTSTAT {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_err_per_rank_intr			: 32;	// [00 ... 31]
	};
} ECCERRCNTSTAT_t;

typedef union tag_ECCERRCNT0 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_err_cnt_rank0				: 16;	// [00 ... 15]
		const uint32_t ecc_corr_err_cnt_rank1				: 16;	// [16 ... 31]
	};
} ECCERRCNT0_t;

typedef union tag_ECCERRCNT1 {
	uint32_t value;
	struct {
		const uint32_t ecc_corr_err_cnt_rank2				: 16;	// [00 ... 15]
		const uint32_t ecc_corr_err_cnt_rank3				: 16;	// [16 ... 31]
	};
} ECCERRCNT1_t;

typedef union tag_PPT2CTRL0 {
	uint32_t value;
	struct {
		uint32_t ppt2_burst_num						: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 2;	// [10 ... 11]
		uint32_t ppt2_ctrlupd_num_dfi0					: 6;	// [12 ... 17]
		uint32_t ppt2_ctrlupd_num_dfi1					: 6;	// [18 ... 23]
		const uint32_t _RESERVED1					: 4;	// [24 ... 27]
		uint32_t ppt2_burst						: 1;	// [28]
		const uint32_t _RESERVED2					: 2;	// [29 ... 30]
		uint32_t ppt2_wait_ref						: 1;	// [31]
	};
} PPT2CTRL0_t;

typedef union tag_PPT2STAT0 {
	uint32_t value;
	struct {
		const uint32_t ppt2_state					: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 24;	// [04 ... 27]
		const uint32_t ppt2_burst_busy					: 1;	// [28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} PPT2STAT0_t;

typedef union tag_DDRCTL_IMECFG0 {
	uint32_t value;
	struct {
		uint32_t ime_en							: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DDRCTL_IMECFG0_t;

typedef union tag_DDRCTL_IMESTAT0 {
	uint32_t value;
	struct {
		const uint32_t ime_force_disabled				: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} DDRCTL_IMESTAT0_t;

typedef union tag_DDRCTL_VER_NUMBER {
	uint32_t value;
	struct {
		const uint32_t ver_number					: 32;	// [00 ... 31]
	};
} DDRCTL_VER_NUMBER_t;

typedef union tag_DDRCTL_VER_TYPE {
	uint32_t value;
	struct {
		const uint32_t ver_type						: 32;	// [00 ... 31]
	};
} DDRCTL_VER_TYPE_t;

typedef union tag_ADDRMAP0 {
	uint32_t value;
	struct {
		uint32_t addrmap_dch_bit0					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} ADDRMAP0_t;

typedef union tag_ADDRMAP1 {
	uint32_t value;
	struct {
		uint32_t addrmap_cs_bit0					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t addrmap_cs_bit1					: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t addrmap_cs_bit2					: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 2;	// [22 ... 23]
		uint32_t addrmap_cs_bit3					: 6;	// [24 ... 29]
		const uint32_t _RESERVED3					: 2;	// [30 ... 31]
	};
} ADDRMAP1_t;

typedef union tag_ADDRMAP2 {
	uint32_t value;
	struct {
		uint32_t addrmap_cid_b0						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t addrmap_cid_b1						: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t addrmap_cid_b2						: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 2;	// [22 ... 23]
		uint32_t addrmap_cid_b3						: 6;	// [24 ... 29]
		const uint32_t _RESERVED3					: 2;	// [30 ... 31]
	};
} ADDRMAP2_t;

typedef union tag_ADDRMAP3 {
	uint32_t value;
	struct {
		uint32_t addrmap_bank_b0					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t addrmap_bank_b1					: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t addrmap_bank_b2					: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 10;	// [22 ... 31]
	};
} ADDRMAP3_t;

typedef union tag_ADDRMAP4 {
	uint32_t value;
	struct {
		uint32_t addrmap_bg_b0						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t addrmap_bg_b1						: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t addrmap_bg_b2						: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 10;	// [22 ... 31]
	};
} ADDRMAP4_t;

typedef union tag_ADDRMAP5 {
	uint32_t value;
	struct {
		uint32_t addrmap_col_b7						: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_col_b8						: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t addrmap_col_b9						: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t addrmap_col_b10					: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} ADDRMAP5_t;

typedef union tag_ADDRMAP6 {
	uint32_t value;
	struct {
		uint32_t addrmap_col_b3						: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 4;	// [04 ... 07]
		uint32_t addrmap_col_b4						: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 4;	// [12 ... 15]
		uint32_t addrmap_col_b5						: 4;	// [16 ... 19]
		const uint32_t _RESERVED2					: 4;	// [20 ... 23]
		uint32_t addrmap_col_b6						: 4;	// [24 ... 27]
		const uint32_t _RESERVED3					: 4;	// [28 ... 31]
	};
} ADDRMAP6_t;

typedef union tag_ADDRMAP7 {
	uint32_t value;
	struct {
		uint32_t addrmap_row_b14					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_row_b15					: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t addrmap_row_b16					: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t addrmap_row_b17					: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} ADDRMAP7_t;

typedef union tag_ADDRMAP8 {
	uint32_t value;
	struct {
		uint32_t addrmap_row_b10					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_row_b11					: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t addrmap_row_b12					: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t addrmap_row_b13					: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} ADDRMAP8_t;

typedef union tag_ADDRMAP9 {
	uint32_t value;
	struct {
		uint32_t addrmap_row_b6						: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_row_b7						: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t addrmap_row_b8						: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t addrmap_row_b9						: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} ADDRMAP9_t;

typedef union tag_ADDRMAP10 {
	uint32_t value;
	struct {
		uint32_t addrmap_row_b2						: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_row_b3						: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t addrmap_row_b4						: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t addrmap_row_b5						: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} ADDRMAP10_t;

typedef union tag_ADDRMAP11 {
	uint32_t value;
	struct {
		uint32_t addrmap_row_b0						: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t addrmap_row_b1						: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 19;	// [13 ... 31]
	};
} ADDRMAP11_t;

typedef union tag_ADDRMAP12 {
	uint32_t value;
	struct {
		uint32_t nonbinary_device_density				: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t bank_hash_en						: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t lpddr_mixed_pkg_en					: 1;	// [08]
		const uint32_t _RESERVED2					: 7;	// [09 ... 15]
		uint32_t lpddr_mixed_pkg_x16_size				: 4;	// [16 ... 19]
		const uint32_t _RESERVED3					: 12;	// [20 ... 31]
	};
} ADDRMAP12_t;

typedef union tag_ADDRMAPLUTCFG {
	uint32_t value;
	struct {
		uint32_t addrmap_lut_bypass					: 1;	// [00]
		uint32_t addrmap_use_lut_cs					: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t addrmap_lut_rank_type					: 4;	// [04 ... 07]
		uint32_t addrmap_lut_bit0					: 3;	// [08 ... 10]
		const uint32_t _RESERVED1					: 2;	// [11 ... 12]
		uint32_t addrmap_lut_bit0_valid					: 1;	// [13]
		uint32_t addrmap_lut_bit1					: 3;	// [14 ... 16]
		const uint32_t _RESERVED2					: 2;	// [17 ... 18]
		uint32_t addrmap_lut_bit1_valid					: 1;	// [19]
		uint32_t addrmap_lut_max_active_hif_addr_offset			: 4;	// [20 ... 23]
		const uint32_t _RESERVED3					: 8;	// [24 ... 31]
	};
} ADDRMAPLUTCFG_t;

typedef union tag_ADDRMAPLUTCTRL {
	uint32_t value;
	struct {
		uint32_t addrmap_lut_wdata0					: 8;	// [00 ... 07]
		uint32_t addrmap_lut_wdata1					: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t addrmap_lut_addr					: 6;	// [24 ... 29]
		uint32_t addrmap_lut_rw_type					: 1;	// [30]
		uint32_t addrmap_lut_rw_start					: 1;	// [31]
	};
} ADDRMAPLUTCTRL_t;

typedef union tag_ADDRMAPLUTRDATA {
	uint32_t value;
	struct {
		const uint32_t addrmap_lut_rdata0				: 8;	// [00 ... 07]
		const uint32_t addrmap_lut_rdata1				: 8;	// [08 ... 15]
		const uint32_t addrmap_rank_valid				: 16;	// [16 ... 31]
	};
} ADDRMAPLUTRDATA_t;

typedef union tag_PCCFG {
	uint32_t value;
	struct {
		uint32_t go2critical_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 3;	// [01 ... 03]
		uint32_t pagematch_limit					: 1;	// [04]
		const uint32_t _RESERVED1					: 7;	// [05 ... 11]
		uint32_t dch_density_ratio					: 2;	// [12 ... 13]
		const uint32_t _RESERVED2					: 18;	// [14 ... 31]
	};
} PCCFG_t;

typedef union tag_PCFGR {
	uint32_t value;
	struct {
		uint32_t rd_port_priority					: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 1;	// [10]
		uint32_t read_reorder_bypass_en					: 1;	// [11]
		uint32_t rd_port_aging_en					: 1;	// [12]
		uint32_t rd_port_urgent_en					: 1;	// [13]
		uint32_t rd_port_pagematch_en					: 1;	// [14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t rdwr_ordered_en					: 1;	// [16]
		const uint32_t _RESERVED2					: 3;	// [17 ... 19]
		uint32_t rrb_lock_threshold					: 4;	// [20 ... 23]
		const uint32_t _RESERVED3					: 8;	// [24 ... 31]
	};
} PCFGR_t;

typedef union tag_PCFGW {
	uint32_t value;
	struct {
		uint32_t wr_port_priority					: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 2;	// [10 ... 11]
		uint32_t wr_port_aging_en					: 1;	// [12]
		uint32_t wr_port_urgent_en					: 1;	// [13]
		uint32_t wr_port_pagematch_en					: 1;	// [14]
		uint32_t snf_mode						: 1;	// [15]
		const uint32_t _RESERVED1					: 16;	// [16 ... 31]
	};
} PCFGW_t;

typedef union tag_PCFGIDMASKCH {
	uint32_t value;
	struct {
		uint32_t id_mask						: 32;	// [00 ... 31]
	};
} PCFGIDMASKCH_t;

typedef union tag_PCFGIDVALUECH {
	uint32_t value;
	struct {
		uint32_t id_value						: 32;	// [00 ... 31]
	};
} PCFGIDVALUECH_t;

typedef union tag_PCTRL {
	uint32_t value;
	struct {
		uint32_t port_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} PCTRL_t;

typedef union tag_PCFGQOS0 {
	uint32_t value;
	struct {
		uint32_t rqos_map_level1					: 8;	// [00 ... 07]
		uint32_t rqos_map_level2					: 8;	// [08 ... 15]
		uint32_t rqos_map_region0					: 4;	// [16 ... 19]
		uint32_t rqos_map_region1					: 4;	// [20 ... 23]
		uint32_t rqos_map_region2					: 8;	// [24 ... 31]
	};
} PCFGQOS0_t;

typedef union tag_PCFGQOS1 {
	uint32_t value;
	struct {
		uint32_t rqos_map_timeoutb					: 16;	// [00 ... 15]
		uint32_t rqos_map_timeoutr					: 16;	// [16 ... 31]
	};
} PCFGQOS1_t;

typedef union tag_PCFGWQOS0 {
	uint32_t value;
	struct {
		uint32_t wqos_map_level1					: 8;	// [00 ... 07]
		uint32_t wqos_map_level2					: 8;	// [08 ... 15]
		uint32_t wqos_map_region0					: 4;	// [16 ... 19]
		uint32_t wqos_map_region1					: 4;	// [20 ... 23]
		uint32_t wqos_map_region2					: 8;	// [24 ... 31]
	};
} PCFGWQOS0_t;

typedef union tag_PCFGWQOS1 {
	uint32_t value;
	struct {
		uint32_t wqos_map_timeout1					: 16;	// [00 ... 15]
		uint32_t wqos_map_timeout2					: 16;	// [16 ... 31]
	};
} PCFGWQOS1_t;

typedef union tag_SARBASE {
	uint32_t value;
	struct {
		uint32_t base_addr						: 32;	// [00 ... 31]
	};
} SARBASE_t;

typedef union tag_SARSIZE {
	uint32_t value;
	struct {
		uint32_t nblocks						: 32;	// [00 ... 31]
	};
} SARSIZE_t;

typedef union tag_SBRCTL {
	uint32_t value;
	struct {
		uint32_t scrub_en						: 1;	// [00]
		uint32_t scrub_during_lowpower					: 1;	// [01]
		const uint32_t _RESERVED0					: 1;	// [02]
		uint32_t scrub_en_dch1						: 1;	// [03]
		uint32_t scrub_burst_length_nm					: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		uint32_t scrub_interval						: 16;	// [08 ... 23]
		uint32_t scrub_cmd_type						: 2;	// [24 ... 25]
		uint32_t sbr_correction_mode					: 2;	// [26 ... 27]
		uint32_t scrub_burst_length_lp					: 3;	// [28 ... 30]
		uint32_t scrub_ue						: 1;	// [31]
	};
} SBRCTL_t;

typedef union tag_SBRSTAT {
	uint32_t value;
	struct {
		const uint32_t scrub_busy					: 1;	// [00]
		const uint32_t scrub_done					: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		const uint32_t scrub_drop_cnt					: 5;	// [04 ... 08]
		const uint32_t _RESERVED1					: 7;	// [09 ... 15]
		const uint32_t scrub_busy_dch1					: 1;	// [16]
		const uint32_t scrub_done_dch1					: 1;	// [17]
		const uint32_t _RESERVED2					: 2;	// [18 ... 19]
		const uint32_t scrub_drop_cnt_dch1				: 5;	// [20 ... 24]
		const uint32_t _RESERVED3					: 7;	// [25 ... 31]
	};
} SBRSTAT_t;

typedef union tag_SBRWDATA0 {
	uint32_t value;
	struct {
		uint32_t scrub_pattern0						: 32;	// [00 ... 31]
	};
} SBRWDATA0_t;

typedef union tag_SBRWDATA1 {
	uint32_t value;
	struct {
		uint32_t scrub_pattern1						: 32;	// [00 ... 31]
	};
} SBRWDATA1_t;

typedef union tag_SBRSTART0 {
	uint32_t value;
	struct {
		uint32_t sbr_address_start_mask_0				: 32;	// [00 ... 31]
	};
} SBRSTART0_t;

typedef union tag_SBRSTART1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_start_mask_1				: 32;	// [00 ... 31]
	};
} SBRSTART1_t;

typedef union tag_SBRRANGE0 {
	uint32_t value;
	struct {
		uint32_t sbr_address_range_mask_0				: 32;	// [00 ... 31]
	};
} SBRRANGE0_t;

typedef union tag_SBRRANGE1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_range_mask_1				: 32;	// [00 ... 31]
	};
} SBRRANGE1_t;

typedef union tag_SBRSTART0DCH1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_start_mask_dch1_0				: 32;	// [00 ... 31]
	};
} SBRSTART0DCH1_t;

typedef union tag_SBRSTART1DCH1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_start_mask_dch1_1				: 32;	// [00 ... 31]
	};
} SBRSTART1DCH1_t;

typedef union tag_SBRRANGE0DCH1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_range_mask_dch1_0				: 32;	// [00 ... 31]
	};
} SBRRANGE0DCH1_t;

typedef union tag_SBRRANGE1DCH1 {
	uint32_t value;
	struct {
		uint32_t sbr_address_range_mask_dch1_1				: 32;	// [00 ... 31]
	};
} SBRRANGE1DCH1_t;

typedef union tag_PDCH {
	uint32_t value;
	struct {
		uint32_t port_data_channel_0					: 1;	// [00]
		uint32_t port_data_channel_1					: 1;	// [01]
		uint32_t port_data_channel_2					: 1;	// [02]
		uint32_t port_data_channel_3					: 1;	// [03]
		uint32_t port_data_channel_4					: 1;	// [04]
		uint32_t port_data_channel_5					: 1;	// [05]
		uint32_t port_data_channel_6					: 1;	// [06]
		uint32_t port_data_channel_7					: 1;	// [07]
		uint32_t port_data_channel_8					: 1;	// [08]
		uint32_t port_data_channel_9					: 1;	// [09]
		uint32_t port_data_channel_10					: 1;	// [10]
		uint32_t port_data_channel_11					: 1;	// [11]
		uint32_t port_data_channel_12					: 1;	// [12]
		uint32_t port_data_channel_13					: 1;	// [13]
		uint32_t port_data_channel_14					: 1;	// [14]
		uint32_t port_data_channel_15					: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} PDCH_t;

typedef union tag_PSTAT {
	uint32_t value;
	struct {
		const uint32_t rd_port_busy_0					: 1;	// [00]
		const uint32_t rd_port_busy_1					: 1;	// [01]
		const uint32_t rd_port_busy_2					: 1;	// [02]
		const uint32_t rd_port_busy_3					: 1;	// [03]
		const uint32_t rd_port_busy_4					: 1;	// [04]
		const uint32_t rd_port_busy_5					: 1;	// [05]
		const uint32_t rd_port_busy_6					: 1;	// [06]
		const uint32_t rd_port_busy_7					: 1;	// [07]
		const uint32_t rd_port_busy_8					: 1;	// [08]
		const uint32_t rd_port_busy_9					: 1;	// [09]
		const uint32_t rd_port_busy_10					: 1;	// [10]
		const uint32_t rd_port_busy_11					: 1;	// [11]
		const uint32_t rd_port_busy_12					: 1;	// [12]
		const uint32_t rd_port_busy_13					: 1;	// [13]
		const uint32_t rd_port_busy_14					: 1;	// [14]
		const uint32_t rd_port_busy_15					: 1;	// [15]
		const uint32_t wr_port_busy_0					: 1;	// [16]
		const uint32_t wr_port_busy_1					: 1;	// [17]
		const uint32_t wr_port_busy_2					: 1;	// [18]
		const uint32_t wr_port_busy_3					: 1;	// [19]
		const uint32_t wr_port_busy_4					: 1;	// [20]
		const uint32_t wr_port_busy_5					: 1;	// [21]
		const uint32_t wr_port_busy_6					: 1;	// [22]
		const uint32_t wr_port_busy_7					: 1;	// [23]
		const uint32_t wr_port_busy_8					: 1;	// [24]
		const uint32_t wr_port_busy_9					: 1;	// [25]
		const uint32_t wr_port_busy_10					: 1;	// [26]
		const uint32_t wr_port_busy_11					: 1;	// [27]
		const uint32_t wr_port_busy_12					: 1;	// [28]
		const uint32_t wr_port_busy_13					: 1;	// [29]
		const uint32_t wr_port_busy_14					: 1;	// [30]
		const uint32_t wr_port_busy_15					: 1;	// [31]
	};
} PSTAT_t;

typedef union tag_SBRLPCTL {
	uint32_t value;
	struct {
		uint32_t perrank_dis_scrub					: 4;	// [00 ... 03]
		uint32_t scrub_restore						: 1;	// [04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t perrank_dis_scrub_dch1					: 4;	// [08 ... 11]
		uint32_t scrub_restore_dch1					: 1;	// [12]
		const uint32_t _RESERVED1					: 19;	// [13 ... 31]
	};
} SBRLPCTL_t;

typedef union tag_SBRADDRLOG0 {
	uint32_t value;
	struct {
		const uint32_t scrub_addr_log0					: 32;	// [00 ... 31]
	};
} SBRADDRLOG0_t;

typedef union tag_SBRADDRLOG1 {
	uint32_t value;
	struct {
		const uint32_t scrub_addr_log1					: 32;	// [00 ... 31]
	};
} SBRADDRLOG1_t;

typedef union tag_SBRADDRRESTORE0 {
	uint32_t value;
	struct {
		uint32_t scrub_restore_address0					: 32;	// [00 ... 31]
	};
} SBRADDRRESTORE0_t;

typedef union tag_SBRADDRRESTORE1 {
	uint32_t value;
	struct {
		uint32_t scrub_restore_address1					: 32;	// [00 ... 31]
	};
} SBRADDRRESTORE1_t;

typedef union tag_SBRADDRLOG0DCH1 {
	uint32_t value;
	struct {
		const uint32_t scrub_addr_log0_dch1				: 32;	// [00 ... 31]
	};
} SBRADDRLOG0DCH1_t;

typedef union tag_SBRADDRLOG1DCH1 {
	uint32_t value;
	struct {
		const uint32_t scrub_addr_log1_dch1				: 32;	// [00 ... 31]
	};
} SBRADDRLOG1DCH1_t;

typedef union tag_SBRADDRRESTORE0DCH1 {
	uint32_t value;
	struct {
		uint32_t scrub_restore_address0_dch1				: 32;	// [00 ... 31]
	};
} SBRADDRRESTORE0DCH1_t;

typedef union tag_SBRADDRRESTORE1DCH1 {
	uint32_t value;
	struct {
		uint32_t scrub_restore_address1_dch1				: 32;	// [00 ... 31]
	};
} SBRADDRRESTORE1DCH1_t;

typedef union tag_PCHBLCTRL {
	uint32_t value;
	struct {
		uint32_t txsactive_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} PCHBLCTRL_t;

typedef union tag_PCHBTCTRL {
	uint32_t value;
	struct {
		uint32_t dis_prefetch						: 1;	// [00]
		uint32_t crc_ue_rsp_sel						: 2;	// [01 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t dbg_force_pcrd_steal_mode				: 1;	// [04]
		uint32_t dbg_wdc_en						: 1;	// [05]
		uint32_t cbusy_select						: 1;	// [06]
		uint32_t dbg_dis_wrptl_rmw_be_eval				: 1;	// [07]
		const uint32_t _RESERVED1					: 24;	// [08 ... 31]
	};
} PCHBTCTRL_t;

typedef union tag_PCHBPRCTMR {
	uint32_t value;
	struct {
		uint32_t prc_exp_cnt						: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 6;	// [10 ... 15]
		uint32_t exp_cnt_div						: 2;	// [16 ... 17]
		const uint32_t _RESERVED1					: 14;	// [18 ... 31]
	};
} PCHBPRCTMR_t;

typedef union tag_PCHBPROTQCTL {
	uint32_t value;
	struct {
		uint32_t rpq_lpr_min						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t rpq_hpr_min						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 17;	// [15 ... 31]
	};
} PCHBPROTQCTL_t;

typedef union tag_PCHBRQOS0 {
	uint32_t value;
	struct {
		uint32_t chb_rqos_map_level1					: 8;	// [00 ... 07]
		uint32_t chb_rqos_map_level2					: 8;	// [08 ... 15]
		uint32_t chb_rqos_map_region0					: 4;	// [16 ... 19]
		uint32_t chb_rqos_map_region1					: 4;	// [20 ... 23]
		uint32_t chb_rqos_map_region2					: 8;	// [24 ... 31]
	};
} PCHBRQOS0_t;

typedef union tag_PCHBRQOS1 {
	uint32_t value;
	struct {
		uint32_t vpr_uncrd_timeout					: 16;	// [00 ... 15]
		uint32_t vpr_crd_timeout					: 16;	// [16 ... 31]
	};
} PCHBRQOS1_t;

typedef union tag_PCHBWQOS0 {
	uint32_t value;
	struct {
		uint32_t chb_wqos_map_level1					: 8;	// [00 ... 07]
		uint32_t chb_wqos_map_level2					: 8;	// [08 ... 15]
		uint32_t chb_wqos_map_region0					: 4;	// [16 ... 19]
		uint32_t chb_wqos_map_region1					: 4;	// [20 ... 23]
		uint32_t chb_wqos_map_region2					: 8;	// [24 ... 31]
	};
} PCHBWQOS0_t;

typedef union tag_PCHBWQOS1 {
	uint32_t value;
	struct {
		uint32_t vpw_uncrd_timeout					: 16;	// [00 ... 15]
		uint32_t vpw_crd_timeout					: 16;	// [16 ... 31]
	};
} PCHBWQOS1_t;

typedef union tag_PCHBCBUSYH {
	uint32_t value;
	struct {
		uint32_t cam_busy_threshold_hpr					: 10;	// [00 ... 09]
		uint32_t cam_free_threshold_hpr					: 10;	// [10 ... 19]
		uint32_t cam_middle_threshold_hpr				: 12;	// [20 ... 31]
	};
} PCHBCBUSYH_t;

typedef union tag_PCHBCBUSYL {
	uint32_t value;
	struct {
		uint32_t cam_busy_threshold_lpr					: 10;	// [00 ... 09]
		uint32_t cam_free_threshold_lpr					: 10;	// [10 ... 19]
		uint32_t cam_middle_threshold_lpr				: 12;	// [20 ... 31]
	};
} PCHBCBUSYL_t;

typedef union tag_PCHBCBUSYW {
	uint32_t value;
	struct {
		uint32_t cam_busy_threshold_wr					: 10;	// [00 ... 09]
		uint32_t cam_free_threshold_wr					: 10;	// [10 ... 19]
		uint32_t cam_middle_threshold_wr				: 12;	// [20 ... 31]
	};
} PCHBCBUSYW_t;

typedef union tag_PCHBLSTAT0 {
	uint32_t value;
	struct {
		const uint32_t txsactive_status					: 1;	// [00]
		const uint32_t rxsactive_status					: 1;	// [01]
		const uint32_t tx_req						: 1;	// [02]
		const uint32_t tx_ack						: 1;	// [03]
		const uint32_t rx_req						: 1;	// [04]
		const uint32_t rx_ack						: 1;	// [05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} PCHBLSTAT0_t;

typedef union tag_PCHBRLSTAT {
	uint32_t value;
	struct {
		const uint32_t retry_list_empty					: 1;	// [00]
		const uint32_t retry_list_full					: 1;	// [01]
		const uint32_t pend_qos_type					: 30;	// [02 ... 31]
	};
} PCHBRLSTAT_t;

typedef union tag_PCHBTZCFG {
	uint32_t value;
	struct {
		const uint32_t tz_no_regions					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		const uint32_t tz_no_subregions					: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		const uint32_t tz_chb_address_width				: 6;	// [08 ... 13]
		const uint32_t _RESERVED2					: 18;	// [14 ... 31]
	};
} PCHBTZCFG_t;

typedef union tag_PCHBTZACT {
	uint32_t value;
	struct {
		uint32_t tz_int_enable						: 1;	// [00]
		uint32_t tz_resperr_enable					: 1;	// [01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} PCHBTZACT_t;

typedef union tag_PCHBTZINTSTS {
	uint32_t value;
	struct {
		const uint32_t tz_int						: 1;	// [00]
		const uint32_t tz_overrun					: 1;	// [01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} PCHBTZINTSTS_t;

typedef union tag_PCHBTZINTCLR {
	uint32_t value;
	struct {
		uint32_t tz_int_clear						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} PCHBTZINTCLR_t;

typedef union tag_PCHBTZLOGADDR0 {
	uint32_t value;
	struct {
		const uint32_t tz_log_addr_low					: 32;	// [00 ... 31]
	};
} PCHBTZLOGADDR0_t;

typedef union tag_PCHBTZLOGADDR1 {
	uint32_t value;
	struct {
		const uint32_t tz_log_addr_high					: 32;	// [00 ... 31]
	};
} PCHBTZLOGADDR1_t;

typedef union tag_PCHBTZLOGOP {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 21;	// [00 ... 20]
		const uint32_t tz_log_nonsecure					: 1;	// [21]
		const uint32_t _RESERVED1					: 2;	// [22 ... 23]
		const uint32_t tz_log_opcode					: 7;	// [24 ... 30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} PCHBTZLOGOP_t;

typedef union tag_PCHBTZLOGID0 {
	uint32_t value;
	struct {
		const uint32_t tz_log_txnid					: 12;	// [00 ... 11]
		const uint32_t tz_log_returntxid				: 11;	// [12 ... 22]
		const uint32_t _RESERVED0					: 9;	// [23 ... 31]
	};
} PCHBTZLOGID0_t;

typedef union tag_PCHBTZLOGID1 {
	uint32_t value;
	struct {
		const uint32_t tz_log_srcid					: 11;	// [00 ... 10]
		const uint32_t tz_log_returnnid					: 11;	// [11 ... 21]
		const uint32_t _RESERVED0					: 10;	// [22 ... 31]
	};
} PCHBTZLOGID1_t;

typedef union tag_PCHBTZCTRL {
	uint32_t value;
	struct {
		uint32_t tz_sec_inv_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} PCHBTZCTRL_t;

typedef union tag_PCHBTZRSETL {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 15;	// [00 ... 14]
		uint32_t tz_base_addr_low					: 17;	// [15 ... 31]
	};
} PCHBTZRSETL_t;

typedef union tag_PCHBTZRSETH {
	uint32_t value;
	struct {
		uint32_t tz_base_addr_high					: 32;	// [00 ... 31]
	};
} PCHBTZRSETH_t;

typedef union tag_PCHBTZRATTR {
	uint32_t value;
	struct {
		uint32_t tz_region_en						: 1;	// [00]
		uint32_t tz_region_size						: 6;	// [01 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t tz_subregion_disable					: 20;	// [08 ... 27]
		uint32_t tz_reg_sp						: 4;	// [28 ... 31]
	};
} PCHBTZRATTR_t;

typedef union tag_DRAMSET1TMG0 {
	uint32_t value;
	struct {
		uint32_t t_ras_min						: 8;	// [00 ... 07]
		uint32_t t_ras_max						: 8;	// [08 ... 15]
		uint32_t t_faw							: 8;	// [16 ... 23]
		uint32_t wr2pre							: 8;	// [24 ... 31]
	};
} DRAMSET1TMG0_t;

typedef union tag_DRAMSET1TMG1 {
	uint32_t value;
	struct {
		uint32_t t_rc							: 8;	// [00 ... 07]
		uint32_t rd2pre							: 8;	// [08 ... 15]
		uint32_t t_xp							: 6;	// [16 ... 21]
		const uint32_t _RESERVED0					: 2;	// [22 ... 23]
		uint32_t t_rcd_write						: 8;	// [24 ... 31]
	};
} DRAMSET1TMG1_t;

typedef union tag_DRAMSET1TMG2 {
	uint32_t value;
	struct {
		uint32_t wr2rd							: 8;	// [00 ... 07]
		uint32_t rd2wr							: 8;	// [08 ... 15]
		uint32_t read_latency						: 7;	// [16 ... 22]
		const uint32_t _RESERVED0					: 1;	// [23]
		uint32_t write_latency						: 7;	// [24 ... 30]
		const uint32_t _RESERVED1					: 1;	// [31]
	};
} DRAMSET1TMG2_t;

typedef union tag_DRAMSET1TMG3 {
	uint32_t value;
	struct {
		uint32_t wr2mr							: 8;	// [00 ... 07]
		uint32_t rd2mr							: 8;	// [08 ... 15]
		uint32_t t_mr							: 7;	// [16 ... 22]
		const uint32_t _RESERVED0					: 9;	// [23 ... 31]
	};
} DRAMSET1TMG3_t;

typedef union tag_DRAMSET1TMG4 {
	uint32_t value;
	struct {
		uint32_t t_rp							: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_rrd							: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t t_ccd							: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 2;	// [22 ... 23]
		uint32_t t_rcd							: 8;	// [24 ... 31]
	};
} DRAMSET1TMG4_t;

typedef union tag_DRAMSET1TMG5 {
	uint32_t value;
	struct {
		uint32_t t_cke							: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t t_ckesr						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t t_cksre						: 7;	// [16 ... 22]
		const uint32_t _RESERVED2					: 1;	// [23]
		uint32_t t_cksrx						: 6;	// [24 ... 29]
		const uint32_t _RESERVED3					: 2;	// [30 ... 31]
	};
} DRAMSET1TMG5_t;

typedef union tag_DRAMSET1TMG6 {
	uint32_t value;
	struct {
		uint32_t t_ckcsx						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 26;	// [06 ... 31]
	};
} DRAMSET1TMG6_t;

typedef union tag_DRAMSET1TMG7 {
	uint32_t value;
	struct {
		uint32_t t_csh							: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 12;	// [04 ... 15]
		uint32_t t_mrw_l						: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} DRAMSET1TMG7_t;

typedef union tag_DRAMSET1TMG8 {
	uint32_t value;
	struct {
		uint32_t t_xs_x32						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_xs_dll_x32						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t t_xs_abort_x32						: 7;	// [16 ... 22]
		const uint32_t _RESERVED2					: 1;	// [23]
		uint32_t t_xs_fast_x32						: 7;	// [24 ... 30]
		const uint32_t _RESERVED3					: 1;	// [31]
	};
} DRAMSET1TMG8_t;

typedef union tag_DRAMSET1TMG9 {
	uint32_t value;
	struct {
		uint32_t wr2rd_s						: 8;	// [00 ... 07]
		uint32_t t_rrd_s						: 6;	// [08 ... 13]
		const uint32_t _RESERVED0					: 2;	// [14 ... 15]
		uint32_t t_ccd_s						: 5;	// [16 ... 20]
		const uint32_t _RESERVED1					: 9;	// [21 ... 29]
		uint32_t ddr4_wr_preamble					: 1;	// [30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} DRAMSET1TMG9_t;

typedef union tag_DRAMSET1TMG10 {
	uint32_t value;
	struct {
		uint32_t t_gear_hold						: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t t_gear_setup						: 3;	// [04 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		uint32_t t_cmd_gear						: 6;	// [08 ... 13]
		const uint32_t _RESERVED2					: 2;	// [14 ... 15]
		uint32_t t_sync_gear						: 6;	// [16 ... 21]
		const uint32_t _RESERVED3					: 10;	// [22 ... 31]
	};
} DRAMSET1TMG10_t;

typedef union tag_DRAMSET1TMG11 {
	uint32_t value;
	struct {
		uint32_t t_ckmpe						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t t_mpx_s						: 3;	// [08 ... 10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t t_mpx_lh						: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 2;	// [22 ... 23]
		uint32_t post_mpsm_gap_x32					: 8;	// [24 ... 31]
	};
} DRAMSET1TMG11_t;

typedef union tag_DRAMSET1TMG12 {
	uint32_t value;
	struct {
		uint32_t t_mrd_pda						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 10;	// [06 ... 15]
		uint32_t t_cmdcke						: 4;	// [16 ... 19]
		const uint32_t _RESERVED1					: 4;	// [20 ... 23]
		uint32_t t_wr_mpr						: 7;	// [24 ... 30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} DRAMSET1TMG12_t;

typedef union tag_DRAMSET1TMG13 {
	uint32_t value;
	struct {
		uint32_t t_ppd							: 4;	// [00 ... 03]
		uint32_t t_ccd_w2						: 8;	// [04 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_ccd_mw						: 7;	// [16 ... 22]
		const uint32_t _RESERVED1					: 1;	// [23]
		uint32_t odtloff						: 7;	// [24 ... 30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} DRAMSET1TMG13_t;

typedef union tag_DRAMSET1TMG14 {
	uint32_t value;
	struct {
		uint32_t t_xsr							: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_osco							: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} DRAMSET1TMG14_t;

typedef union tag_DRAMSET1TMG15 {
	uint32_t value;
	struct {
		uint32_t t_stab_x32						: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 14;	// [10 ... 23]
		uint32_t en_hwffc_t_stab					: 1;	// [24]
		const uint32_t _RESERVED1					: 6;	// [25 ... 30]
		uint32_t en_dfi_lp_t_stab					: 1;	// [31]
	};
} DRAMSET1TMG15_t;

typedef union tag_DRAMSET1TMG16 {
	uint32_t value;
	struct {
		uint32_t t_ccd_dlr						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t t_rrd_dlr						: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 4;	// [12 ... 15]
		uint32_t t_faw_dlr						: 8;	// [16 ... 23]
		uint32_t t_rp_ca_parity						: 8;	// [24 ... 31]
	};
} DRAMSET1TMG16_t;

typedef union tag_DRAMSET1TMG17 {
	uint32_t value;
	struct {
		uint32_t t_vrcg_disable						: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 6;	// [10 ... 15]
		uint32_t t_vrcg_enable						: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} DRAMSET1TMG17_t;

typedef union tag_DRAMSET1TMG18 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t t_mpsmx						: 7;	// [16 ... 22]
		const uint32_t _RESERVED1					: 1;	// [23]
		uint32_t t_pd							: 7;	// [24 ... 30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} DRAMSET1TMG18_t;

typedef union tag_DRAMSET1TMG20 {
	uint32_t value;
	struct {
		uint32_t t_csl_srexit						: 8;	// [00 ... 07]
		uint32_t t_csh_srexit						: 8;	// [08 ... 15]
		uint32_t t_casrx						: 5;	// [16 ... 20]
		const uint32_t _RESERVED0					: 3;	// [21 ... 23]
		uint32_t t_cpded						: 6;	// [24 ... 29]
		const uint32_t _RESERVED1					: 2;	// [30 ... 31]
	};
} DRAMSET1TMG20_t;

typedef union tag_DRAMSET1TMG21 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 14;	// [00 ... 13]
		uint32_t t_mpc_hold						: 3;	// [14 ... 16]
		uint32_t t_mpc_setup						: 3;	// [17 ... 19]
		uint32_t t_mpc_cs						: 5;	// [20 ... 24]
		uint32_t t_csl							: 7;	// [25 ... 31]
	};
} DRAMSET1TMG21_t;

typedef union tag_DRAMSET1TMG22 {
	uint32_t value;
	struct {
		uint32_t t_rd2wr_dpr						: 7;	// [00 ... 06]
		uint32_t t_rd2wr_dlr						: 7;	// [07 ... 13]
		uint32_t t_wr2rd_dpr						: 8;	// [14 ... 21]
		uint32_t t_wr2rd_dlr						: 8;	// [22 ... 29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} DRAMSET1TMG22_t;

typedef union tag_DRAMSET1TMG23 {
	uint32_t value;
	struct {
		uint32_t t_pdn							: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_xsr_dsm_x1024					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} DRAMSET1TMG23_t;

typedef union tag_DRAMSET1TMG24 {
	uint32_t value;
	struct {
		uint32_t max_wr_sync						: 8;	// [00 ... 07]
		uint32_t max_rd_sync						: 8;	// [08 ... 15]
		uint32_t rd2wr_s						: 8;	// [16 ... 23]
		uint32_t bank_org						: 2;	// [24 ... 25]
		const uint32_t _RESERVED0					: 6;	// [26 ... 31]
	};
} DRAMSET1TMG24_t;

typedef union tag_DRAMSET1TMG25 {
	uint32_t value;
	struct {
		uint32_t rda2pre						: 8;	// [00 ... 07]
		uint32_t wra2pre						: 8;	// [08 ... 15]
		uint32_t lpddr4_diff_bank_rwa2pre				: 3;	// [16 ... 18]
		const uint32_t _RESERVED0					: 13;	// [19 ... 31]
	};
} DRAMSET1TMG25_t;

typedef union tag_DRAMSET1TMG26 {
	uint32_t value;
	struct {
		uint32_t t_ccd_r						: 8;	// [00 ... 07]
		uint32_t t_ccd_w						: 8;	// [08 ... 15]
		uint32_t t_ccd_r_s						: 8;	// [16 ... 23]
		uint32_t t_ccd_w_s						: 8;	// [24 ... 31]
	};
} DRAMSET1TMG26_t;

typedef union tag_DRAMSET1TMG27 {
	uint32_t value;
	struct {
		uint32_t t_mrr2mpc						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t t_ecsc							: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} DRAMSET1TMG27_t;

typedef union tag_DRAMSET1TMG28 {
	uint32_t value;
	struct {
		uint32_t t_srx2srx						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_cpded2srx						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t t_cssr							: 7;	// [16 ... 22]
		const uint32_t _RESERVED2					: 9;	// [23 ... 31]
	};
} DRAMSET1TMG28_t;

typedef union tag_DRAMSET1TMG29 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t t_ckact						: 6;	// [16 ... 21]
		const uint32_t _RESERVED1					: 2;	// [22 ... 23]
		uint32_t t_ckoff						: 7;	// [24 ... 30]
		const uint32_t _RESERVED2					: 1;	// [31]
	};
} DRAMSET1TMG29_t;

typedef union tag_DRAMSET1TMG30 {
	uint32_t value;
	struct {
		uint32_t mrr2rd							: 8;	// [00 ... 07]
		uint32_t mrr2wr							: 8;	// [08 ... 15]
		uint32_t mrr2mrw						: 8;	// [16 ... 23]
		const uint32_t _RESERVED0					: 8;	// [24 ... 31]
	};
} DRAMSET1TMG30_t;

typedef union tag_DRAMSET1TMG31 {
	uint32_t value;
	struct {
		uint32_t rfm_raaimt						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 2;	// [07 ... 08]
		uint32_t rfm_raa_thr						: 9;	// [09 ... 17]
		const uint32_t _RESERVED1					: 1;	// [18]
		uint32_t rfm_raa_ref_decr					: 2;	// [19 ... 20]
		const uint32_t _RESERVED2					: 11;	// [21 ... 31]
	};
} DRAMSET1TMG31_t;

typedef union tag_DRAMSET1TMG32 {
	uint32_t value;
	struct {
		uint32_t ws_fs2wck_sus						: 4;	// [00 ... 03]
		const uint32_t _RESERVED0					: 4;	// [04 ... 07]
		uint32_t t_wcksus						: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 4;	// [12 ... 15]
		uint32_t ws_off2ws_fs						: 4;	// [16 ... 19]
		const uint32_t _RESERVED2					: 12;	// [20 ... 31]
	};
} DRAMSET1TMG32_t;

typedef union tag_DRAMSET1TMG33 {
	uint32_t value;
	struct {
		uint32_t t_ccd_r_m						: 8;	// [00 ... 07]
		uint32_t t_ccd_w_m						: 8;	// [08 ... 15]
		uint32_t t_wr2rd_m						: 8;	// [16 ... 23]
		const uint32_t _RESERVED0					: 8;	// [24 ... 31]
	};
} DRAMSET1TMG33_t;

typedef union tag_DRAMSET1TMG34 {
	uint32_t value;
	struct {
		uint32_t t_ccd_mw_blx2						: 8;	// [00 ... 07]
		uint32_t rd2wr_blx2						: 8;	// [08 ... 15]
		uint32_t wr2rd_blx2						: 8;	// [16 ... 23]
		uint32_t t_ccd_blx2						: 6;	// [24 ... 29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} DRAMSET1TMG34_t;

typedef union tag_DRAMSET1TMG35 {
	uint32_t value;
	struct {
		uint32_t rda2pre_blx2						: 8;	// [00 ... 07]
		uint32_t wra2pre_blx2						: 8;	// [08 ... 15]
		uint32_t rd2pre_blx2						: 8;	// [16 ... 23]
		uint32_t wr2pre_blx2						: 8;	// [24 ... 31]
	};
} DRAMSET1TMG35_t;

typedef union tag_DRAMSET1TMG36 {
	uint32_t value;
	struct {
		uint32_t rd2wr_s_blx2						: 8;	// [00 ... 07]
		uint32_t wr2rd_s_blx2						: 8;	// [08 ... 15]
		uint32_t t_ccd_s_blx2						: 5;	// [16 ... 20]
		const uint32_t _RESERVED0					: 11;	// [21 ... 31]
	};
} DRAMSET1TMG36_t;

typedef union tag_DRAMSET1TMG37 {
	uint32_t value;
	struct {
		uint32_t max_wr_sync_blx2					: 8;	// [00 ... 07]
		uint32_t max_rd_sync_blx2					: 8;	// [08 ... 15]
		uint32_t wr2mr_blx2						: 8;	// [16 ... 23]
		uint32_t rd2mr_blx2						: 8;	// [24 ... 31]
	};
} DRAMSET1TMG37_t;

typedef union tag_DRAMSET1TMG38 {
	uint32_t value;
	struct {
		uint32_t wr2rd_dr_blx2						: 8;	// [00 ... 07]
		uint32_t rd2wr_dr_blx2						: 8;	// [08 ... 15]
		uint32_t diff_rank_rd_gap_blx2					: 8;	// [16 ... 23]
		uint32_t diff_rank_wr_gap_blx2					: 8;	// [24 ... 31]
	};
} DRAMSET1TMG38_t;

typedef union tag_DRAMSET2TMG0 {
	uint32_t value;
	struct {
		uint32_t t_ras_min_2						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t t_faw_2						: 8;	// [16 ... 23]
		uint32_t wr2pre_2						: 8;	// [24 ... 31]
	};
} DRAMSET2TMG0_t;

typedef union tag_DRAMSET2TMG1 {
	uint32_t value;
	struct {
		uint32_t t_rc_2							: 8;	// [00 ... 07]
		uint32_t rd2pre_2						: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} DRAMSET2TMG1_t;

typedef union tag_DRAMSET2TMG2 {
	uint32_t value;
	struct {
		uint32_t wr2rd_2						: 8;	// [00 ... 07]
		uint32_t rd2wr_2						: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} DRAMSET2TMG2_t;

typedef union tag_DRAMSET2TMG3 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t t_mr_2							: 7;	// [16 ... 22]
		const uint32_t _RESERVED1					: 9;	// [23 ... 31]
	};
} DRAMSET2TMG3_t;

typedef union tag_DRAMSET2TMG4 {
	uint32_t value;
	struct {
		uint32_t t_rp_2							: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_rrd_2						: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 10;	// [14 ... 23]
		uint32_t t_rcd_2						: 8;	// [24 ... 31]
	};
} DRAMSET2TMG4_t;

typedef union tag_DRAMSET2TMG8 {
	uint32_t value;
	struct {
		uint32_t t_xs_x32_2						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_xs_dll_x32_2						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 17;	// [15 ... 31]
	};
} DRAMSET2TMG8_t;

typedef union tag_DRAMSET2TMG9 {
	uint32_t value;
	struct {
		uint32_t wr2rd_s_2						: 8;	// [00 ... 07]
		uint32_t t_rrd_s_2						: 6;	// [08 ... 13]
		const uint32_t _RESERVED0					: 18;	// [14 ... 31]
	};
} DRAMSET2TMG9_t;

typedef union tag_DRAMSET2TMG13 {
	uint32_t value;
	struct {
		uint32_t t_ppd_2						: 4;	// [00 ... 03]
		uint32_t t_ccd_w2_2						: 8;	// [04 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} DRAMSET2TMG13_t;

typedef union tag_DRAMSET2TMG16 {
	uint32_t value;
	struct {
		uint32_t t_ccd_dlr_2						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t t_rrd_dlr_2						: 4;	// [08 ... 11]
		const uint32_t _RESERVED1					: 4;	// [12 ... 15]
		uint32_t t_faw_dlr_2						: 8;	// [16 ... 23]
		uint32_t t_rp_ca_parity_2					: 8;	// [24 ... 31]
	};
} DRAMSET2TMG16_t;

typedef union tag_DRAMSET2TMG22 {
	uint32_t value;
	struct {
		uint32_t t_rd2wr_dpr_2						: 7;	// [00 ... 06]
		uint32_t t_rd2wr_dlr_2						: 7;	// [07 ... 13]
		uint32_t t_wr2rd_dpr_2						: 8;	// [14 ... 21]
		uint32_t t_wr2rd_dlr_2						: 8;	// [22 ... 29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} DRAMSET2TMG22_t;

typedef union tag_DRAMSET2TMG26 {
	uint32_t value;
	struct {
		uint32_t t_ccd_r_2						: 8;	// [00 ... 07]
		uint32_t t_ccd_w_2						: 8;	// [08 ... 15]
		uint32_t t_ccd_r_s_2						: 8;	// [16 ... 23]
		uint32_t t_ccd_w_s_2						: 8;	// [24 ... 31]
	};
} DRAMSET2TMG26_t;

typedef union tag_DRAMSET2TMG27 {
	uint32_t value;
	struct {
		uint32_t t_mrr2mpc_2						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} DRAMSET2TMG27_t;

typedef union tag_DRAMSET2TMG31 {
	uint32_t value;
	struct {
		uint32_t rfm_raaimt_2						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 2;	// [07 ... 08]
		uint32_t rfm_raa_thr_2						: 9;	// [09 ... 17]
		const uint32_t _RESERVED1					: 1;	// [18]
		uint32_t rfm_raa_ref_decr_2					: 2;	// [19 ... 20]
		const uint32_t _RESERVED2					: 11;	// [21 ... 31]
	};
} DRAMSET2TMG31_t;

typedef union tag_DRAMSET2TMG33 {
	uint32_t value;
	struct {
		uint32_t t_ccd_r_m_2						: 8;	// [00 ... 07]
		uint32_t t_ccd_w_m_2						: 8;	// [08 ... 15]
		uint32_t t_wr2rd_m_2						: 8;	// [16 ... 23]
		const uint32_t _RESERVED0					: 8;	// [24 ... 31]
	};
} DRAMSET2TMG33_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL0 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r0r1					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r1r0					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r0r1					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r1r0					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r0r1					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r1r0					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r0r1					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r1r0					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL0_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL1 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r0r2					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r2r0					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r0r2					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r2r0					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r0r2					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r2r0					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r0r2					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r2r0					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL1_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL2 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r0r3					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r3r0					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r0r3					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r3r0					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r0r3					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r3r0					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r0r3					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r3r0					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL2_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL3 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r1r2					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r2r1					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r1r2					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r2r1					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r1r2					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r2r1					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r1r2					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r2r1					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL3_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL4 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r1r3					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r3r1					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r1r3					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r3r1					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r1r3					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r3r1					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r1r3					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r3r1					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL4_t;

typedef union tag_RANK_SWITCH_TIMING_CONTROL5 {
	uint32_t value;
	struct {
		uint32_t t_rd2rd_gap_r2r3					: 4;	// [00 ... 03]
		uint32_t t_rd2rd_gap_r3r2					: 4;	// [04 ... 07]
		uint32_t t_wr2rd_gap_r2r3					: 4;	// [08 ... 11]
		uint32_t t_wr2rd_gap_r3r2					: 4;	// [12 ... 15]
		uint32_t t_rd2wr_gap_r2r3					: 4;	// [16 ... 19]
		uint32_t t_rd2wr_gap_r3r2					: 4;	// [20 ... 23]
		uint32_t t_wr2wr_gap_r2r3					: 4;	// [24 ... 27]
		uint32_t t_wr2wr_gap_r3r2					: 4;	// [28 ... 31]
	};
} RANK_SWITCH_TIMING_CONTROL5_t;

typedef union tag_MRAMTMG0 {
	uint32_t value;
	struct {
		uint32_t t_ras_min_mram						: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t t_faw_mram						: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} MRAMTMG0_t;

typedef union tag_MRAMTMG1 {
	uint32_t value;
	struct {
		uint32_t t_rc_mram						: 9;	// [00 ... 08]
		const uint32_t _RESERVED0					: 23;	// [09 ... 31]
	};
} MRAMTMG1_t;

typedef union tag_MRAMTMG2 {
	uint32_t value;
	struct {
		uint32_t t_rp_mram						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t t_rrd_mram						: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 10;	// [14 ... 23]
		uint32_t t_rcd_mram						: 8;	// [24 ... 31]
	};
} MRAMTMG2_t;

typedef union tag_MRAMTMG3 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 8;	// [00 ... 07]
		uint32_t t_rrd_s_mram						: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 18;	// [14 ... 31]
	};
} MRAMTMG3_t;

typedef union tag_INITMR0 {
	uint32_t value;
	struct {
		uint32_t emr							: 16;	// [00 ... 15]
		uint32_t mr							: 16;	// [16 ... 31]
	};
} INITMR0_t;

typedef union tag_INITMR1 {
	uint32_t value;
	struct {
		uint32_t emr3							: 16;	// [00 ... 15]
		uint32_t emr2							: 16;	// [16 ... 31]
	};
} INITMR1_t;

typedef union tag_INITMR2 {
	uint32_t value;
	struct {
		uint32_t mr5							: 16;	// [00 ... 15]
		uint32_t mr4							: 16;	// [16 ... 31]
	};
} INITMR2_t;

typedef union tag_INITMR3 {
	uint32_t value;
	struct {
		uint32_t mr6							: 16;	// [00 ... 15]
		uint32_t mr22							: 16;	// [16 ... 31]
	};
} INITMR3_t;

typedef union tag_DFITMG0 {
	uint32_t value;
	struct {
		uint32_t dfi_tphy_wrlat						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t dfi_tphy_wrdata					: 6;	// [08 ... 13]
		const uint32_t _RESERVED1					: 2;	// [14 ... 15]
		uint32_t dfi_t_rddata_en					: 7;	// [16 ... 22]
		const uint32_t _RESERVED2					: 1;	// [23]
		uint32_t dfi_t_ctrl_delay					: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} DFITMG0_t;

typedef union tag_DFITMG1 {
	uint32_t value;
	struct {
		uint32_t dfi_t_dram_clk_enable					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t dfi_t_dram_clk_disable					: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t dfi_t_wrdata_delay					: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t dfi_t_parin_lat					: 2;	// [24 ... 25]
		const uint32_t _RESERVED3					: 2;	// [26 ... 27]
		uint32_t dfi_t_cmd_lat						: 4;	// [28 ... 31]
	};
} DFITMG1_t;

typedef union tag_DFITMG2 {
	uint32_t value;
	struct {
		uint32_t dfi_tphy_wrcslat					: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 1;	// [07]
		uint32_t dfi_tphy_rdcslat					: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t dfi_twck_delay						: 6;	// [16 ... 21]
		const uint32_t _RESERVED2					: 10;	// [22 ... 31]
	};
} DFITMG2_t;

typedef union tag_DFITMG3 {
	uint32_t value;
	struct {
		uint32_t dfi_t_geardown_delay					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 27;	// [05 ... 31]
	};
} DFITMG3_t;

typedef union tag_DFITMG4 {
	uint32_t value;
	struct {
		uint32_t dfi_twck_dis						: 8;	// [00 ... 07]
		uint32_t dfi_twck_en_fs						: 8;	// [08 ... 15]
		uint32_t dfi_twck_en_wr						: 8;	// [16 ... 23]
		uint32_t dfi_twck_en_rd						: 8;	// [24 ... 31]
	};
} DFITMG4_t;

typedef union tag_DFITMG5 {
	uint32_t value;
	struct {
		uint32_t dfi_twck_toggle_post					: 8;	// [00 ... 07]
		uint32_t dfi_twck_toggle_cs					: 8;	// [08 ... 15]
		uint32_t dfi_twck_toggle					: 8;	// [16 ... 23]
		uint32_t dfi_twck_fast_toggle					: 8;	// [24 ... 31]
	};
} DFITMG5_t;

typedef union tag_DFITMG6 {
	uint32_t value;
	struct {
		uint32_t dfi_twck_toggle_post_rd				: 8;	// [00 ... 07]
		uint32_t dfi_twck_toggle_post_rd_en				: 1;	// [08]
		const uint32_t _RESERVED0					: 23;	// [09 ... 31]
	};
} DFITMG6_t;

typedef union tag_DFITMG7 {
	uint32_t value;
	struct {
		uint32_t dfi_t_2n_mode_delay					: 5;	// [00 ... 04]
		uint32_t dfi_t_init_start					: 12;	// [05 ... 16]
		uint32_t dfi_t_init_complete					: 15;	// [17 ... 31]
	};
} DFITMG7_t;

typedef union tag_DFILPTMG0 {
	uint32_t value;
	struct {
		uint32_t dfi_lp_wakeup_pd					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t dfi_lp_wakeup_sr					: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 3;	// [13 ... 15]
		uint32_t dfi_lp_wakeup_dsm					: 5;	// [16 ... 20]
		const uint32_t _RESERVED2					: 3;	// [21 ... 23]
		uint32_t dfi_lp_wakeup_mpsm					: 5;	// [24 ... 28]
		const uint32_t _RESERVED3					: 3;	// [29 ... 31]
	};
} DFILPTMG0_t;

typedef union tag_DFILPTMG1 {
	uint32_t value;
	struct {
		uint32_t dfi_lp_wakeup_data					: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 3;	// [05 ... 07]
		uint32_t dfi_tlp_resp						: 5;	// [08 ... 12]
		const uint32_t _RESERVED1					: 19;	// [13 ... 31]
	};
} DFILPTMG1_t;

typedef union tag_DFIUPDTMG0 {
	uint32_t value;
	struct {
		uint32_t dfi_t_ctrlup_min					: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 6;	// [10 ... 15]
		uint32_t dfi_t_ctrlup_max					: 10;	// [16 ... 25]
		uint32_t dfi_ctrlup_gap						: 6;	// [26 ... 31]
	};
} DFIUPDTMG0_t;

typedef union tag_DFIUPDTMG1 {
	uint32_t value;
	struct {
		uint32_t dfi_t_ctrlupd_interval_max_x1024			: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t dfi_t_ctrlupd_interval_min_x1024			: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} DFIUPDTMG1_t;

typedef union tag_DFIMSGTMG0 {
	uint32_t value;
	struct {
		uint32_t dfi_t_ctrlmsg_resp					: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 24;	// [08 ... 31]
	};
} DFIMSGTMG0_t;

typedef union tag_DFIUPDTMG2 {
	uint32_t value;
	struct {
		uint32_t dfi_t_ctrlupd_interval_type1				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 15;	// [12 ... 26]
		uint32_t ctrlupd_after_dqsosc					: 1;	// [27]
		uint32_t ppt2_override						: 1;	// [28]
		uint32_t ppt2_en						: 1;	// [29]
		uint32_t dfi_t_ctrlupd_interval_type1_unit			: 2;	// [30 ... 31]
	};
} DFIUPDTMG2_t;

typedef union tag_DFIUPDTMG3 {
	uint32_t value;
	struct {
		uint32_t dfi_t_ctrlupd_burst_interval_x8			: 9;	// [00 ... 08]
		const uint32_t _RESERVED0					: 23;	// [09 ... 31]
	};
} DFIUPDTMG3_t;

typedef union tag_RFSHSET1TMG0 {
	uint32_t value;
	struct {
		uint32_t t_refi_x1_x32						: 16;	// [00 ... 15]
		uint32_t refresh_to_x1_x32					: 6;	// [16 ... 21]
		const uint32_t _RESERVED0					: 2;	// [22 ... 23]
		uint32_t refresh_margin						: 4;	// [24 ... 27]
		const uint32_t _RESERVED1					: 2;	// [28 ... 29]
		uint32_t refresh_to_x1_sel					: 1;	// [30]
		uint32_t t_refi_x1_sel						: 1;	// [31]
	};
} RFSHSET1TMG0_t;

typedef union tag_RFSHSET1TMG1 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_rfc_min_ab						: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET1TMG1_t;

typedef union tag_RFSHSET1TMG2 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min_dlr						: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 6;	// [10 ... 15]
		uint32_t t_pbr2pbr						: 8;	// [16 ... 23]
		uint32_t t_pbr2act						: 8;	// [24 ... 31]
	};
} RFSHSET1TMG2_t;

typedef union tag_RFSHSET1TMG3 {
	uint32_t value;
	struct {
		uint32_t t_rfcsb						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_refsbrd						: 8;	// [16 ... 23]
		uint32_t refresh_to_ab_x32					: 6;	// [24 ... 29]
		const uint32_t _RESERVED1					: 2;	// [30 ... 31]
	};
} RFSHSET1TMG3_t;

typedef union tag_RFSHSET1TMG4 {
	uint32_t value;
	struct {
		uint32_t refresh_timer0_start_value_x32				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t refresh_timer1_start_value_x32				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET1TMG4_t;

typedef union tag_RFSHSET1TMG5 {
	uint32_t value;
	struct {
		uint32_t refresh_timer2_start_value_x32				: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t refresh_timer3_start_value_x32				: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET1TMG5_t;

typedef union tag_RFSHSET1TMG6 {
	uint32_t value;
	struct {
		uint32_t refresh_timer_lr_offset_x32				: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 21;	// [11 ... 31]
	};
} RFSHSET1TMG6_t;

typedef union tag_RFSHSET1TMG7 {
	uint32_t value;
	struct {
		uint32_t t_rfcsb_dlr						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_refsbrd_dlr						: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} RFSHSET1TMG7_t;

typedef union tag_RFSHSET1TMG8 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min_het						: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 21;	// [11 ... 31]
	};
} RFSHSET1TMG8_t;

typedef union tag_RFSHSET1TMG9 {
	uint32_t value;
	struct {
		uint32_t refab_hi_sch_gap					: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t refsb_hi_sch_gap					: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET1TMG9_t;

typedef union tag_RFSHSET1TMG10 {
	uint32_t value;
	struct {
		uint32_t t_win_size_1xtrefi					: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} RFSHSET1TMG10_t;

typedef union tag_RFSHSET1TMG11 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t t_pbr2pbr_mp						: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} RFSHSET1TMG11_t;

typedef union tag_RFSHSET1TMG12 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min_mp						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_rfc_min_ab_mp					: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET1TMG12_t;

typedef union tag_ECSSET1TMG0 {
	uint32_t value;
	struct {
		uint32_t t_ecs_int_x1024					: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t t_refi_ecs_offset_x1_x32				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} ECSSET1TMG0_t;

typedef union tag_RFMSET1TMG0 {
	uint32_t value;
	struct {
		uint32_t t_rfmpb						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} RFMSET1TMG0_t;

typedef union tag_RFMSET1TMG1 {
	uint32_t value;
	struct {
		uint32_t t_rfmpb_mp						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} RFMSET1TMG1_t;

typedef union tag_RFSHSET2TMG0 {
	uint32_t value;
	struct {
		uint32_t t_refi_x1_x32_2					: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t refresh_to_x1_x32_2					: 6;	// [16 ... 21]
		const uint32_t _RESERVED1					: 2;	// [22 ... 23]
		uint32_t refresh_margin_2					: 4;	// [24 ... 27]
		const uint32_t _RESERVED2					: 4;	// [28 ... 31]
	};
} RFSHSET2TMG0_t;

typedef union tag_RFSHSET2TMG1 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min_2						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} RFSHSET2TMG1_t;

typedef union tag_RFSHSET2TMG2 {
	uint32_t value;
	struct {
		uint32_t t_rfc_min_dlr_2					: 10;	// [00 ... 09]
		const uint32_t _RESERVED0					: 22;	// [10 ... 31]
	};
} RFSHSET2TMG2_t;

typedef union tag_RFSHSET2TMG3 {
	uint32_t value;
	struct {
		uint32_t t_rfcsb_2						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_refsbrd_2						: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} RFSHSET2TMG3_t;

typedef union tag_RFSHSET2TMG6 {
	uint32_t value;
	struct {
		uint32_t refresh_timer_lr_offset_x32_2				: 11;	// [00 ... 10]
		const uint32_t _RESERVED0					: 21;	// [11 ... 31]
	};
} RFSHSET2TMG6_t;

typedef union tag_RFSHSET2TMG7 {
	uint32_t value;
	struct {
		uint32_t t_rfcsb_dlr_2						: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 4;	// [12 ... 15]
		uint32_t t_refsbrd_dlr_2					: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} RFSHSET2TMG7_t;

typedef union tag_RFSHSET2TMG9 {
	uint32_t value;
	struct {
		uint32_t refab_hi_sch_gap_2					: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t refsb_hi_sch_gap_2					: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} RFSHSET2TMG9_t;

typedef union tag_RFSHSET2TMG10 {
	uint32_t value;
	struct {
		uint32_t t_win_size_1xtrefi_2					: 12;	// [00 ... 11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} RFSHSET2TMG10_t;

typedef union tag_ECSSET2TMG0 {
	uint32_t value;
	struct {
		uint32_t t_ecs_int_x1024_2					: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t t_refi_ecs_offset_x1_x32_2				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} ECSSET2TMG0_t;

typedef union tag_ZQSET1TMG0 {
	uint32_t value;
	struct {
		uint32_t t_zq_long_nop						: 14;	// [00 ... 13]
		const uint32_t _RESERVED0					: 2;	// [14 ... 15]
		uint32_t t_zq_short_nop						: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} ZQSET1TMG0_t;

typedef union tag_ZQSET1TMG1 {
	uint32_t value;
	struct {
		uint32_t t_zq_short_interval_x1024				: 20;	// [00 ... 19]
		uint32_t t_zq_reset_nop						: 10;	// [20 ... 29]
		const uint32_t _RESERVED0					: 2;	// [30 ... 31]
	};
} ZQSET1TMG1_t;

typedef union tag_ZQSET1TMG2 {
	uint32_t value;
	struct {
		uint32_t t_zq_stop						: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 25;	// [07 ... 31]
	};
} ZQSET1TMG2_t;

typedef union tag_ZQSET2TMG0 {
	uint32_t value;
	struct {
		uint32_t t_zq_long_nop_2					: 14;	// [00 ... 13]
		const uint32_t _RESERVED0					: 2;	// [14 ... 15]
		uint32_t t_zq_short_nop_2					: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} ZQSET2TMG0_t;

typedef union tag_RCDINIT1 {
	uint32_t value;
	struct {
		uint32_t ctrl_word_1						: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t ctrl_word_2						: 13;	// [16 ... 28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} RCDINIT1_t;

typedef union tag_RCDINIT2 {
	uint32_t value;
	struct {
		uint32_t ctrl_word_3						: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t ctrl_word_4						: 13;	// [16 ... 28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} RCDINIT2_t;

typedef union tag_RCDINIT3 {
	uint32_t value;
	struct {
		uint32_t ctrl_word_5						: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t ctrl_word_6						: 13;	// [16 ... 28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} RCDINIT3_t;

typedef union tag_RCDINIT4 {
	uint32_t value;
	struct {
		uint32_t ctrl_word_7						: 13;	// [00 ... 12]
		const uint32_t _RESERVED0					: 3;	// [13 ... 15]
		uint32_t ctrl_word_8						: 13;	// [16 ... 28]
		const uint32_t _RESERVED1					: 3;	// [29 ... 31]
	};
} RCDINIT4_t;

typedef union tag_HWFFCEX_RANK1 {
	uint32_t value;
	struct {
		uint32_t rank1_mr1_rtt_nom					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		uint32_t rank1_mr2_rtt_wr					: 3;	// [08 ... 10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t rank1_mr5_rtt_park					: 3;	// [16 ... 18]
		const uint32_t _RESERVED2					: 5;	// [19 ... 23]
		uint32_t rank1_mr6_vref_value					: 6;	// [24 ... 29]
		uint32_t rank1_mr6_vref_range					: 1;	// [30]
		const uint32_t _RESERVED3					: 1;	// [31]
	};
} HWFFCEX_RANK1_t;

typedef union tag_HWFFCEX_RANK2 {
	uint32_t value;
	struct {
		uint32_t rank2_mr1_rtt_nom					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		uint32_t rank2_mr2_rtt_wr					: 3;	// [08 ... 10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t rank2_mr5_rtt_park					: 3;	// [16 ... 18]
		const uint32_t _RESERVED2					: 5;	// [19 ... 23]
		uint32_t rank2_mr6_vref_value					: 6;	// [24 ... 29]
		uint32_t rank2_mr6_vref_range					: 1;	// [30]
		const uint32_t _RESERVED3					: 1;	// [31]
	};
} HWFFCEX_RANK2_t;

typedef union tag_HWFFCEX_RANK3 {
	uint32_t value;
	struct {
		uint32_t rank3_mr1_rtt_nom					: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 5;	// [03 ... 07]
		uint32_t rank3_mr2_rtt_wr					: 3;	// [08 ... 10]
		const uint32_t _RESERVED1					: 5;	// [11 ... 15]
		uint32_t rank3_mr5_rtt_park					: 3;	// [16 ... 18]
		const uint32_t _RESERVED2					: 5;	// [19 ... 23]
		uint32_t rank3_mr6_vref_value					: 6;	// [24 ... 29]
		uint32_t rank3_mr6_vref_range					: 1;	// [30]
		const uint32_t _RESERVED3					: 1;	// [31]
	};
} HWFFCEX_RANK3_t;

typedef union tag_DQSOSCCTL0 {
	uint32_t value;
	struct {
		uint32_t dqsosc_enable						: 1;	// [00]
		const uint32_t _RESERVED0					: 1;	// [01]
		uint32_t dqsosc_interval_unit					: 1;	// [02]
		const uint32_t _RESERVED1					: 1;	// [03]
		uint32_t dqsosc_interval					: 12;	// [04 ... 15]
		const uint32_t _RESERVED2					: 16;	// [16 ... 31]
	};
} DQSOSCCTL0_t;

typedef union tag_DERATEINT {
	uint32_t value;
	struct {
		uint32_t mr4_read_interval					: 32;	// [00 ... 31]
	};
} DERATEINT_t;

typedef union tag_DERATEVAL0 {
	uint32_t value;
	struct {
		uint32_t derated_t_rrd						: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		uint32_t derated_t_rp						: 7;	// [08 ... 14]
		const uint32_t _RESERVED1					: 1;	// [15]
		uint32_t derated_t_ras_min					: 8;	// [16 ... 23]
		uint32_t derated_t_rcd						: 8;	// [24 ... 31]
	};
} DERATEVAL0_t;

typedef union tag_DERATEVAL1 {
	uint32_t value;
	struct {
		uint32_t derated_t_rc						: 8;	// [00 ... 07]
		uint32_t derated_t_rcd_write					: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} DERATEVAL1_t;

typedef union tag_HWLPTMG0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t hw_lp_idle_x32						: 12;	// [16 ... 27]
		const uint32_t _RESERVED1					: 4;	// [28 ... 31]
	};
} HWLPTMG0_t;

typedef union tag_DVFSCTL0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t dvfsq_enable						: 1;	// [02]
		const uint32_t _RESERVED1					: 29;	// [03 ... 31]
	};
} DVFSCTL0_t;

typedef union tag_SCHEDTMG0 {
	uint32_t value;
	struct {
		uint32_t pageclose_timer					: 8;	// [00 ... 07]
		uint32_t rdwr_idle_gap						: 7;	// [08 ... 14]
		const uint32_t _RESERVED0					: 17;	// [15 ... 31]
	};
} SCHEDTMG0_t;

typedef union tag_PERFHPR1 {
	uint32_t value;
	struct {
		uint32_t hpr_max_starve						: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t hpr_xact_run_length					: 8;	// [24 ... 31]
	};
} PERFHPR1_t;

typedef union tag_PERFLPR1 {
	uint32_t value;
	struct {
		uint32_t lpr_max_starve						: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t lpr_xact_run_length					: 8;	// [24 ... 31]
	};
} PERFLPR1_t;

typedef union tag_PERFWR1 {
	uint32_t value;
	struct {
		uint32_t w_max_starve						: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t w_xact_run_length					: 8;	// [24 ... 31]
	};
} PERFWR1_t;

typedef union tag_TMGCFG {
	uint32_t value;
	struct {
		uint32_t frequency_ratio					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} TMGCFG_t;

typedef union tag_RANKTMG0 {
	uint32_t value;
	struct {
		uint32_t diff_rank_rd_gap					: 8;	// [00 ... 07]
		uint32_t diff_rank_wr_gap					: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} RANKTMG0_t;

typedef union tag_RANKTMG1 {
	uint32_t value;
	struct {
		uint32_t wr2rd_dr						: 8;	// [00 ... 07]
		uint32_t rd2wr_dr						: 8;	// [08 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} RANKTMG1_t;

typedef union tag_PWRTMG {
	uint32_t value;
	struct {
		uint32_t powerdown_to_x32					: 7;	// [00 ... 06]
		const uint32_t _RESERVED0					: 9;	// [07 ... 15]
		uint32_t selfref_to_x32						: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 6;	// [26 ... 31]
	};
} PWRTMG_t;

typedef union tag_ODTCFG {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t rd_odt_delay						: 5;	// [02 ... 06]
		const uint32_t _RESERVED1					: 1;	// [07]
		uint32_t rd_odt_hold						: 4;	// [08 ... 11]
		const uint32_t _RESERVED2					: 4;	// [12 ... 15]
		uint32_t wr_odt_delay						: 5;	// [16 ... 20]
		const uint32_t _RESERVED3					: 3;	// [21 ... 23]
		uint32_t wr_odt_hold						: 4;	// [24 ... 27]
		const uint32_t _RESERVED4					: 4;	// [28 ... 31]
	};
} ODTCFG_t;

typedef union tag_CRCPARTMG0 {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 16;	// [00 ... 15]
		uint32_t t_wr_crc_alert_pw_max					: 10;	// [16 ... 25]
		const uint32_t _RESERVED1					: 2;	// [26 ... 27]
		uint32_t t_wr_crc_alert_pw_min					: 4;	// [28 ... 31]
	};
} CRCPARTMG0_t;

typedef union tag_CRCPARTMG1 {
	uint32_t value;
	struct {
		uint32_t t_csalt						: 5;	// [00 ... 04]
		const uint32_t _RESERVED0					: 27;	// [05 ... 31]
	};
} CRCPARTMG1_t;

typedef union tag_RETRYTMG0 {
	uint32_t value;
	struct {
		uint32_t capar_retry_window					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 10;	// [06 ... 15]
		uint32_t t_wr_crc_retry_window					: 9;	// [16 ... 24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} RETRYTMG0_t;

typedef union tag_RETRYTMG1 {
	uint32_t value;
	struct {
		uint32_t dfi_t_phy_rdlat					: 8;	// [00 ... 07]
		uint32_t extra_rd_retry_window					: 6;	// [08 ... 13]
		const uint32_t _RESERVED0					: 2;	// [14 ... 15]
		uint32_t retry_add_rd_lat					: 8;	// [16 ... 23]
		uint32_t retry_add_rd_lat_en					: 1;	// [24]
		const uint32_t _RESERVED1					: 7;	// [25 ... 31]
	};
} RETRYTMG1_t;

typedef union tag_DDR4PPRTMG0 {
	uint32_t value;
	struct {
		uint32_t t_pgm_x1_x1024						: 22;	// [00 ... 21]
		const uint32_t _RESERVED0					: 9;	// [22 ... 30]
		uint32_t t_pgm_x1_sel						: 1;	// [31]
	};
} DDR4PPRTMG0_t;

typedef union tag_DDR4PPRTMG1 {
	uint32_t value;
	struct {
		uint32_t t_pgmpst_x32						: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 8;	// [16 ... 23]
		uint32_t t_pgm_exit						: 6;	// [24 ... 29]
		const uint32_t _RESERVED1					: 2;	// [30 ... 31]
	};
} DDR4PPRTMG1_t;

typedef union tag_LNKECCCTL0 {
	uint32_t value;
	struct {
		uint32_t wr_link_ecc_enable					: 1;	// [00]
		uint32_t rd_link_ecc_enable					: 1;	// [01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} LNKECCCTL0_t;

typedef union tag_IME_VER_NUM {
	uint32_t value;
	struct {
		const uint32_t ver_num						: 16;	// [00 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_VER_NUM_t;

typedef union tag_IME_VER_TYPE {
	uint32_t value;
	struct {
		const uint32_t type_num						: 8;	// [00 ... 07]
		const uint32_t pkg_num						: 4;	// [08 ... 11]
		const uint32_t type_enum					: 4;	// [12 ... 15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_VER_TYPE_t;

typedef union tag_IME_KEY_LOAD_IRQ_EN {
	uint32_t value;
	struct {
		uint32_t key_done_en						: 1;	// [00]
		const uint32_t _RESERVED0					: 5;	// [01 ... 05]
		uint32_t key_miss_err_en					: 1;	// [06]
		uint32_t key_collision_err_en					: 1;	// [07]
		uint32_t apb_timing_err_en					: 1;	// [08]
		uint32_t key_size_err_en					: 1;	// [09]
		const uint32_t _RESERVED1					: 6;	// [10 ... 15]
		uint32_t reg_parity_err_en					: 1;	// [16]
		const uint32_t _RESERVED2					: 14;	// [17 ... 30]
		uint32_t glbl							: 1;	// [31]
	};
} IME_KEY_LOAD_IRQ_EN_t;

typedef union tag_IME_KEY_LOAD_IRQ_STAT {
	uint32_t value;
	struct {
		uint32_t key_done						: 1;	// [00]
		const uint32_t _RESERVED0					: 5;	// [01 ... 05]
		uint32_t key_miss_err						: 1;	// [06]
		uint32_t key_collision_err					: 1;	// [07]
		uint32_t apb_timing_err						: 1;	// [08]
		uint32_t key_size_err						: 1;	// [09]
		const uint32_t _RESERVED1					: 6;	// [10 ... 15]
		uint32_t reg_parity_err						: 1;	// [16]
		const uint32_t _RESERVED2					: 15;	// [17 ... 31]
	};
} IME_KEY_LOAD_IRQ_STAT_t;

typedef union tag_IME_KEY_USAGE_IRQ_EN {
	uint32_t value;
	struct {
		uint32_t key0_usage_hit_en					: 1;	// [00]
		uint32_t key1_usage_hit_en					: 1;	// [01]
		uint32_t key2_usage_hit_en					: 1;	// [02]
		uint32_t key3_usage_hit_en					: 1;	// [03]
		uint32_t key4_usage_hit_en					: 1;	// [04]
		uint32_t key5_usage_hit_en					: 1;	// [05]
		uint32_t key6_usage_hit_en					: 1;	// [06]
		uint32_t key7_usage_hit_en					: 1;	// [07]
		uint32_t key8_usage_hit_en					: 1;	// [08]
		uint32_t key9_usage_hit_en					: 1;	// [09]
		uint32_t key10_usage_hit_en					: 1;	// [10]
		uint32_t key11_usage_hit_en					: 1;	// [11]
		uint32_t key12_usage_hit_en					: 1;	// [12]
		uint32_t key13_usage_hit_en					: 1;	// [13]
		uint32_t key14_usage_hit_en					: 1;	// [14]
		uint32_t key15_usage_hit_en					: 1;	// [15]
		uint32_t key0_swapped_en					: 1;	// [16]
		uint32_t key1_swapped_en					: 1;	// [17]
		uint32_t key2_swapped_en					: 1;	// [18]
		uint32_t key3_swapped_en					: 1;	// [19]
		uint32_t key4_swapped_en					: 1;	// [20]
		uint32_t key5_swapped_en					: 1;	// [21]
		uint32_t key6_swapped_en					: 1;	// [22]
		uint32_t key7_swapped_en					: 1;	// [23]
		uint32_t key8_swapped_en					: 1;	// [24]
		uint32_t key9_swapped_en					: 1;	// [25]
		uint32_t key10_swapped_en					: 1;	// [26]
		uint32_t key11_swapped_en					: 1;	// [27]
		uint32_t key12_swapped_en					: 1;	// [28]
		uint32_t key13_swapped_en					: 1;	// [29]
		uint32_t key14_swapped_en					: 1;	// [30]
		uint32_t key15_swapped_en					: 1;	// [31]
	};
} IME_KEY_USAGE_IRQ_EN_t;

typedef union tag_IME_KEY_USAGE_IRQ_STAT {
	uint32_t value;
	struct {
		uint32_t key0_usage_hit						: 1;	// [00]
		uint32_t key1_usage_hit						: 1;	// [01]
		uint32_t key2_usage_hit						: 1;	// [02]
		uint32_t key3_usage_hit						: 1;	// [03]
		uint32_t key4_usage_hit						: 1;	// [04]
		uint32_t key5_usage_hit						: 1;	// [05]
		uint32_t key6_usage_hit						: 1;	// [06]
		uint32_t key7_usage_hit						: 1;	// [07]
		uint32_t key8_usage_hit						: 1;	// [08]
		uint32_t key9_usage_hit						: 1;	// [09]
		uint32_t key10_usage_hit					: 1;	// [10]
		uint32_t key11_usage_hit					: 1;	// [11]
		uint32_t key12_usage_hit					: 1;	// [12]
		uint32_t key13_usage_hit					: 1;	// [13]
		uint32_t key14_usage_hit					: 1;	// [14]
		uint32_t key15_usage_hit					: 1;	// [15]
		uint32_t key0_swapped						: 1;	// [16]
		uint32_t key1_swapped						: 1;	// [17]
		uint32_t key2_swapped						: 1;	// [18]
		uint32_t key3_swapped						: 1;	// [19]
		uint32_t key4_swapped						: 1;	// [20]
		uint32_t key5_swapped						: 1;	// [21]
		uint32_t key6_swapped						: 1;	// [22]
		uint32_t key7_swapped						: 1;	// [23]
		uint32_t key8_swapped						: 1;	// [24]
		uint32_t key9_swapped						: 1;	// [25]
		uint32_t key10_swapped						: 1;	// [26]
		uint32_t key11_swapped						: 1;	// [27]
		uint32_t key12_swapped						: 1;	// [28]
		uint32_t key13_swapped						: 1;	// [29]
		uint32_t key14_swapped						: 1;	// [30]
		uint32_t key15_swapped						: 1;	// [31]
	};
} IME_KEY_USAGE_IRQ_STAT_t;

typedef union tag_IME_BUILD_CONFIG_REG0 {
	uint32_t value;
	struct {
		const uint32_t dp_width						: 2;	// [00 ... 01]
		const uint32_t _RESERVED0					: 7;	// [02 ... 08]
		const uint32_t key256_en					: 1;	// [09]
		const uint32_t key512_en					: 1;	// [10]
		const uint32_t _RESERVED1					: 3;	// [11 ... 13]
		const uint32_t aes_ecb_en					: 1;	// [14]
		const uint32_t _RESERVED2					: 4;	// [15 ... 18]
		const uint32_t apb4_en						: 1;	// [19]
		const uint32_t apb5_e_en					: 1;	// [20]
		const uint32_t _RESERVED3					: 11;	// [21 ... 31]
	};
} IME_BUILD_CONFIG_REG0_t;

typedef union tag_IME_SOFTWARE_BW_CTRL {
	uint32_t value;
	struct {
		const uint32_t software_bw_ctrl					: 2;	// [00 ... 01]
		const uint32_t _RESERVED0					: 30;	// [02 ... 31]
	};
} IME_SOFTWARE_BW_CTRL_t;

typedef union tag_IME_REGION0_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region0_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION0_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION0_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region0_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION0_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION0_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region0_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION0_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION0_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region0_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION0_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION1_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region1_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION1_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION1_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region1_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION1_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION1_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region1_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION1_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION1_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region1_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION1_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION2_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region2_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION2_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION2_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region2_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION2_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION2_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region2_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION2_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION2_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region2_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION2_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION3_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region3_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION3_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION3_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region3_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION3_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION3_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region3_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION3_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION3_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region3_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION3_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION4_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region4_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION4_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION4_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region4_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION4_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION4_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region4_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION4_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION4_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region4_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION4_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION5_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region5_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION5_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION5_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region5_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION5_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION5_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region5_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION5_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION5_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region5_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION5_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION6_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region6_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION6_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION6_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region6_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION6_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION6_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region6_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION6_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION6_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region6_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION6_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION7_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region7_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION7_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION7_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region7_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION7_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION7_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region7_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION7_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION7_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region7_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION7_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION8_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region8_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION8_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION8_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region8_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION8_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION8_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region8_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION8_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION8_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region8_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION8_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION9_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region9_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION9_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION9_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region9_addr_low_63_32					: 32;	// [00 ... 31]
	};
} IME_REGION9_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION9_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region9_addr_high_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION9_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION9_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region9_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION9_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION10_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region10_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION10_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION10_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region10_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION10_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION10_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region10_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION10_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION10_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region10_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION10_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION11_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region11_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION11_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION11_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region11_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION11_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION11_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region11_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION11_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION11_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region11_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION11_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION12_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region12_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION12_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION12_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region12_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION12_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION12_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region12_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION12_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION12_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region12_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION12_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION13_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region13_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION13_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION13_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region13_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION13_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION13_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region13_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION13_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION13_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region13_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION13_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION14_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region14_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION14_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION14_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region14_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION14_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION14_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region14_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION14_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION14_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region14_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION14_ADDR_HIGH_63_32_t;

typedef union tag_IME_REGION15_ADDR_LOW_31_0 {
	uint32_t value;
	struct {
		uint32_t region15_addr_low_31_0					: 32;	// [00 ... 31]
	};
} IME_REGION15_ADDR_LOW_31_0_t;

typedef union tag_IME_REGION15_ADDR_LOW_63_32 {
	uint32_t value;
	struct {
		uint32_t region15_addr_low_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION15_ADDR_LOW_63_32_t;

typedef union tag_IME_REGION15_ADDR_HIGH_31_0 {
	uint32_t value;
	struct {
		uint32_t region15_addr_high_31_0				: 32;	// [00 ... 31]
	};
} IME_REGION15_ADDR_HIGH_31_0_t;

typedef union tag_IME_REGION15_ADDR_HIGH_63_32 {
	uint32_t value;
	struct {
		uint32_t region15_addr_high_63_32				: 32;	// [00 ... 31]
	};
} IME_REGION15_ADDR_HIGH_63_32_t;

typedef union tag_IME_KEY0_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key0_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY0_USAGE_THR_31_0_t;

typedef union tag_IME_KEY0_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key0_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY0_USAGE_THR_63_32_t;

typedef union tag_IME_KEY1_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key1_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY1_USAGE_THR_31_0_t;

typedef union tag_IME_KEY1_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key1_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY1_USAGE_THR_63_32_t;

typedef union tag_IME_KEY2_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key2_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY2_USAGE_THR_31_0_t;

typedef union tag_IME_KEY2_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key2_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY2_USAGE_THR_63_32_t;

typedef union tag_IME_KEY3_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key3_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY3_USAGE_THR_31_0_t;

typedef union tag_IME_KEY3_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key3_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY3_USAGE_THR_63_32_t;

typedef union tag_IME_KEY4_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key4_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY4_USAGE_THR_31_0_t;

typedef union tag_IME_KEY4_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key4_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY4_USAGE_THR_63_32_t;

typedef union tag_IME_KEY5_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key5_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY5_USAGE_THR_31_0_t;

typedef union tag_IME_KEY5_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key5_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY5_USAGE_THR_63_32_t;

typedef union tag_IME_KEY6_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key6_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY6_USAGE_THR_31_0_t;

typedef union tag_IME_KEY6_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key6_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY6_USAGE_THR_63_32_t;

typedef union tag_IME_KEY7_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key7_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY7_USAGE_THR_31_0_t;

typedef union tag_IME_KEY7_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key7_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY7_USAGE_THR_63_32_t;

typedef union tag_IME_KEY8_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key8_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY8_USAGE_THR_31_0_t;

typedef union tag_IME_KEY8_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key8_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY8_USAGE_THR_63_32_t;

typedef union tag_IME_KEY9_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key9_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY9_USAGE_THR_31_0_t;

typedef union tag_IME_KEY9_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key9_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY9_USAGE_THR_63_32_t;

typedef union tag_IME_KEY10_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key10_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY10_USAGE_THR_31_0_t;

typedef union tag_IME_KEY10_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key10_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY10_USAGE_THR_63_32_t;

typedef union tag_IME_KEY11_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key11_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY11_USAGE_THR_31_0_t;

typedef union tag_IME_KEY11_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key11_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY11_USAGE_THR_63_32_t;

typedef union tag_IME_KEY12_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key12_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY12_USAGE_THR_31_0_t;

typedef union tag_IME_KEY12_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key12_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY12_USAGE_THR_63_32_t;

typedef union tag_IME_KEY13_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key13_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY13_USAGE_THR_31_0_t;

typedef union tag_IME_KEY13_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key13_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY13_USAGE_THR_63_32_t;

typedef union tag_IME_KEY14_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key14_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY14_USAGE_THR_31_0_t;

typedef union tag_IME_KEY14_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key14_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY14_USAGE_THR_63_32_t;

typedef union tag_IME_KEY15_USAGE_THR_31_0 {
	uint32_t value;
	struct {
		uint32_t key15_usage_thr_31_0					: 32;	// [00 ... 31]
	};
} IME_KEY15_USAGE_THR_31_0_t;

typedef union tag_IME_KEY15_USAGE_THR_63_32 {
	uint32_t value;
	struct {
		uint32_t key15_usage_thr_63_32					: 32;	// [00 ... 31]
	};
} IME_KEY15_USAGE_THR_63_32_t;

typedef union tag_IME_KEY_USAGE_AUTO_CLEAR {
	uint32_t value;
	struct {
		uint32_t key0_usage_auto_clear					: 1;	// [00]
		uint32_t key1_usage_auto_clear					: 1;	// [01]
		uint32_t key2_usage_auto_clear					: 1;	// [02]
		uint32_t key3_usage_auto_clear					: 1;	// [03]
		uint32_t key4_usage_auto_clear					: 1;	// [04]
		uint32_t key5_usage_auto_clear					: 1;	// [05]
		uint32_t key6_usage_auto_clear					: 1;	// [06]
		uint32_t key7_usage_auto_clear					: 1;	// [07]
		uint32_t key8_usage_auto_clear					: 1;	// [08]
		uint32_t key9_usage_auto_clear					: 1;	// [09]
		uint32_t key10_usage_auto_clear					: 1;	// [10]
		uint32_t key11_usage_auto_clear					: 1;	// [11]
		uint32_t key12_usage_auto_clear					: 1;	// [12]
		uint32_t key13_usage_auto_clear					: 1;	// [13]
		uint32_t key14_usage_auto_clear					: 1;	// [14]
		uint32_t key15_usage_auto_clear					: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_KEY_USAGE_AUTO_CLEAR_t;

typedef union tag_IME_KEY_USAGE_EN {
	uint32_t value;
	struct {
		uint32_t key0_usage_en						: 1;	// [00]
		uint32_t key1_usage_en						: 1;	// [01]
		uint32_t key2_usage_en						: 1;	// [02]
		uint32_t key3_usage_en						: 1;	// [03]
		uint32_t key4_usage_en						: 1;	// [04]
		uint32_t key5_usage_en						: 1;	// [05]
		uint32_t key6_usage_en						: 1;	// [06]
		uint32_t key7_usage_en						: 1;	// [07]
		uint32_t key8_usage_en						: 1;	// [08]
		uint32_t key9_usage_en						: 1;	// [09]
		uint32_t key10_usage_en						: 1;	// [10]
		uint32_t key11_usage_en						: 1;	// [11]
		uint32_t key12_usage_en						: 1;	// [12]
		uint32_t key13_usage_en						: 1;	// [13]
		uint32_t key14_usage_en						: 1;	// [14]
		uint32_t key15_usage_en						: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_KEY_USAGE_EN_t;

typedef union tag_IME_KEY0_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key0_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY0_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY0_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key0_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY0_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY1_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key1_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY1_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY1_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key1_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY1_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY2_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key2_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY2_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY2_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key2_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY2_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY3_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key3_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY3_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY3_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key3_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY3_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY4_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key4_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY4_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY4_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key4_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY4_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY5_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key5_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY5_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY5_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key5_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY5_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY6_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key6_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY6_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY6_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key6_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY6_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY7_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key7_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY7_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY7_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key7_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY7_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY8_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key8_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY8_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY8_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key8_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY8_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY9_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key9_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY9_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY9_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key9_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY9_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY10_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key10_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY10_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY10_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key10_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY10_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY11_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key11_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY11_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY11_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key11_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY11_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY12_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key12_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY12_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY12_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key12_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY12_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY13_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key13_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY13_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY13_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key13_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY13_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY14_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key14_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY14_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY14_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key14_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY14_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY15_USAGE_CNT_STATUS_31_0 {
	uint32_t value;
	struct {
		const uint32_t key15_usage_cnt_status_31_0			: 32;	// [00 ... 31]
	};
} IME_KEY15_USAGE_CNT_STATUS_31_0_t;

typedef union tag_IME_KEY15_USAGE_CNT_STATUS_63_32 {
	uint32_t value;
	struct {
		const uint32_t key15_usage_cnt_status_63_32			: 32;	// [00 ... 31]
	};
} IME_KEY15_USAGE_CNT_STATUS_63_32_t;

typedef union tag_IME_KEY_LOAD_CTRL {
	uint32_t value;
	struct {
		uint32_t key_idx						: 16;	// [00 ... 15]
		uint32_t key_slot_sel						: 1;	// [16]
		uint32_t key_invalidate						: 1;	// [17]
		const uint32_t _RESERVED0					: 2;	// [18 ... 19]
		uint32_t key_sz							: 1;	// [20]
		const uint32_t _RESERVED1					: 1;	// [21]
		uint32_t bypass_sel						: 1;	// [22]
		const uint32_t _RESERVED2					: 9;	// [23 ... 31]
	};
} IME_KEY_LOAD_CTRL_t;

typedef union tag_IME_KEY_LOAD_STAT {
	uint32_t value;
	struct {
		const uint32_t busy						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_KEY_LOAD_STAT_t;

typedef union tag_IME_KEY_SWAP_FORCE_CTRL {
	uint32_t value;
	struct {
		uint32_t key0_swap_force					: 1;	// [00]
		uint32_t key1_swap_force					: 1;	// [01]
		uint32_t key2_swap_force					: 1;	// [02]
		uint32_t key3_swap_force					: 1;	// [03]
		uint32_t key4_swap_force					: 1;	// [04]
		uint32_t key5_swap_force					: 1;	// [05]
		uint32_t key6_swap_force					: 1;	// [06]
		uint32_t key7_swap_force					: 1;	// [07]
		uint32_t key8_swap_force					: 1;	// [08]
		uint32_t key9_swap_force					: 1;	// [09]
		uint32_t key10_swap_force					: 1;	// [10]
		uint32_t key11_swap_force					: 1;	// [11]
		uint32_t key12_swap_force					: 1;	// [12]
		uint32_t key13_swap_force					: 1;	// [13]
		uint32_t key14_swap_force					: 1;	// [14]
		uint32_t key15_swap_force					: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_KEY_SWAP_FORCE_CTRL_t;

typedef union tag_IME_KEY_RMW_SWAP_EN {
	uint32_t value;
	struct {
		uint32_t key0_rmw_swap_en					: 1;	// [00]
		uint32_t key1_rmw_swap_en					: 1;	// [01]
		uint32_t key2_rmw_swap_en					: 1;	// [02]
		uint32_t key3_rmw_swap_en					: 1;	// [03]
		uint32_t key4_rmw_swap_en					: 1;	// [04]
		uint32_t key5_rmw_swap_en					: 1;	// [05]
		uint32_t key6_rmw_swap_en					: 1;	// [06]
		uint32_t key7_rmw_swap_en					: 1;	// [07]
		uint32_t key8_rmw_swap_en					: 1;	// [08]
		uint32_t key9_rmw_swap_en					: 1;	// [09]
		uint32_t key10_rmw_swap_en					: 1;	// [10]
		uint32_t key11_rmw_swap_en					: 1;	// [11]
		uint32_t key12_rmw_swap_en					: 1;	// [12]
		uint32_t key13_rmw_swap_en					: 1;	// [13]
		uint32_t key14_rmw_swap_en					: 1;	// [14]
		uint32_t key15_rmw_swap_en					: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_KEY_RMW_SWAP_EN_t;

typedef union tag_IME_KEY_SWAP_STATUS {
	uint32_t value;
	struct {
		const uint32_t key0_swap_status					: 1;	// [00]
		const uint32_t key1_swap_status					: 1;	// [01]
		const uint32_t key2_swap_status					: 1;	// [02]
		const uint32_t key3_swap_status					: 1;	// [03]
		const uint32_t key4_swap_status					: 1;	// [04]
		const uint32_t key5_swap_status					: 1;	// [05]
		const uint32_t key6_swap_status					: 1;	// [06]
		const uint32_t key7_swap_status					: 1;	// [07]
		const uint32_t key8_swap_status					: 1;	// [08]
		const uint32_t key9_swap_status					: 1;	// [09]
		const uint32_t key10_swap_status				: 1;	// [10]
		const uint32_t key11_swap_status				: 1;	// [11]
		const uint32_t key12_swap_status				: 1;	// [12]
		const uint32_t key13_swap_status				: 1;	// [13]
		const uint32_t key14_swap_status				: 1;	// [14]
		const uint32_t key15_swap_status				: 1;	// [15]
		const uint32_t _RESERVED0					: 16;	// [16 ... 31]
	};
} IME_KEY_SWAP_STATUS_t;

typedef union tag_IME_CKEY_0 {
	uint32_t value;
	struct {
		const uint32_t ckey_0						: 32;	// [00 ... 31]
	};
} IME_CKEY_0_t;

typedef union tag_IME_CKEY_1 {
	uint32_t value;
	struct {
		const uint32_t ckey_1						: 32;	// [00 ... 31]
	};
} IME_CKEY_1_t;

typedef union tag_IME_CKEY_2 {
	uint32_t value;
	struct {
		const uint32_t ckey_2						: 32;	// [00 ... 31]
	};
} IME_CKEY_2_t;

typedef union tag_IME_CKEY_3 {
	uint32_t value;
	struct {
		const uint32_t ckey_3						: 32;	// [00 ... 31]
	};
} IME_CKEY_3_t;

typedef union tag_IME_CKEY_4 {
	uint32_t value;
	struct {
		const uint32_t ckey_4						: 32;	// [00 ... 31]
	};
} IME_CKEY_4_t;

typedef union tag_IME_CKEY_5 {
	uint32_t value;
	struct {
		const uint32_t ckey_5						: 32;	// [00 ... 31]
	};
} IME_CKEY_5_t;

typedef union tag_IME_CKEY_6 {
	uint32_t value;
	struct {
		const uint32_t ckey_6						: 32;	// [00 ... 31]
	};
} IME_CKEY_6_t;

typedef union tag_IME_CKEY_7 {
	uint32_t value;
	struct {
		const uint32_t ckey_7						: 32;	// [00 ... 31]
	};
} IME_CKEY_7_t;

typedef union tag_IME_TKEY_0 {
	uint32_t value;
	struct {
		const uint32_t tkey_0						: 32;	// [00 ... 31]
	};
} IME_TKEY_0_t;

typedef union tag_IME_TKEY_1 {
	uint32_t value;
	struct {
		const uint32_t tkey_1						: 32;	// [00 ... 31]
	};
} IME_TKEY_1_t;

typedef union tag_IME_TKEY_2 {
	uint32_t value;
	struct {
		const uint32_t tkey_2						: 32;	// [00 ... 31]
	};
} IME_TKEY_2_t;

typedef union tag_IME_TKEY_3 {
	uint32_t value;
	struct {
		const uint32_t tkey_3						: 32;	// [00 ... 31]
	};
} IME_TKEY_3_t;

typedef union tag_IME_TKEY_4 {
	uint32_t value;
	struct {
		const uint32_t tkey_4						: 32;	// [00 ... 31]
	};
} IME_TKEY_4_t;

typedef union tag_IME_TKEY_5 {
	uint32_t value;
	struct {
		const uint32_t tkey_5						: 32;	// [00 ... 31]
	};
} IME_TKEY_5_t;

typedef union tag_IME_TKEY_6 {
	uint32_t value;
	struct {
		const uint32_t tkey_6						: 32;	// [00 ... 31]
	};
} IME_TKEY_6_t;

typedef union tag_IME_TKEY_7 {
	uint32_t value;
	struct {
		const uint32_t tkey_7						: 32;	// [00 ... 31]
	};
} IME_TKEY_7_t;

typedef union tag_IME_POISON_CFG {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_poison_en					: 1;	// [00]
		uint32_t wrch_ckey_poison_en					: 1;	// [01]
		uint32_t wrch_tval_poison_en					: 1;	// [02]
		uint32_t rdch_tkey_poison_en					: 1;	// [03]
		uint32_t rdch_ckey_poison_en					: 1;	// [04]
		uint32_t rdch_tval_poison_en					: 1;	// [05]
		uint32_t wrch_tkey_poison_bit					: 1;	// [06]
		uint32_t wrch_ckey_poison_bit					: 1;	// [07]
		uint32_t wrch_tval_poison_bit					: 1;	// [08]
		uint32_t rdch_tkey_poison_bit					: 1;	// [09]
		uint32_t rdch_ckey_poison_bit					: 1;	// [10]
		uint32_t rdch_tval_poison_bit					: 1;	// [11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} IME_POISON_CFG_t;

typedef union tag_IME_WRCH_TKEY_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_flip_bit_pos0				: 16;	// [00 ... 15]
		uint32_t wrch_tkey_flip_bit_pos1				: 16;	// [16 ... 31]
	};
} IME_WRCH_TKEY_FLIP_BIT_POS_t;

typedef union tag_IME_WRCH_CKEY_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t wrch_ckey_flip_bit_pos0				: 16;	// [00 ... 15]
		uint32_t wrch_ckey_flip_bit_pos1				: 16;	// [16 ... 31]
	};
} IME_WRCH_CKEY_FLIP_BIT_POS_t;

typedef union tag_IME_WRCH_TVAL_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t wrch_tval_flip_bit_pos0				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t wrch_tval_flip_bit_pos1				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} IME_WRCH_TVAL_FLIP_BIT_POS_t;

typedef union tag_IME_RDCH_TKEY_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t rdch_tkey_flip_bit_pos0				: 16;	// [00 ... 15]
		uint32_t rdch_tkey_flip_bit_pos1				: 16;	// [16 ... 31]
	};
} IME_RDCH_TKEY_FLIP_BIT_POS_t;

typedef union tag_IME_RDCH_CKEY_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t rdch_ckey_flip_bit_pos0				: 16;	// [00 ... 15]
		uint32_t rdch_ckey_flip_bit_pos1				: 16;	// [16 ... 31]
	};
} IME_RDCH_CKEY_FLIP_BIT_POS_t;

typedef union tag_IME_RDCH_TVAL_FLIP_BIT_POS {
	uint32_t value;
	struct {
		uint32_t rdch_tval_flip_bit_pos0				: 8;	// [00 ... 07]
		const uint32_t _RESERVED0					: 8;	// [08 ... 15]
		uint32_t rdch_tval_flip_bit_pos1				: 8;	// [16 ... 23]
		const uint32_t _RESERVED1					: 8;	// [24 ... 31]
	};
} IME_RDCH_TVAL_FLIP_BIT_POS_t;

typedef union tag_IME_WRCH_TKEY_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_poison_addr					: 32;	// [00 ... 31]
	};
} IME_WRCH_TKEY_POISON_ADDR_t;

typedef union tag_IME_WRCH_CKEY_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t wrch_ckey_poison_addr					: 32;	// [00 ... 31]
	};
} IME_WRCH_CKEY_POISON_ADDR_t;

typedef union tag_IME_WRCH_TVAL_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t wrch_tval_poison_addr					: 32;	// [00 ... 31]
	};
} IME_WRCH_TVAL_POISON_ADDR_t;

typedef union tag_IME_RDCH_TKEY_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t rdch_tkey_poison_addr					: 32;	// [00 ... 31]
	};
} IME_RDCH_TKEY_POISON_ADDR_t;

typedef union tag_IME_RDCH_CKEY_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t rdch_ckey_poison_addr					: 32;	// [00 ... 31]
	};
} IME_RDCH_CKEY_POISON_ADDR_t;

typedef union tag_IME_RDCH_TVAL_POISON_ADDR {
	uint32_t value;
	struct {
		uint32_t rdch_tval_poison_addr					: 32;	// [00 ... 31]
	};
} IME_RDCH_TVAL_POISON_ADDR_t;

typedef union tag_IME_ECC_ERR_STAT {
	uint32_t value;
	struct {
		const uint32_t wrch_tkey_eccc_stat				: 1;	// [00]
		const uint32_t wrch_tkey_eccu_stat				: 1;	// [01]
		const uint32_t wrch_ckey_eccc_stat				: 1;	// [02]
		const uint32_t wrch_ckey_eccu_stat				: 1;	// [03]
		const uint32_t wrch_tval_eccc_stat				: 1;	// [04]
		const uint32_t wrch_tval_eccu_stat				: 1;	// [05]
		const uint32_t rdch_tkey_eccc_stat				: 1;	// [06]
		const uint32_t rdch_tkey_eccu_stat				: 1;	// [07]
		const uint32_t rdch_ckey_eccc_stat				: 1;	// [08]
		const uint32_t rdch_ckey_eccu_stat				: 1;	// [09]
		const uint32_t rdch_tval_eccc_stat				: 1;	// [10]
		const uint32_t rdch_tval_eccu_stat				: 1;	// [11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} IME_ECC_ERR_STAT_t;

typedef union tag_IME_WRCH_ECCC_SYN {
	uint32_t value;
	struct {
		const uint32_t wrch_tkey_eccc_syn				: 10;	// [00 ... 09]
		const uint32_t wrch_ckey_eccc_syn				: 10;	// [10 ... 19]
		const uint32_t wrch_tval_eccc_syn				: 9;	// [20 ... 28]
		const uint32_t _RESERVED0					: 3;	// [29 ... 31]
	};
} IME_WRCH_ECCC_SYN_t;

typedef union tag_IME_WRCH_ECCU_SYN {
	uint32_t value;
	struct {
		const uint32_t wrch_tkey_eccu_syn				: 10;	// [00 ... 09]
		const uint32_t wrch_ckey_eccu_syn				: 10;	// [10 ... 19]
		const uint32_t wrch_tval_eccu_syn				: 9;	// [20 ... 28]
		const uint32_t _RESERVED0					: 3;	// [29 ... 31]
	};
} IME_WRCH_ECCU_SYN_t;

typedef union tag_IME_RDCH_ECCC_SYN {
	uint32_t value;
	struct {
		const uint32_t rdch_tkey_eccc_syn				: 10;	// [00 ... 09]
		const uint32_t rdch_ckey_eccc_syn				: 10;	// [10 ... 19]
		const uint32_t rdch_tval_eccc_syn				: 9;	// [20 ... 28]
		const uint32_t _RESERVED0					: 3;	// [29 ... 31]
	};
} IME_RDCH_ECCC_SYN_t;

typedef union tag_IME_RDCH_ECCU_SYN {
	uint32_t value;
	struct {
		const uint32_t rdch_tkey_eccu_syn				: 10;	// [00 ... 09]
		const uint32_t rdch_ckey_eccu_syn				: 10;	// [10 ... 19]
		const uint32_t rdch_tval_eccu_syn				: 9;	// [20 ... 28]
		const uint32_t _RESERVED0					: 3;	// [29 ... 31]
	};
} IME_RDCH_ECCU_SYN_t;

typedef union tag_IME_WRCH_TKEY_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t wrch_tkey_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t wrch_tkey_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_WRCH_TKEY_ECC_ADDR_t;

typedef union tag_IME_WRCH_CKEY_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t wrch_ckey_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t wrch_ckey_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_WRCH_CKEY_ECC_ADDR_t;

typedef union tag_IME_WRCH_TVAL_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t wrch_tval_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t wrch_tval_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_WRCH_TVAL_ECC_ADDR_t;

typedef union tag_IME_RDCH_TKEY_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t rdch_tkey_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t rdch_tkey_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_RDCH_TKEY_ECC_ADDR_t;

typedef union tag_IME_RDCH_CKEY_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t rdch_ckey_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t rdch_ckey_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_RDCH_CKEY_ECC_ADDR_t;

typedef union tag_IME_RDCH_TVAL_ECC_ADDR {
	uint32_t value;
	struct {
		const uint32_t rdch_tval_eccc_addr				: 16;	// [00 ... 15]
		const uint32_t rdch_tval_eccu_addr				: 16;	// [16 ... 31]
	};
} IME_RDCH_TVAL_ECC_ADDR_t;

typedef union tag_IME_ECC_IRQ_EN {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_eccc_irq_en					: 1;	// [00]
		uint32_t wrch_tkey_eccu_irq_en					: 1;	// [01]
		uint32_t wrch_ckey_eccc_irq_en					: 1;	// [02]
		uint32_t wrch_ckey_eccu_irq_en					: 1;	// [03]
		uint32_t wrch_tval_eccc_irq_en					: 1;	// [04]
		uint32_t wrch_tval_eccu_irq_en					: 1;	// [05]
		uint32_t rdch_tkey_eccc_irq_en					: 1;	// [06]
		uint32_t rdch_tkey_eccu_irq_en					: 1;	// [07]
		uint32_t rdch_ckey_eccc_irq_en					: 1;	// [08]
		uint32_t rdch_ckey_eccu_irq_en					: 1;	// [09]
		uint32_t rdch_tval_eccc_irq_en					: 1;	// [10]
		uint32_t rdch_tval_eccu_irq_en					: 1;	// [11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} IME_ECC_IRQ_EN_t;

typedef union tag_IME_ECC_IRQ_STAT {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_eccc_irq_stat				: 1;	// [00]
		uint32_t wrch_tkey_eccu_irq_stat				: 1;	// [01]
		uint32_t wrch_ckey_eccc_irq_stat				: 1;	// [02]
		uint32_t wrch_ckey_eccu_irq_stat				: 1;	// [03]
		uint32_t wrch_tval_eccc_irq_stat				: 1;	// [04]
		uint32_t wrch_tval_eccu_irq_stat				: 1;	// [05]
		uint32_t rdch_tkey_eccc_irq_stat				: 1;	// [06]
		uint32_t rdch_tkey_eccu_irq_stat				: 1;	// [07]
		uint32_t rdch_ckey_eccc_irq_stat				: 1;	// [08]
		uint32_t rdch_ckey_eccu_irq_stat				: 1;	// [09]
		uint32_t rdch_tval_eccc_irq_stat				: 1;	// [10]
		uint32_t rdch_tval_eccu_irq_stat				: 1;	// [11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} IME_ECC_IRQ_STAT_t;

typedef union tag_IME_WRCH_TKEY_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t wrch_tkey_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t wrch_tkey_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_WRCH_TKEY_ECC_ERR_CNT_t;

typedef union tag_IME_WRCH_CKEY_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t wrch_ckey_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t wrch_ckey_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_WRCH_CKEY_ECC_ERR_CNT_t;

typedef union tag_IME_WRCH_TVAL_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t wrch_tval_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t wrch_tval_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_WRCH_TVAL_ECC_ERR_CNT_t;

typedef union tag_IME_RDCH_TKEY_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t rdch_tkey_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t rdch_tkey_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_RDCH_TKEY_ECC_ERR_CNT_t;

typedef union tag_IME_RDCH_CKEY_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t rdch_ckey_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t rdch_ckey_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_RDCH_CKEY_ECC_ERR_CNT_t;

typedef union tag_IME_RDCH_TVAL_ECC_ERR_CNT {
	uint32_t value;
	struct {
		const uint32_t rdch_tval_eccc_err_cnt				: 16;	// [00 ... 15]
		const uint32_t rdch_tval_eccu_err_cnt				: 16;	// [16 ... 31]
	};
} IME_RDCH_TVAL_ECC_ERR_CNT_t;

typedef union tag_IME_WRCH_TKEY_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t wrch_tkey_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_WRCH_TKEY_ECC_ERR_THR_t;

typedef union tag_IME_WRCH_CKEY_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t wrch_ckey_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t wrch_ckey_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_WRCH_CKEY_ECC_ERR_THR_t;

typedef union tag_IME_WRCH_TVAL_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t wrch_tval_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t wrch_tval_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_WRCH_TVAL_ECC_ERR_THR_t;

typedef union tag_IME_RDCH_TKEY_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t rdch_tkey_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t rdch_tkey_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_RDCH_TKEY_ECC_ERR_THR_t;

typedef union tag_IME_RDCH_CKEY_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t rdch_ckey_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t rdch_ckey_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_RDCH_CKEY_ECC_ERR_THR_t;

typedef union tag_IME_RDCH_TVAL_ECC_ERR_THR {
	uint32_t value;
	struct {
		uint32_t rdch_tval_eccc_err_thr					: 16;	// [00 ... 15]
		uint32_t rdch_tval_eccu_err_thr					: 16;	// [16 ... 31]
	};
} IME_RDCH_TVAL_ECC_ERR_THR_t;

typedef union tag_IME_ECC_CLR {
	uint32_t value;
	struct {
		uint32_t wrch_tkey_eccc_clr					: 1;	// [00]
		uint32_t wrch_tkey_eccu_clr					: 1;	// [01]
		uint32_t wrch_ckey_eccc_clr					: 1;	// [02]
		uint32_t wrch_ckey_eccu_clr					: 1;	// [03]
		uint32_t wrch_tval_eccc_clr					: 1;	// [04]
		uint32_t wrch_tval_eccu_clr					: 1;	// [05]
		uint32_t rdch_tkey_eccc_clr					: 1;	// [06]
		uint32_t rdch_tkey_eccu_clr					: 1;	// [07]
		uint32_t rdch_ckey_eccc_clr					: 1;	// [08]
		uint32_t rdch_ckey_eccu_clr					: 1;	// [09]
		uint32_t rdch_tval_eccc_clr					: 1;	// [10]
		uint32_t rdch_tval_eccu_clr					: 1;	// [11]
		const uint32_t _RESERVED0					: 20;	// [12 ... 31]
	};
} IME_ECC_CLR_t;

typedef union tag_IME_FIFO_WARN_IRQ_EN {
	uint32_t value;
	struct {
		uint32_t wrch_enc_fifo_warn_en					: 1;	// [00]
		uint32_t wrch_data_fifo_warn_en					: 1;	// [01]
		uint32_t rdch_dec_fifo_warn_en					: 1;	// [02]
		uint32_t rdch_data_fifo_warn_en					: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} IME_FIFO_WARN_IRQ_EN_t;

typedef union tag_IME_FIFO_WARN_IRQ_STAT {
	uint32_t value;
	struct {
		uint32_t wrch_enc_fifo_warn_stat				: 1;	// [00]
		uint32_t wrch_data_fifo_warn_stat				: 1;	// [01]
		uint32_t rdch_dec_fifo_warn_stat				: 1;	// [02]
		uint32_t rdch_data_fifo_warn_stat				: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} IME_FIFO_WARN_IRQ_STAT_t;

typedef union tag_IME_CFG_LOCK_OVERRIDE {
	uint32_t value;
	struct {
		uint32_t cfg_lock_override					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_CFG_LOCK_OVERRIDE_t;

typedef union tag_IME_GLOBAL_KEY_SIZE {
	uint32_t value;
	struct {
		uint32_t global_key_size					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_GLOBAL_KEY_SIZE_t;

typedef union tag_IME_WRCH_UXTS_IRQ_EN {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t wrch_ctx_idx_err_en					: 1;	// [02]
		uint32_t wrch_reg_par_err_en					: 1;	// [03]
		uint32_t wrch_fsm_par_err_en					: 1;	// [04]
		uint32_t wrch_key_err_en					: 1;	// [05]
		uint32_t wrch_key_idx_err_en					: 1;	// [06]
		const uint32_t _RESERVED1					: 24;	// [07 ... 30]
		uint32_t wrch_uxts_irq_en					: 1;	// [31]
	};
} IME_WRCH_UXTS_IRQ_EN_t;

typedef union tag_IME_WRCH_UXTS_IRQ_STAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t wrch_ctx_idx_err					: 1;	// [02]
		uint32_t wrch_reg_par_err					: 1;	// [03]
		uint32_t wrch_fsm_par_err					: 1;	// [04]
		uint32_t wrch_key_err						: 1;	// [05]
		uint32_t wrch_key_idx_err					: 1;	// [06]
		const uint32_t _RESERVED1					: 25;	// [07 ... 31]
	};
} IME_WRCH_UXTS_IRQ_STAT_t;

typedef union tag_IME_WRCH_UXTS_BUILD_CONFIG_REG0 {
	uint32_t value;
	struct {
		const uint32_t wrch_dp_width					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		const uint32_t wrch_sk_en					: 1;	// [08]
		const uint32_t wrch_key128_en					: 1;	// [09]
		const uint32_t wrch_key256_en					: 1;	// [10]
		const uint32_t wrch_enc_en					: 1;	// [11]
		const uint32_t wrch_dec_en					: 1;	// [12]
		const uint32_t _RESERVED1					: 1;	// [13]
		const uint32_t wrch_aes_ecb_en					: 1;	// [14]
		const uint32_t _RESERVED2					: 3;	// [15 ... 17]
		const uint32_t wrch_random_blk_seq				: 1;	// [18]
		const uint32_t _RESERVED3					: 2;	// [19 ... 20]
		const uint32_t wrch_aes_en					: 1;	// [21]
		const uint32_t wrch_sm4_en					: 1;	// [22]
		const uint32_t _RESERVED4					: 9;	// [23 ... 31]
	};
} IME_WRCH_UXTS_BUILD_CONFIG_REG0_t;

typedef union tag_IME_WRCH_UXTS_BYPASS_CTL {
	uint32_t value;
	struct {
		const uint32_t wrch_ena						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_WRCH_UXTS_BYPASS_CTL_t;

typedef union tag_IME_WRCH_UXTS_MISC_CONFIG_REG {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 1;	// [00]
		const uint32_t wrch_enc_bypass					: 1;	// [01]
		const uint32_t wrch_pipe_bypass					: 1;	// [02]
		const uint32_t wrch_idle_bypass					: 1;	// [03]
		const uint32_t _RESERVED1					: 1;	// [04]
		uint32_t wrch_self_test_fail_act				: 1;	// [05]
		const uint32_t _RESERVED2					: 1;	// [06]
		const uint32_t wrch_inhibit_output				: 1;	// [07]
		uint32_t wrch_clr_ssp						: 1;	// [08]
		const uint32_t _RESERVED3					: 23;	// [09 ... 31]
	};
} IME_WRCH_UXTS_MISC_CONFIG_REG_t;

typedef union tag_IME_WRCH_UXTS_HW_INIT_CTRL {
	uint32_t value;
	struct {
		uint32_t wrch_hw_init_go					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_WRCH_UXTS_HW_INIT_CTRL_t;

typedef union tag_IME_WRCH_UXTS_STATUS {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		const uint32_t wrch_hw_init_done				: 1;	// [02]
		const uint32_t _RESERVED1					: 29;	// [03 ... 31]
	};
} IME_WRCH_UXTS_STATUS_t;

typedef union tag_IME_WRCH_SELF_TEST_CTL {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 4;	// [00 ... 03]
		uint32_t wrch_pipe_num						: 5;	// [04 ... 08]
		uint32_t wrch_chk_disable					: 1;	// [09]
		const uint32_t _RESERVED1					: 2;	// [10 ... 11]
		uint32_t wrch_enc_bypass_1					: 1;	// [12]
		const uint32_t _RESERVED2					: 19;	// [13 ... 31]
	};
} IME_WRCH_SELF_TEST_CTL_t;

typedef union tag_IME_WRCH_SELF_TEST_ATTRIB {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 4;	// [00 ... 03]
		uint32_t wrch_du_start						: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t wrch_du_end						: 1;	// [08]
		const uint32_t _RESERVED2					: 7;	// [09 ... 15]
		uint32_t wrch_ecb						: 1;	// [16]
		const uint32_t _RESERVED3					: 15;	// [17 ... 31]
	};
} IME_WRCH_SELF_TEST_ATTRIB_t;

typedef union tag_IME_WRCH_SELF_TEST_BSEQ {
	uint32_t value;
	struct {
		uint32_t wrch_val						: 20;	// [00 ... 19]
		const uint32_t _RESERVED0					: 12;	// [20 ... 31]
	};
} IME_WRCH_SELF_TEST_BSEQ_t;

typedef union tag_IME_WRCH_SELF_TEST_STAT {
	uint32_t value;
	struct {
		uint32_t wrch_st_done						: 1;	// [00]
		uint32_t wrch_st_fail						: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t wrch_fail_cause_1					: 1;	// [04]
		const uint32_t wrch_fail_cause_2				: 1;	// [05]
		const uint32_t wrch_fail_cause_3				: 1;	// [06]
		const uint32_t wrch_fail_cause_4				: 1;	// [07]
		const uint32_t wrch_fail_cause_5				: 1;	// [08]
		const uint32_t wrch_fail_cause_6				: 1;	// [09]
		const uint32_t wrch_fail_cause_7				: 1;	// [10]
		const uint32_t wrch_fail_cause_8				: 1;	// [11]
		const uint32_t wrch_fail_cause_9				: 1;	// [12]
		const uint32_t _RESERVED1					: 19;	// [13 ... 31]
	};
} IME_WRCH_SELF_TEST_STAT_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_PT_0 {
	uint32_t value;
	struct {
		uint32_t wrch_pt						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_PT_0_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_PT_1 {
	uint32_t value;
	struct {
		uint32_t wrch_pt_1						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_PT_1_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_PT_2 {
	uint32_t value;
	struct {
		uint32_t wrch_pt_2						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_PT_2_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_PT_3 {
	uint32_t value;
	struct {
		uint32_t wrch_pt_3						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_PT_3_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_CT_0 {
	uint32_t value;
	struct {
		uint32_t wrch_ct						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_CT_0_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_CT_1 {
	uint32_t value;
	struct {
		uint32_t wrch_ct_1						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_CT_1_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_CT_2 {
	uint32_t value;
	struct {
		uint32_t wrch_ct_2						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_CT_2_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_CT_3 {
	uint32_t value;
	struct {
		uint32_t wrch_ct_3						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_CT_3_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_RES_0 {
	uint32_t value;
	struct {
		const uint32_t wrch_cr_res					: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_RES_0_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_RES_1 {
	uint32_t value;
	struct {
		const uint32_t wrch_cr_res_1					: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_RES_1_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_RES_2 {
	uint32_t value;
	struct {
		const uint32_t wrch_cr_res_2					: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_RES_2_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_RES_3 {
	uint32_t value;
	struct {
		const uint32_t wrch_cr_res_3					: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_RES_3_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_TWK_0 {
	uint32_t value;
	struct {
		uint32_t wrch_dseq						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_TWK_0_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_TWK_1 {
	uint32_t value;
	struct {
		uint32_t wrch_dseq_1						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_TWK_1_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_TWK_2 {
	uint32_t value;
	struct {
		uint32_t wrch_dseq_2						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_TWK_2_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_TWK_3 {
	uint32_t value;
	struct {
		uint32_t wrch_dseq_3						: 32;	// [00 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_TWK_3_t;

typedef union tag_IME_WRCH_SELF_TEST_VECT_CTL {
	uint32_t value;
	struct {
		uint32_t wrch_go						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_WRCH_SELF_TEST_VECT_CTL_t;

typedef union tag_IME_WRCH_BIST_VECT_MODE {
	uint32_t value;
	struct {
		uint32_t wrch_funct						: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t wrch_key_size						: 1;	// [04]
		const uint32_t _RESERVED1					: 27;	// [05 ... 31]
	};
} IME_WRCH_BIST_VECT_MODE_t;

typedef union tag_IME_WRCH_UXTS_BIST_VECT_ERR_INJ {
	uint32_t value;
	struct {
		uint32_t wrch_byp_err_inj					: 1;	// [00]
		uint32_t wrch_ecb_err_inj					: 1;	// [01]
		uint32_t wrch_xts_err_inj					: 1;	// [02]
		uint32_t wrch_cts_err_inj					: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} IME_WRCH_UXTS_BIST_VECT_ERR_INJ_t;

typedef union tag_IME_WRCH_UXTS_BIST_VECT_CTL {
	uint32_t value;
	struct {
		uint32_t wrch_bist_go						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_WRCH_UXTS_BIST_VECT_CTL_t;

typedef union tag_IME_RDCH_UXTS_IRQ_EN {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t rdch_ctx_idx_err_en					: 1;	// [02]
		uint32_t rdch_reg_par_err_en					: 1;	// [03]
		uint32_t rdch_fsm_par_err_en					: 1;	// [04]
		uint32_t rdch_key_err_en					: 1;	// [05]
		uint32_t rdch_key_idx_err_en					: 1;	// [06]
		const uint32_t _RESERVED1					: 24;	// [07 ... 30]
		uint32_t rdch_uxts_irq_en					: 1;	// [31]
	};
} IME_RDCH_UXTS_IRQ_EN_t;

typedef union tag_IME_RDCH_UXTS_IRQ_STAT {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		uint32_t rdch_ctx_idx_err					: 1;	// [02]
		uint32_t rdch_reg_par_err					: 1;	// [03]
		uint32_t rdch_fsm_par_err					: 1;	// [04]
		uint32_t rdch_key_err						: 1;	// [05]
		uint32_t rdch_key_idx_err					: 1;	// [06]
		const uint32_t _RESERVED1					: 25;	// [07 ... 31]
	};
} IME_RDCH_UXTS_IRQ_STAT_t;

typedef union tag_IME_RDCH_UXTS_BUILD_CONFIG_REG0 {
	uint32_t value;
	struct {
		const uint32_t rdch_dp_width					: 6;	// [00 ... 05]
		const uint32_t _RESERVED0					: 2;	// [06 ... 07]
		const uint32_t rdch_sk_en					: 1;	// [08]
		const uint32_t rdch_key128_en					: 1;	// [09]
		const uint32_t rdch_key256_en					: 1;	// [10]
		const uint32_t rdch_enc_en					: 1;	// [11]
		const uint32_t rdch_dec_en					: 1;	// [12]
		const uint32_t _RESERVED1					: 1;	// [13]
		const uint32_t rdch_aes_ecb_en					: 1;	// [14]
		const uint32_t _RESERVED2					: 3;	// [15 ... 17]
		const uint32_t rdch_random_blk_seq				: 1;	// [18]
		const uint32_t _RESERVED3					: 2;	// [19 ... 20]
		const uint32_t rdch_aes_en					: 1;	// [21]
		const uint32_t rdch_sm4_en					: 1;	// [22]
		const uint32_t _RESERVED4					: 9;	// [23 ... 31]
	};
} IME_RDCH_UXTS_BUILD_CONFIG_REG0_t;

typedef union tag_IME_RDCH_UXTS_BYPASS_CTL {
	uint32_t value;
	struct {
		const uint32_t rdch_ena						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_RDCH_UXTS_BYPASS_CTL_t;

typedef union tag_IME_RDCH_UXTS_MISC_CONFIG_REG {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 1;	// [00]
		const uint32_t rdch_enc_bypass					: 1;	// [01]
		const uint32_t rdch_pipe_bypass					: 1;	// [02]
		const uint32_t rdch_idle_bypass					: 1;	// [03]
		const uint32_t _RESERVED1					: 1;	// [04]
		uint32_t rdch_self_test_fail_act				: 1;	// [05]
		const uint32_t _RESERVED2					: 1;	// [06]
		const uint32_t rdch_inhibit_output				: 1;	// [07]
		uint32_t rdch_clr_ssp						: 1;	// [08]
		const uint32_t _RESERVED3					: 23;	// [09 ... 31]
	};
} IME_RDCH_UXTS_MISC_CONFIG_REG_t;

typedef union tag_IME_RDCH_UXTS_HW_INIT_CTRL {
	uint32_t value;
	struct {
		uint32_t rdch_hw_init_go					: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_RDCH_UXTS_HW_INIT_CTRL_t;

typedef union tag_IME_RDCH_UXTS_STATUS {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 2;	// [00 ... 01]
		const uint32_t rdch_hw_init_done				: 1;	// [02]
		const uint32_t _RESERVED1					: 29;	// [03 ... 31]
	};
} IME_RDCH_UXTS_STATUS_t;

typedef union tag_IME_RDCH_SELF_TEST_CTL {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 4;	// [00 ... 03]
		uint32_t rdch_pipe_num						: 5;	// [04 ... 08]
		uint32_t rdch_chk_disable					: 1;	// [09]
		const uint32_t _RESERVED1					: 2;	// [10 ... 11]
		uint32_t rdch_enc_bypass_1					: 1;	// [12]
		const uint32_t _RESERVED2					: 19;	// [13 ... 31]
	};
} IME_RDCH_SELF_TEST_CTL_t;

typedef union tag_IME_RDCH_SELF_TEST_ATTRIB {
	uint32_t value;
	struct {
		const uint32_t _RESERVED0					: 4;	// [00 ... 03]
		uint32_t rdch_du_start						: 1;	// [04]
		const uint32_t _RESERVED1					: 3;	// [05 ... 07]
		uint32_t rdch_du_end						: 1;	// [08]
		const uint32_t _RESERVED2					: 7;	// [09 ... 15]
		uint32_t rdch_ecb						: 1;	// [16]
		const uint32_t _RESERVED3					: 15;	// [17 ... 31]
	};
} IME_RDCH_SELF_TEST_ATTRIB_t;

typedef union tag_IME_RDCH_SELF_TEST_BSEQ {
	uint32_t value;
	struct {
		uint32_t rdch_val						: 20;	// [00 ... 19]
		const uint32_t _RESERVED0					: 12;	// [20 ... 31]
	};
} IME_RDCH_SELF_TEST_BSEQ_t;

typedef union tag_IME_RDCH_SELF_TEST_STAT {
	uint32_t value;
	struct {
		uint32_t rdch_st_done						: 1;	// [00]
		uint32_t rdch_st_fail						: 1;	// [01]
		const uint32_t _RESERVED0					: 2;	// [02 ... 03]
		uint32_t rdch_fail_cause_1					: 1;	// [04]
		const uint32_t rdch_fail_cause_2				: 1;	// [05]
		const uint32_t rdch_fail_cause_3				: 1;	// [06]
		const uint32_t rdch_fail_cause_4				: 1;	// [07]
		const uint32_t rdch_fail_cause_5				: 1;	// [08]
		const uint32_t rdch_fail_cause_6				: 1;	// [09]
		const uint32_t rdch_fail_cause_7				: 1;	// [10]
		const uint32_t rdch_fail_cause_8				: 1;	// [11]
		const uint32_t rdch_fail_cause_9				: 1;	// [12]
		const uint32_t _RESERVED1					: 19;	// [13 ... 31]
	};
} IME_RDCH_SELF_TEST_STAT_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_PT_0 {
	uint32_t value;
	struct {
		uint32_t rdch_pt						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_PT_0_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_PT_1 {
	uint32_t value;
	struct {
		uint32_t rdch_pt_1						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_PT_1_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_PT_2 {
	uint32_t value;
	struct {
		uint32_t rdch_pt_2						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_PT_2_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_PT_3 {
	uint32_t value;
	struct {
		uint32_t rdch_pt_3						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_PT_3_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_CT_0 {
	uint32_t value;
	struct {
		uint32_t rdch_ct						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_CT_0_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_CT_1 {
	uint32_t value;
	struct {
		uint32_t rdch_ct_1						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_CT_1_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_CT_2 {
	uint32_t value;
	struct {
		uint32_t rdch_ct_2						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_CT_2_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_CT_3 {
	uint32_t value;
	struct {
		uint32_t rdch_ct_3						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_CT_3_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_RES_0 {
	uint32_t value;
	struct {
		const uint32_t rdch_cr_res					: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_RES_0_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_RES_1 {
	uint32_t value;
	struct {
		const uint32_t rdch_cr_res_1					: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_RES_1_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_RES_2 {
	uint32_t value;
	struct {
		const uint32_t rdch_cr_res_2					: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_RES_2_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_RES_3 {
	uint32_t value;
	struct {
		const uint32_t rdch_cr_res_3					: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_RES_3_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_TWK_0 {
	uint32_t value;
	struct {
		uint32_t rdch_dseq						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_TWK_0_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_TWK_1 {
	uint32_t value;
	struct {
		uint32_t rdch_dseq_1						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_TWK_1_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_TWK_2 {
	uint32_t value;
	struct {
		uint32_t rdch_dseq_2						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_TWK_2_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_TWK_3 {
	uint32_t value;
	struct {
		uint32_t rdch_dseq_3						: 32;	// [00 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_TWK_3_t;

typedef union tag_IME_RDCH_SELF_TEST_VECT_CTL {
	uint32_t value;
	struct {
		uint32_t rdch_go						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_RDCH_SELF_TEST_VECT_CTL_t;

typedef union tag_IME_RDCH_BIST_VECT_MODE {
	uint32_t value;
	struct {
		uint32_t rdch_funct						: 3;	// [00 ... 02]
		const uint32_t _RESERVED0					: 1;	// [03]
		uint32_t rdch_key_size						: 1;	// [04]
		const uint32_t _RESERVED1					: 27;	// [05 ... 31]
	};
} IME_RDCH_BIST_VECT_MODE_t;

typedef union tag_IME_RDCH_UXTS_BIST_VECT_ERR_INJ {
	uint32_t value;
	struct {
		uint32_t rdch_byp_err_inj					: 1;	// [00]
		uint32_t rdch_ecb_err_inj					: 1;	// [01]
		uint32_t rdch_xts_err_inj					: 1;	// [02]
		uint32_t rdch_cts_err_inj					: 1;	// [03]
		const uint32_t _RESERVED0					: 28;	// [04 ... 31]
	};
} IME_RDCH_UXTS_BIST_VECT_ERR_INJ_t;

typedef union tag_IME_RDCH_UXTS_BIST_VECT_CTL {
	uint32_t value;
	struct {
		uint32_t rdch_bist_go						: 1;	// [00]
		const uint32_t _RESERVED0					: 31;	// [01 ... 31]
	};
} IME_RDCH_UXTS_BIST_VECT_CTL_t;

#endif /* __DWC_DDRCTL_CINIT_REGB_REG_H__ */

