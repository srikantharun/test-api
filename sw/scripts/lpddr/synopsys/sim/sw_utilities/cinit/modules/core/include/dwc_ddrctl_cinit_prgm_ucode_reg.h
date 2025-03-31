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


#ifndef __DWC_DDRCTL_CINIT_PRGM_UCODE_H__
#define __DWC_DDRCTL_CINIT_PRGM_UCODE_H__

/*************************************************************************
 * T Y P E D E F S   f o r   M I C R O C O D E
 *************************************************************************/

/************************************************************************/
/*! \enum ddr5_pas_du_blk_sel_e
 * Encoding of PAS DU blk select, select to access global block or rank block in config buffer
 */
typedef enum tag_ddr5_pas_du_blk_sel {
    DWC_DDRCTL_GLOBAL_BLK = 0,
    DWC_DDRCTL_RANK_BLK = 1
} ddr5_pas_du_blk_sel_e;

/*! \enum ddr5_pas_du_blk_type_e
 * Encoding of PAS DU block type
 */
typedef enum tag_ddr5_pas_du_blk_type {
    DWC_DDRCTL_MASTER_BLK = 0,
    DWC_DDRCTL_SLAVE_BLK = 1
} ddr5_pas_du_blk_type_e;

/*! \enum ddr5_pas_du_glk_cfg_addr_e
 * Encoding of PAS DU CFGBUF address for global bloks
 */
typedef enum tag_ddr5_pas_du_gblk_cfg_addr {
	DWC_DDRCTL_GBLK_ZQCAL_START = 0,
	DWC_DDRCTL_GBLK_CTRL_UPD = 2,
	DWC_DDRCTL_GBLK_ZQCAL_LATCH = 8,
	DWC_DDRCTL_GBLK_SWFFC = 14
} ddr5_pas_du_gblk_cfg_addr_e;

/*! \enum ddr5_pas_du_rankblk_cfg_addr_e
 * Encoding of PAS DU CFGBUF address for rank bloks
 */
typedef enum tag_ddr5_pas_du_rankblk_cfg_addr {
    // RANK 0
    DWC_DDRCTL_RANK0_BLK0_ZQCAL_START = 0,
    DWC_DDRCTL_RANK0_BLK1_DQSOSC_START = 2,
    DWC_DDRCTL_RANK0_BLK2_RFU = 4,
    DWC_DDRCTL_RANK0_BLK3_RFU = 6,
    DWC_DDRCTL_RANK0_BLK4_ZQCAL_LATCH = 8,
    DWC_DDRCTL_RANK0_BLK5_TCR_MRR = 10,
    DWC_DDRCTL_RANK0_BLK6_MANUAL_ECS = 12,
    DWC_DDRCTL_RANK0_BLK7_RFU = 14,
    // RANK 1
    DWC_DDRCTL_RANK1_BLK0_ZQCAL_START = 16,
    DWC_DDRCTL_RANK1_BLK1_DQSOSC_START = 18,
    DWC_DDRCTL_RANK1_BLK2_RFU = 20,
    DWC_DDRCTL_RANK1_BLK3_RFU = 22,
    DWC_DDRCTL_RANK1_BLK4_ZQCAL_LATCH = 24,
    DWC_DDRCTL_RANK1_BLK5_TCR_MRR = 26,
    DWC_DDRCTL_RANK1_BLK6_MANUAL_ECS = 28,
    DWC_DDRCTL_RANK1_BLK7_RFU = 30,
    // RANK 2
    DWC_DDRCTL_RANK2_BLK0_ZQCAL_START = 32,
    DWC_DDRCTL_RANK2_BLK1_DQSOSC_START = 34,
    DWC_DDRCTL_RANK2_BLK2_RFU = 36,
    DWC_DDRCTL_RANK2_BLK3_RFU = 38,
    DWC_DDRCTL_RANK2_BLK4_ZQCAL_LATCH = 40,
    DWC_DDRCTL_RANK2_BLK5_TCR_MRR = 42,
    DWC_DDRCTL_RANK2_BLK6_MANUAL_ECS = 44,
    DWC_DDRCTL_RANK2_BLK7_RFU = 46,
    // RANK 3
    DWC_DDRCTL_RANK3_BLK0_ZQCAL_START = 48,
    DWC_DDRCTL_RANK3_BLK1_DQSOSC_START = 50,
    DWC_DDRCTL_RANK3_BLK2_RFU = 52,
    DWC_DDRCTL_RANK3_BLK3_RFU = 54,
    DWC_DDRCTL_RANK3_BLK4_ZQCAL_LATCH = 56,
    DWC_DDRCTL_RANK3_BLK5_TCR_MRR = 58,
    DWC_DDRCTL_RANK3_BLK6_MANUAL_ECS = 60,
    DWC_DDRCTL_RANK3_BLK7_RFU = 62
} ddr5_pas_du_blk_cfg_addr_e;

/*! \enum mc_cmd_code_e
 * Encoding uCode CMD options used in LC/DU module.
 * The encoding must match the code in microcode.c file and uCode definition spec.
 */
typedef enum tag_mc_cmd_code_e {
    MPC_CMD = 0x0c,
    MRR_CMD = 0x00,
    MRW_CMD = 0x10,
    SRE_CMD = 0x20,
    SRX_CMD = 0x21,
    PDE_CMD = 0x22,
    PDX_CMD = 0x23,
    NOP_CMD = 0x28,
    DES_CMD = 0x29,
    IWAIT_TIME_CMD = 0x18,
    IWAIT_SIG_CMD = 0x19,
    MOV_CMD = 0x34,
    IMM_BIT_CMD = 0x36,
    DISDQ_CMD = 0x40,
    PAUSEREF_CMD = 0x41,
    REF_FLUSH_CMD = 0x4f,
    SRX_DONE_CMD = 0x42,
    PDX_MPSMX_DONE_CMD = 0x43,
    CTRLUPD_CMD = 0x44,
    DFILP_CMD = 0x45,
    PRANK_PREAB_CMD = 0x48,
    PRANK_REFAB_CMD = 0x49,
    FORCE_CS_CMD = 0x4a,
    LOCK_CTRL_CMD = 0x4b,
    DFI_CLK_CMD = 0x4c,
    NTODT_CTRL_CMD = 0x4d,
    JPC_CMD = 0x05
} mc_cmd_code_e;

/*! \enum CSn_SEL_e
 * Encoding CSn_SEL options for RANK selection.
 * The encoding must match the code in microcode.c file and uCode definition spec.
 */
typedef enum tag_CSn_SEL_e {
    RANK0_SEL = 0,
    RANK1_SEL,
    RANK2_SEL,
    RANK3_SEL,
    RANK0_1_SEL,
    RANK2_3_SEL,
    RANK_ALL_SEL,
    RANK_R15_SEL
} CSn_SEL_e;

/*! \enum DIMM_TYPE_SEL_e
 * Encoding DIMM_TYPE options for DIMM type selection for uCode.
 * The encoding must match the code in the programming guide.
 */
typedef enum tag_DIMM_TYPE_SEL_e {
    DDR5_NODIMM = 0,
    DDR5_RDIMM,
    DDR5_LRDIMM
} DIMM_TYPE_SEL_e;

/**
 * @brief The following union types define the uCode bit-field structure.
 */
typedef union tag_MPC_UCODE {
    const uint16_t value;
    struct {
        uint16_t op                        : 8;    // [00 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t csn_sel                    : 3;    // [09 ... 11]
        uint16_t cmd_code                    : 4;    // [12 ... 15]
    };
} __attribute__((packed)) MPC_UCODE_t;

typedef union tag_MRR_UCODE {
    const uint16_t value;
    struct {
        uint16_t mra                        : 8;    // [00 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t prank_sel                    : 1;    // [09]
        uint16_t phy_snoop_en                    : 1;    // [10]
        uint16_t prank_num                    : 2;    // [11 ... 12]
        uint16_t cmd_code                    : 3;    // [13 ... 15]
    };
} __attribute__((packed)) MRR_UCODE_t;

typedef union tag_MRW1_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_time                    : 5;    // [00 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) MRW1_UCODE_t;

typedef union tag_MRW2_UCODE {
    const uint16_t value;
    struct {
        uint16_t mra                        : 8;    // [00 ... 07]
        uint16_t op                        : 8;    // [08 ... 15]
    };
} __attribute__((packed)) MRW2_UCODE_t;

typedef union tag_SRE_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 3;    // [00 ... 02]
        uint16_t wait_type                    : 1;    // [03]
        uint16_t freq_change                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) SRE_UCODE_t;

typedef union tag_SRX_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 4;    // [00 ... 03]
        uint16_t wait_type                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) SRX_UCODE_t;

typedef union tag_PDE_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_cycle                    : 4;    // [00 ... 03]
        uint16_t wait_type                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PDE_UCODE_t;

typedef union tag_PDX_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 4;    // [00 ... 03]
        uint16_t wait_type                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PDX_UCODE_t;

typedef union tag_NOP_UCODE {
    const uint16_t value;
    struct {
        uint16_t nop_len                    : 4;    // [00 ... 03]
        uint16_t _RESERVED                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) NOP_UCODE_t;

typedef union tag_DES_UCODE {
    const uint16_t value;
    struct {
        uint16_t unit_count                    : 6;    // [00 ... 05]
        uint16_t unit_sel                    : 2;    // [06 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) DES_UCODE_t;

typedef union tag_IWAIT_REG_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 4;    // [00 ... 03]
        uint16_t _RESERVED                    : 5;    // [04 ... 08]
        uint16_t wait_type                    : 1;    // [09]
        uint16_t cmd_code                    : 6;    // [10 ... 15]
    };
} __attribute__((packed)) IWAIT_REG_UCODE_t;

typedef union tag_IWAIT_TIME_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_time                    : 7;    // [00 ... 06]
        uint16_t wait_unit                    : 2;    // [07 ... 08]
        uint16_t wait_type                    : 1;    // [09]
        uint16_t cmd_code                    : 6;    // [10 ... 15]
    };
} __attribute__((packed)) IWAIT_TIME_UCODE_t;

typedef union tag_IWAIT_SIG_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_cycle                    : 4;    // [00 ... 03]
        uint16_t sig_sel                    : 5;    // [04 ... 08]
        uint16_t sig_value                    : 1;    // [09]
        uint16_t cmd_code                    : 6;    // [10 ... 15]
    };
} __attribute__((packed)) IWAIT_SIG_UCODE_t;

typedef union tag_MOV_UCODE {
    const uint16_t value;
    struct {
        uint16_t reg_num                    : 4;    // [00 ... 03]
        uint16_t _RESERVED                    : 3;    // [04 ... 06]
        uint16_t mov_type                    : 1;    // [07]
        uint16_t mov_dir                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) MOV_UCODE_t;

typedef union tag_IMM_BIT_UCODE {
    const uint16_t value;
    struct {
        uint16_t bit_val                    : 1;    // [00]
        uint16_t bit_loc                    : 3;    // [01 ... 03]
        uint16_t reg_sel                    : 2;    // [04 ... 05]
        uint16_t _RESERVED                    : 2;    // [06 ... 07]
        uint16_t imm_type                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) IMM_BIT_UCODE_t;

typedef union tag_DISDQ_UCODE {
    const uint16_t value;
    struct {
        uint16_t disdqreset                    : 1;    // [00]
        uint16_t disdqset                    : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) DISDQ_UCODE_t;

typedef union tag_REF_FLUSH_UCODE {
    const uint16_t value;
    struct {
        uint16_t ref_flush_req_set           : 1;    // [00]
        uint16_t _RESERVED                   : 4;    // [01 ... 04]
        uint16_t csn_sel                     : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) REF_FLUSH_UCODE_t;

typedef union tag_PAUSEREF_UCODE {
    const uint16_t value;
    struct {
        uint16_t pauserefreset                    : 1;    // [00]
        uint16_t pauserefset                    : 1;    // [01]
        uint16_t pausereftype                    : 1;    // [02]
        uint16_t _RESERVED                    : 2;    // [03 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PAUSEREF_UCODE_t;

typedef union tag_SRX_DONE_UCODE {
    const uint16_t value;
    struct {
        uint16_t srx_done_txs                    : 1;    // [00]
        uint16_t srx_done_txsdll                : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) SRX_DONE_UCODE_t;

typedef union tag_PDX_MPSMX_DONE_UCODE {
    const uint16_t value;
    struct {
        uint16_t pdx_done                    : 1;    // [00]
        uint16_t mpsmx_done                    : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PDX_MPSMX_DONE_UCODE_t;

typedef union tag_CTRLUPD_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_time                    : 5;    // [00 ... 04]
        uint16_t wait_unit                    : 1;    // [05]
        uint16_t dfi_ctrlupd_retry_en                : 1;    // [06]
        uint16_t dfi_ctrlupd_req_set                : 1;    // [07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) CTRLUPD_UCODE_t;

typedef union tag_DFILP_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_time                    : 3;    // [00 ... 02]
        uint16_t wakeup_type                : 1;    // [03]
        uint16_t dfi_lp_ctrl_req_clr        : 1;    // [04]
        uint16_t dfi_lp_ctrl_req_set        : 1;    // [05]
        uint16_t dfi_lp_data_req_clr        : 1;    // [06]
        uint16_t dfi_lp_data_req_set        : 1;    // [07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) DFILP_UCODE_t;

typedef union tag_PRANK_PREAB_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 3;    // [00 ... 02]
        uint16_t wait_type                    : 1;    // [03]
        uint16_t _RESERVED                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PRANK_PREAB_UCODE_t;

typedef union tag_PRANK_REFAB_UCODE {
    const uint16_t value;
    struct {
        uint16_t wait_reg                    : 3;    // [00 ... 02]
        uint16_t wait_type                    : 1;    // [03]
        uint16_t _RESERVED                    : 1;    // [04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) PRANK_REFAB_UCODE_t;

typedef union tag_FORCE_CS_UCODE {
    const uint16_t value;
    struct {
        uint16_t force_cse                    : 1;    // [00]
        uint16_t force_csx                    : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) FORCE_CS_UCODE_t;

typedef union tag_LOCK_CTRL_UCODE {
	const uint16_t value;
	struct {
		uint16_t lock_ci_bus					: 1;	// [00]
		uint16_t unlock_ci_bus					: 1;	// [01]
		uint16_t set_urgent_flag				: 1;	// [02]
		uint16_t reset_urgent_flag				: 1;	// [03]
		uint16_t set_ucode_seq_ongoing_flag		: 1;	// [04]
		uint16_t reset_ucode_seq_ongoing_flag   : 1;	// [05]
		uint16_t _RESERVED					: 3;	// [06 ... 08]
		uint16_t cmd_code					: 7;	// [09 ... 15]
	};
} __attribute__((packed)) LOCK_CTRL_UCODE_t;

typedef union tag_DFICLK_UCODE {
    const uint16_t value;
    struct {
        uint16_t dfi_ck_disable_set                : 1;    // [00]
        uint16_t dfi_ck_disable_clear                : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) DFICLK_UCODE_t;

typedef union tag_NTODT_CTRL_UCODE {
    const uint16_t value;
    struct {
        uint16_t ntodt_en_ctrl                    : 1;    // [00]
        uint16_t ntodt_dis_ctrl                    : 1;    // [01]
        uint16_t _RESERVED                    : 3;    // [02 ... 04]
        uint16_t csn_sel                    : 3;    // [05 ... 07]
        uint16_t last_cmd                    : 1;    // [08]
        uint16_t cmd_code                    : 7;    // [09 ... 15]
    };
} __attribute__((packed)) NTODT_CTRL_UCODE_t;

typedef union tag_JPC_UCODE {
    const uint16_t value;
    struct {
        uint16_t jmp_step                    : 6;    // [00 ... 05]
        uint16_t jmp_dir                    : 1;    // [06]
        uint16_t sig_sel                    : 5;    // [07 ... 11]
        uint16_t sig_value                    : 1;    // [12]
        uint16_t cmd_code                    : 3;    // [13 ... 15]
    };
} __attribute__((packed)) JPC_UCODE_t;

#endif /* __DWC_DDRCTL_CINIT_PRGM_UCODE_H__ */
