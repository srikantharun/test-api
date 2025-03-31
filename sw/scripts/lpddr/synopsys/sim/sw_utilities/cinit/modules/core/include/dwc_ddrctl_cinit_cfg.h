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


#ifndef __DWC_DDRCTL_CINIT_CFG_H__
#define __DWC_DDRCTL_CINIT_CFG_H__

/**
 * @note this header will be converted to systemverilog for usage in
 * simulations.
 */

#define IME_MAX_KEY_DWORD_SIZE  (256 / 32)  // 256 Bit key in 32 bits words
#define IME_MAX_KEY_SLOTS        2          // Primary and secondary keys support
#define IME_MAX_REGIONS          16
// DDRCTL_CINIT_MAX_DEV_NUM is set to maximum value of parameter DWC_DDRCTL_DEV_CFG_NUM defined in dwc_ddrctl_pve_parameters_pkg.sv
// For DDR, it is set to maximum value of DEV_CFG_NUM. when ddr5 heterogenourous rank support is enabled, DEV_CFG_NUM has number 2.
// For LPDDR, it is set to MEMC_NUM_RANKS.
#ifdef DDRCTL_DDR
  #define DDRCTL_CINIT_MAX_DEV_NUM 2
#endif
#ifdef DDRCTL_LPDDR
  #define DDRCTL_CINIT_MAX_DEV_NUM 4
#endif

/**
 * @brief Type definition of structure describing attached memory type and topology
 */
typedef struct tag_ddrSpdData_t {
    ddr5_jedec_spec_t ddr5_jedec_spec;
#ifdef DDRCTL_LPDDR
    dwc_lpddr4_data_rate_e lpddr4_data_rate; //!< Max data rate of attached LPDDR4 DRAM
    dwc_lpddr5_data_rate_e lpddr5_data_rate; //!< Max data rate of attached LPDDR5 DRAM
    dwc_lpddr5_wckck_ratio_e lpddr5_wckck_ratio[UMCTL2_FREQUENCY_NUM]; //!< Select 1:2 or 4:1 WCK:CK ratio @deprecated
    dwc_lpddr5_bk_bg_org_e lpddr5_bk_bg_org[UMCTL2_FREQUENCY_NUM]; //!< Bank/BankGroup Organization.
#endif /* DDRCTL_LPDDR */
#ifdef DDRCTL_DDR
    dwc_ddr4_speed_grade_e ddr4_sg;
    dwc_ddr5_speed_bin_t ddr5_speed_bin[DDRCTL_CINIT_MAX_DEV_NUM];
#endif /* DDRCTL_DDR */
    dwc_sdram_protocol sdram_protocol; //!< Basic memory type
    dwc_sdram_module_type module_type; //!< SDRAM Module type
    uint32_t tck_ps[UMCTL2_FREQUENCY_NUM];          //!< Operating clock period ps
    dwc_freq_ratio_t frequency_ratio[UMCTL2_FREQUENCY_NUM]; //!< Frequency ratio
    uint8_t  num_ranks; //!<Number of ranks
    uint32_t sdram_width_bits[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM width (bits) [x4, x8, x16, x32]
    uint32_t sdram_capacity_mbits[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM capacity (megabits)
    uint32_t sdram_capacity_mbits_lp45_mp[DDRCTL_CINIT_MAX_DEV_NUM]; //!<SDRAM capacity (megabits)
    uint8_t addr_mirror; //!<Address mirroring support (0-not supported, 1-supported)
    uint8_t shared_ac;
    uint8_t cid_width[DDRCTL_CINIT_MAX_DEV_NUM]; //Number of 3DS CIDs in use 1-2H 2-4H per phyisical rank
    //The following structure members are calculated for you in the subsys_SetSpd() function. No need to set them
    uint8_t address_mode[DDRCTL_CINIT_MAX_DEV_NUM];
    uint32_t dram_raw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Row address bits
    uint32_t dram_caw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Column address bits
    uint32_t dram_baw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Bank address bits
    uint32_t dram_bgw[DDRCTL_CINIT_MAX_DEV_NUM]; //!<Bank group address bits

    uint8_t num_ranks_per_dimm; //!<
    uint8_t num_dimm; //!< Number of DIMM
    uint8_rnd_t use_ddr4_tcwl_1st_set; //!< When calculating cwl_x use the lower set of values for tcwl
    uint8_rnd_t tAL; //!< Additive Latency can be 0, CL-1, CL-2
    uint8_t tAL_RDBI; //!< Read DBI Additive Latency
    uint32_rnd_t trx_dqs2dq; //!< ddr5 tRx_DQS2DQ, unit is ps
    uint8_t use_lpddr4x; //!< The SDRAM is a variant of LPDDR4
    uint8_t use_lpddr5x; //!< The SDRAM is a variant of LPDDR5
    uint8_t lpddr4_scl; //!<LPDDR4 Scaling Level
#ifdef DDRCTL_DDR
  	dwc_ddr5_dimm_ch_arch_e ddr5_dimm_ch_arch;//!< data width per channel for RDIMM/LRDIMM
#endif
    uint8_t total_address_bits; //!< total number of address bits
} ddrSpdData_t;

/**
 * @brief Type definition of structure describing everything to
 * configure the memory controller.
 */
typedef struct tag_umctl2_t {
#ifdef DDRCTL_LPDDR
    lpddr4_mode_registers_t lpddr4_mr[UMCTL2_FREQUENCY_NUM]; //!< variables that program LPDDR4 mode registers
    lpddr5_mode_registers_t lpddr5_mr[UMCTL2_FREQUENCY_NUM]; //!< variables that program LPDDR5 mode registers
#endif /* DDRCTL_LPDDR */
#ifdef DDRCTL_DDR
    ddr4_mode_registers_t ddr4_mr[UMCTL2_FREQUENCY_NUM]; //!< variables that program DDR4 mode registers
    ddr5_mode_registers_t ddr5_mr[UMCTL2_FREQUENCY_NUM]; //!< variables that program DDR5 mode registers
#endif /* DDRCTL_DDR */
    dwc_ddrctl_cinit_cfg_static_t static_cfg; //!< variables that program static register fields
    dwc_ddrctl_cinit_cfg_qdyn_t qdyn_cfg; //!< variables that are affect quasi-dynamic fields
    dwc_ddrctl_cinit_cfg_dyn_t dyn_cfg; //!< variables that are affect dynamic fields
    dwc_sdram_bus_width_e sdram_bus_width;
    mctl_pre_cfg pre_cfg; //!< A with some pre-calculations used in programming some register fields.
} mctl_t;

#ifdef DDRCTL_DDR
/**
 * @brief Type definition of structure describing DDR5 PAS configuration
 */
typedef struct tag_ddr5_pasdu_en_t {
    uint32_t base_timer_interval_us[DWC_DDRCTL_NUM_CHANNEL]; //!< System level required base timer interval in useconds
    uint32_t ctlupd_en[DWC_DDRCTL_NUM_CHANNEL]; //!< System level requirement to enable controller update
    uint32_t all_rank_zqcal_en[DWC_DDRCTL_NUM_CHANNEL]; //!< System level all rank ZQCAL requirement
    uint32_t per_rank_zqcal_en[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< System level per RANK ZQCAL enable requirement
    uint32_t tcr_dqsosc_en[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< System level TCR/DQS OSC enable requirement
    uint32_t per_rank_ecs_en[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< System level per RANK ZQCAL enable requirement
} ddr5_pasdu_en_t;

/**
 * @brief Structure containing offset value to ajust the read to read
 * or write to write delay for ddr5 interamble
 */
typedef struct tag_ddr5_interamble_tccd_offset_t {
    uint32_rnd_t t_ccd_w_offset[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
    uint32_rnd_t t_ccd_r_offset[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
} ddr5_interamble_tccd_offset_t;
#endif /* DDRCTL_DDR */

/**
 * @brief Type definition of structure describing DDR5 PAS activies threshold
 */
typedef struct tag_ddr5_pasdu_thres_t {
    uint32_t all_rank_zqcal_thres[DWC_DDRCTL_NUM_CHANNEL]; //!< all rank ZQCAL threshold
    uint32_t all_rank_zqlat_thres[DWC_DDRCTL_NUM_CHANNEL]; //!< all rank ZQLAT threshold
    uint32_t ctlupd_thres[DWC_DDRCTL_NUM_CHANNEL]; //!< Controller update threshold
    uint32_t per_rank_zqcal_thres[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< Per RANK ZQCAL threshold
    uint32_t per_rank_zqlat_thres[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< Per RANK ZQLAT threshold
    uint32_t dqsosc_thres[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< DQSOSC threshold
    uint32_t tcr_mrr_thres[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< MRR46+47+4 threshold
    uint32_t ecs_thres[DWC_DDRCTL_NUM_CHANNEL][MEMC_NUM_RANKS]; //!< Per RANK MANUAL ECS threshold
} ddr5_pasdu_thres_t;

/**
 * @brief Type definition of structure describing misc parameters to
 * configure the PHYINIT software.
 */
typedef struct tag_phy_timing_params_t {
    uint32_t pipe_dfi_wr;
    uint32_t pipe_dfi_rd;
    uint32_t pipe_dfi_misc; //!< specifics the term MISC in calculation of tPHY_WRCSLAT and tPHY_RDCSLAT.
    uint32_t dfi_tlp_resp; //!< Specifies the maximum number of DfiClk cycles after the assertion of the dfi_lp_ctrl_req or dfi_lp_ata_req signal to the assertion of the dfi_lp_ack signal
    uint32_t dfi_tphy_wrdata;
    uint32_t dfi_t_ctrlup_max;
    uint32_t dfi_t_ctrlup_min;
    uint32_t dfi_t_ctrl_delay; //!< Specifies the number of DRAM clock cycles after an assertion or de-assertion of the DFI control signals that the control signals at the PHY-DRAM interface reflect the assertion or de-assertion.
    uint32_t dfi_tlp_data_wakeup;
#ifdef DDRCTL_DDR
    uint32_t dfi_t_2n_mode_delay; //!< The delay from dfi_2n_mode assertion to the time of the PHY being ready to receive commands.
#endif /* DDRCTL_DDR */
    uint32_t dfi_t_ctrlupd_burst_interval_x8[UMCTL2_FREQUENCY_NUM];
} phy_timing_params_t;


/**
 * @brief Emun for the IME Encryption key size
 * 
 */
typedef enum {
    IME_KEY_SZ_128=0,
    IME_KEY_SZ_256=1
  } ddrctl_key_size_t;


typedef struct tag_ddrctl_ime_region_e {
    uint64_t    address_start;
    uint64_t    address_end;
    uint16_t    c_key_id[IME_MAX_KEY_SLOTS];
    uint16_t    t_key_id[IME_MAX_KEY_SLOTS];
    uint8_t     key_swap_enable;
} ddrctl_ime_region_t;


/**
 * @brief Type definition for the 
 * 
 */
typedef struct tag_ddrctl_ime_cfg_e {
    uint8_t             enable;
    ddrctl_key_size_t   key_size;
    ddrctl_ime_region_t region[IME_MAX_REGIONS];
} ddrctl_ime_cfg_t;


/**
 * @brief This is the main structure for initializing the DDR Subsystem handler. This acts as a container for all the required structures.
 */
struct SubsysHdlr_priv {
    uint8_rnd_t enable_non_jedec_tck; //!< Allow a out of range TCK value. The value spdData_m.tck_ps must be manually specified in this mode.
    uint8_rnd_t use_snps_vip_timing; //!< Adjust timings for Synopsys VIP
    uint8_rnd_t use_jedec_init; //!< Use JEDEC timings for initialization.
    uint8_rnd_t num_pstates; //!< Number of frequencies to setup
    uint8_rnd_t num_amap; //!< Number of address maps
    uint8_rnd_t num_dch; //!< Number of data channels to setup
    ddrSpdData_t spdData_m; //!< The SDRAM memory descriptor.
    uint8_t lut_entry[DWC_DDRCTL_MAX_LUT_ENTRIES]; // lut entry buffer, used in cs map lut configuration
#ifdef DDRCTL_DDR
    ddr4_control_words_t ddr4_cw; //!< variables that program DDR4 RCD Control Words
    ddr5_control_words_t ddr5_cw; //!< variables that program DDR5 RCD Control Words
    ddr5_db_control_words_t  ddr5_db_cw;                              //!< variables that program DDR5 RCD Databuffer Control Words
    ddr5_pasdu_en_t ddr5_pasdu_en; //!< variables that enable the DDR5 PAS_DU activties
    ddr5_pasdu_thres_t ddr5_pasdu_thres; //!< variables that configure the DDR5 PAS_DU activties threshold
    ddr5_interamble_tccd_offset_t ddr5_interamble_tccd_offset; //!< variables that adjust the DDR5 write to write or read to read delay
    uint8_t ddr5_lock_step_connect_en; //!< variable to enable lock step connection for DFI interface between Controller and PHY
#endif /* DDRCTL_DDR */
    // Bug7444 Single element arrays are treated differently between C and simulator
    ddrTimingParameters_t timingParams_m[UMCTL2_FREQUENCY_NUM + 1][DDRCTL_CINIT_MAX_DEV_NUM]; //!< timing parameters
    ddr5_scaling_control_t ddr5_scaling_control; //!< DDR5 parameter scaling
    mctl_t memCtrlr_m; //!< Structures to configure umctl register field values.
    uint64_t ddrctl_base_addr[DWC_DDRCTL_NUM_CHANNEL]; //!< Memory controller base address
    // PHY options
    phy_timing_params_t phy_timing_params; //!< PHY specific timing parameters.
    uint32_rnd_t num_anibs; //!< Number of PHY address nibbles
    uint32_rnd_t num_dbytes; //!< Number of PHY dbytes
    uint8_rnd_t dfi1_exists; //!< PHY exist dfi1
    uint8_rnd_t lpddr4_pop_support;
    // HdtCtrl
    // 0x05 = Detailed debug messages (e.g. Eye delays)
    // 0x0A = Coarse debug messages (e.g. rank information)
    // 0xC8 = Stage completion
    // 0xC9 = Assertion messages
    // 0xFF = Firmware completion messages only
    uint8_rnd_t HdtCtrl; //!< Used in setting up PUB message block (Hardware Debug Trace Control)
    ddrPhyType_e ddrPhyType_m; //!< PHY type
    uint32_t phyBaseAddr_m; //!< PHY utility block (PUB) base address
    uint32_rnd_t mr7_by_phy;
    uint32_t mr0_pdx_time;
    uint32_rnd_t phy_training; //!< 0 - full training, 1 - skip training, 2 - dev_inti
    // Some control on behaviour of CINIT library
    uint8_rnd_t PhyMstrCtrlMode; //!< When this bit is 1, a PHY Master transaction is initiated only by a dfi_ctrlmsg transaction.
    uint8_rnd_t PhyMstrTrainInterval; //!< Time between the end of one training and the start of the next.
    uint8_rnd_t disable_fsp_op; //!Use to control DisableFspOP in LPDDR54 PHYINIT
    uint8_rnd_t enable_deep_sleep_mode; //!Use to control Lp3DramState in LPDDR5X4 PHYINIT
    uint8_rnd_t EnWck2DqoTracking; //!< Use to control MRR snooping in LPDDR54 PHYINIT.
#ifdef DDRCTL_EXT_SBECC_AND_CRC
    uint8_t en_dfi_ras_model; //!< 1 when dfi_ras_model is used.  
    uint8_t wr_path_delay; //!< Value of the delay on write data path of the DFI RAS model.
    uint8_t rd_path_delay; //!< Value of the delay on read data path of the DFI RAS model.
    uint8_t del_tphy_wrlat; //!< Value of deleted number from tphy_wrlat to compensente the DFI RAS model delay. 
    uint8_t del_tphy_wrdata; //!< Value of deleted number from tphy_wrdata to compensente the DFI RAS model delay.
    uint8_t tphy_wrlat_org[UMCTL2_FREQUENCY_NUM]; //!< original value of tphy_wrlat.
    uint8_t tphy_wrdata_org[UMCTL2_FREQUENCY_NUM]; //!< original value of tphy_wrdata.
    uint8_t dfi_ras_model_cmd_delay; //!< Value to program the command delay of DFI RAS model. 
#endif
    void *phy_config; //!< A pointer to PHYINT meta structure that holds other PHYINT structures
    uint8_rnd_t wr_crc_retry_window_internal_delay_extra; //!< Randomize the tinternal_delay_extra calculated for wr_crc_retry_window
    uint8_rnd_t capar_retry_window_internal_delay_extra; //!< Randomize the tinternal_delay_extra calculated for capar_retry_window
    ddrctl_ime_cfg_t ime_cfg[DWC_DDRCTL_NUM_CHANNEL];   //!< IME configuration paramters
}; // fwd SubsysHdlr_t
// NB the above comment is used by c_to_sv.pl, do not remove it.
#endif /* __DWC_DDRCTL_CINIT_CFG_H__ */
