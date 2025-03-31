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


#ifndef __DWC_DDRCTL_CINIT_H__
#define __DWC_DDRCTL_CINIT_H__

#include "dwc_cinit_io.h"
#include "dwc_cinit_log.h"
#include "dwc_cinit_bsp.h"
#include "dwc_ddrctl_cinit_helpers.h"

// Declare the version of this software.
#define FW_VERSION_MAJOR  (0x34323061)  // ASCII code for 420a
#define FW_VERSION_MINOR  (0x20203030)  // ASCII code for   00

typedef struct SubsysHdlr_priv SubsysHdlr_t;

/* uint32_rnd_t will be declared "rand unsigned int" in Systemverilog world. */
typedef uint32_t uint32_rnd_t;
typedef uint16_t uint16_rnd_t;
typedef uint8_t uint8_rnd_t;
typedef bool bool_rnd_t;

#include "DWC_ddrctl_cc_constants.h"
#ifdef DDRCTL_SECURE
#include "DWC_ime_cc_constants.h"
#endif
#include "dwc_ddrphy_VDEFINES.h"

/* When DDRCTL_SINGLE_INST_DUALCH is set the dual channel DDR controller
 * consists of two identical DWC_ddrctl instances.
 * So DWC_DDRCTL_NUM_CHANNEL is manually set to 2 to account for the second
 * instance.
*/
#ifdef DDRCTL_SINGLE_INST_DUALCH
  #define DWC_DDRCTL_NUM_CHANNEL 2
#else
  #ifdef LPDDR_2MC1PHY
  #define DWC_DDRCTL_NUM_CHANNEL 2
  #else
  #define DWC_DDRCTL_NUM_CHANNEL UMCTL2_NUM_DATA_CHANNEL
  #endif
#endif

#if defined(USE_KCONFIG_DEFINITIONS)
#include ".autoconf.h"
#endif /* USE_KCONFIG_DEFINITIONS */

#include "dwc_ddrctl_cinit_types.h"
// the following files are automated from corebuilder and generateRegisterInfo.tcl
#include "dwc_cinit_macros.h"
#include "dwc_ddrctl_cinit_cfg_static.h"
#include "dwc_ddrctl_cinit_cfg_qdyn.h"
#include "dwc_ddrctl_cinit_cfg_dyn.h"
#include "dwc_ddrctl_cinit_cfg.h"

#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_REGB.h"


uint32_t ddr_cinit_get_major_version();

uint32_t ddr_cinit_get_minor_version();

// Simulation (Testbench) external function declarations
#ifndef STD_ALONE
extern void dwc_ddrphy_cinit_cpu_dpi_main(SubsysHdlr_t *hdlr, dwc_ddrctl_cinit_seq_e cinit_seq);
#endif /* STD_ALONE */


extern SubsysHdlr_t *hdlr;

typedef struct ddr_ctrl_regs_s{
    dwc_ddrctl_cinit_REGB_t    REGB[DWC_DDRCTL_CINIT_MAX_FREQ];
} ddr_ctrl_regs_t;
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_cinit_prgm.h"
#include "dwc_ddrctl_cinit_REGB.h"
#include "dwc_cinit_workaround_macros.h"

extern ddr_ctrl_regs_t g_ctrl_regs;

// Function prototypes
extern void dwc_ddrctl_cinit_begin(SubsysHdlr_t *phdlr);
extern void dwc_ddrctl_cinit_main(SubsysHdlr_t *hdlr);
extern void dwc_ddrctl_cinit_end(void);

extern void dwc_cinit_setup(SubsysHdlr_t *hdlr);
extern void dwc_cinit_set_operational_clk_period(SubsysHdlr_t *hdlr);
extern void dwc_cinit_reg_defaults(SubsysHdlr_t *hdlr);
extern void dwc_ddrctl_cinit_set_static_cfg_initial_values(void);
extern void dwc_ddrctl_cinit_set_qdyn_cfg_initial_values(void);
extern void dwc_ddrctl_cinit_set_dyn_cfg_initial_values(void);
extern void dwc_cinit_phyinit_setuserinput(SubsysHdlr_t *hdlr);
extern uint8_t dwc_cinit_get_rdimm_operating_speed(SubsysHdlr_t *hdlr, uint32_t p);
extern void dwc_cinit_setup_mmap(void);

extern void cinit_pre_cfg(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern void cinit_cal_pre_cfg_timing_1st_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern void cinit_cal_pre_cfg_timing_2nd_set(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern uint32_t cinit_cal_cwlx(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
extern uint32_t cinit_cal_cl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);

extern void cinit_cal_rd2wr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
extern void cinit_cal_wr2rd(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
extern uint32_t cinit_ps_to_tck(uint32_t param_ps, uint32_t tck_ps);
extern uint8_t get_cal_cycles(uint8_t cal_mode);
extern void cinit_cal_lpddr4x_multiphy_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern void cinit_cal_lpddr54_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern void cinit_cal_ddr43_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
extern void cinit_cal_ddr54_dfi_timings(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
#ifdef DDRCTL_EXT_SBECC_AND_CRC
extern void cinit_cal_delay_for_ras_model(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n);
#endif

extern void cinit_encode_wr_recovery(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n, uint32_t lpddr_mixed_pkg_en);
extern void cinit_encode_rl_wl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n, uint32_t lpddr_mixed_pkg_en);
extern void cinit_encode_lpddr5_rl_wl(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch, uint32_t n, uint32_t lpddr_mixed_pkg_en);
extern void cinit_encode_cas_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n);
extern void cinit_encode_cas_write_latency(SubsysHdlr_t *hdlr, uint32_t p);
extern void cinit_encode_write_cmd_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t n);
extern void cinit_encode_tccd_l_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern uint32_t cinit_get_nrtp(uint8_t row);
extern uint32_t cinit_get_rl_row(uint8_t rl, uint8_t x16, uint8_t dbi);
extern uint32_t cinit_get_wl_row(uint8_t wl, uint8_t x16, uint8_t wls);
extern uint32_t dwc_cinit_get_min_t_xsr(SubsysHdlr_t *hdlr, uint32_t tck_ps, uint32_t dvfsc_type);
extern uint32_t dwc_cinit_get_lpddr4_tpbr2pbr(uint32_t capacity_mbits);
extern uint32_t dwc_cinit_get_lpddr4_trfcab(uint32_t capacity_mbits);
extern uint32_t dwc_cinit_get_lpddr4_trfcpb(uint32_t capacity_mbits);
extern uint32_t dwc_cinit_get_lpddr4_trfmpb(uint32_t capacity_mbits);
extern uint32_t dwc_cinit_get_lpddr5_trfcab(uint32_t capacity_mbits, uint8_t dvfsc_type);
extern uint32_t dwc_cinit_get_lpddr5_trfcpb(uint32_t capacity_mbits, uint8_t dvfsc_type);
extern uint32_t dwc_cinit_get_lpddr5_trfmpb(uint32_t capacity_mbits);
extern uint32_t dwc_cinit_get_lpddr5_tpbr2pbr(uint32_t capacity_mbits, uint8_t dvfsc_type);

extern void dwc_cinit_map_tck_ps_to_data_rate(SubsysHdlr_t *hdlr);
extern void map_tck_ps_to_l_lpddr4_data_rate(SubsysHdlr_t *hdlr);
extern void map_tck_ps_to_l_lpddr5_data_rate(SubsysHdlr_t *hdlr);
extern uint32_t cinit_cal_ddr5_rd_min_gap(SubsysHdlr_t *hdlr);
extern uint32_t cinit_cal_ddr5_wr_min_gap(SubsysHdlr_t *hdlr);
extern uint32_t cinit_get_ddr5_twpre(SubsysHdlr_t *hdlr, uint32_t p);
extern uint32_t cinit_get_ddr5_t_rd_dqs_offset(SubsysHdlr_t *hdlr, uint32_t p);
extern void cinit_encode_ddr5_trtp_latency(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern uint32_t cinit_get_lpddr5_tras_max(SubsysHdlr_t *hdlr, uint32_t trefi, uint32_t refesh_rate, uint32_t p, uint32_t n);
extern void cinit_set_rcd(SubsysHdlr_t *hdlr);

extern void cinit_cal_mrr2rdwr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern void cinit_cal_diff_rank_wr_gap(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern void cinit_cal_diff_rank_rd_gap(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern void cinit_cal_wr2rd_dr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);
extern uint32_t cal_lpddr5_odtlon(SubsysHdlr_t *hdlr, uint32_t p, uint32_t dch);
extern void cinit_cal_rd2wr_dr(SubsysHdlr_t *hdlr, uint32_t p, uint32_t ch, uint32_t n);

extern uint32_t dwc_ddrctl_cinit_cal_ddr54_ext(SubsysHdlr_t *hdlr, uint32_t p);

#ifdef DDRCTL_DDR
extern void cinit_pasctl(SubsysHdlr_t *hdlr, uint32_t dch);
extern uint8_t decode_ddr4_rcd_latency_adder_nladd_to_all_dram_cmd(SubsysHdlr_t *hdlr);
extern uint32_t dwc_cinit_get_ddr4_trfc(uint32_t capacity_mbits, uint32_t fgr_mode);
extern uint32_t dwc_cinit_get_ddr5_trfc(uint32_t capacity_mbits, uint32_t fgr_mode);
extern uint32_t dwc_cinit_get_ddr4_trfc_dlr(uint32_t capacity_mbits, uint32_t fgr_mode);
extern uint32_t dwc_cinit_get_ddr5_trfc_dlr(uint32_t capacity_mbits, uint32_t fgr_mode);
extern uint32_t dwc_ddrctl_cinit_get_ddr_trfc_min_tck(uint32_t sdram_protocol, uint32_t capacity_mbits, uint32_t fgr_mode, uint32_t tck_ps);

extern uint32_t dwc_ddrctl_cinit_get_ddr_trfc_tck(uint32_t sdram_protocol, uint32_t capacity_mbits, uint32_t fgr_mode, uint32_t tck_ps);
uint32_t dwc_ddrctl_cinit_get_ddr4_mr5_parity_latency_mode(uint32_t p);

#endif /* DDRCTL_DDR */

extern uint32_t dwc_ddrctl_cinit_read_du_cmdbuf(uint32_t addr, uint32_t block_type, uint32_t ch);
extern void dwc_ddrctl_cinit_write_du_cmdbuf(uint32_t addr, uint32_t data, uint32_t block_type, uint32_t ch);
extern uint32_t dwc_ddrctl_cinit_read_lp_cmdbuf(uint32_t addr, uint32_t ch);
extern void dwc_ddrctl_cinit_write_lp_cmdbuf(uint32_t addr, uint32_t data, uint32_t ch);
extern void dwc_ddrctl_cinit_write_du_cfgbuf(uint32_t addr, uint32_t blk_sel, uint32_t blk_ba, uint32_t blk_size, uint32_t blk_thres,uint32_t blk_type, uint32_t ch);
extern void dwc_ddrctl_cinit_write_capar_cmdbuf(uint32_t addr, uint32_t data, uint32_t ch);

extern void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUTCTRL(uint32_t cfg_addr, uint32_t data0, uint32_t data1);
extern void dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry(SubsysHdlr_t *hdlr);

void dwc_ddrctl_cinit_set_REGB_default(void);

void dwc_ddrctl_cinit_convert_config(void);
extern void dwc_ddrctl_cinit_prgm_REGB_DDRC_PWRCTL(uint32_t ch);
extern void dwc_ddrctl_cinit_ddr_address_mapper(uint32_t am);
#ifdef DDRCTL_DDR
extern void dwc_ddrctl_cinit_ddr_setuserinput(void);
#else
extern void dwc_ddrctl_cinit_lpddr_setuserinput(void);
void dwc_ddrctl_cinit_write_hwffc_mrwbuf(uint32_t pstate, uint32_t addr, uint32_t mrwbuf_wdata);
#endif

#ifdef PHYINIT

// dwc_ddrctl_set_pub_channel_active method purely for simulation purposes.
// The Snps test bench requires it and may not be needed in other environments
extern void dwc_ddrctl_set_pub_channel_active(int p_ch);

#endif /* PHYINIT */

extern void ddr5_udimm_force_ECC_DBYTE(void);

/**
 * @brief Macro utility to create a bit mask with bits sets.
 *
 * For example, SNPS_BITMASK(6:4) yields 0x00000070
 *
 * @param msb Most significant bit of set mask
 * @param lsb Least significant bit of set mask
 */
#define DWC_DDRCTL_BITMASK(msb,lsb) \
    (((uint32_t) -1 >> (31 - (msb))) & ~((1U << (lsb)) - 1))

/**
 * @brief Macro utility to shift a bit field left
 * @param val Value (less than 32-bit value) to shift
 * @param size Size of value (number of bits, 1..32)
 * @param lsb Least significant bit (shift left, 0..31)
 */
#define DWC_DDRCTL_SETREGBITFIELDSHIFT(val,size,lsb) \
    (((val) & DWC_DDRCTL_BITMASK(((size)-1),0)) << (lsb))

#endif /* __DWC_DDRCTL_CINIT_H__ */
