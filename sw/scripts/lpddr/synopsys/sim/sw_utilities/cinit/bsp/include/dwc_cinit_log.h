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


#ifndef CINIT_BSP_INCLUDE_CINIT_LOG_H_
#define CINIT_BSP_INCLUDE_CINIT_LOG_H_

#include "dwc_cinit_os_bsp.h"
#include "dwc_cinit_types.h"

#define CINIT_DEBUG

#ifdef CINIT_DEBUG

#define SNPS_DEBUG(...)    \
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_DEBUG, __FILE__, __func__, __LINE__, __VA_ARGS__)
#define SNPS_INFO(...)    \
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_INFO, __FILE__, __func__, __LINE__, __VA_ARGS__)
#define SNPS_LOG(...)    \
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_INFO, __FILE__, __func__, __LINE__, __VA_ARGS__)
#define SNPS_WARN(...) \
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_WARN, __FILE__, __func__, __LINE__, __VA_ARGS__)
#define SNPS_ERROR(...) \
    ddr_bsp_log_entry(SNPS_MAIN_LOG, DWC_LOG_ERROR, __FILE__, __func__, __LINE__, __VA_ARGS__)

#define SNPS_REGMAP_INFO(...)    \
    ddr_bsp_log_write(SNPS_REGMAP_LOG, __VA_ARGS__)

#define SNPS_INPUT(...) \
    ddr_bsp_log_write(SNPS_DEFCONFIG_LOG, __VA_ARGS__)

#define SNPS_DEFCFG_WR(...) \
    ddr_bsp_log_write(SNPS_DEFCONFIG_LOG, __VA_ARGS__)

#define SNPS_LOG_REG_WRITE_SEQ(address, data) \
    ddr_bsp_log_reg_write(SNPS_SEQUENCES_LOG, address, data)

#define SNPS_LOG_CFG_STRUCT(...) \
    ddr_bsp_log_write(SNPS_CONFIG_LOG, __VA_ARGS__)

#define SNPS_CALL_TRACE(format, ...) \
    ddr_bsp_log_write(SNPS_CALL_TRACE_LOG, "TRACE| "format, __VA_ARGS__)
#else

#define SNPS_DEBUG(...)
#define SNPS_LOG(...)
#define SNPS_INFO(...)
#define SNPS_WARN(...)
#define SNPS_ERROR(...)

#define SNPS_INPUT(...)

#define SNPS_DEFCFG_WR(...)

#define SNPS_LOG_REG_WRITE_SEQ(address, data)

#define SNPS_LOG_CFG_STRUCT(...)

#define SNPS_CALL_TRACE(format, ...)

#endif /* CINIT_DEBUG */


#ifdef CINIT_TRACE_DEBUG
#define SNPS_TRACE(...) \
    ddr_bsp_log_entry(DWC_LOG_INFO, __FILE__, __func__, __LINE__, __VA_ARGS__)

#else
    #define SNPS_TRACE(format)
#endif /* CINIT_TRACE_DEBUG */

void ddr_bsp_log_file_create(ddr_bsp_log_type_t log_type);

void ddr_bsp_log_file_close(ddr_bsp_log_type_t log_type);

void ddr_bsp_log_write(ddr_bsp_log_type_t log_type, const char *format, ...);

void ddr_bsp_log_entry(ddr_bsp_log_type_t log_type, ddr_log_level_t level,
                       char *file, const char *function, const uint32_t line,
                       const char *format, ...);

void ddr_bsp_log_reg_write(ddr_bsp_log_type_t log_type, const uint32_t address,
                           const uint32_t data);


#endif /* CINIT_BSP_INCLUDE_CINIT_LOG_H_ */
