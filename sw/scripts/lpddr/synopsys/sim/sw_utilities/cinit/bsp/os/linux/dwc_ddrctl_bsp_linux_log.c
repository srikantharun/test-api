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


#include "dwc_cinit_bsp.h"
#include "dwc_cinit_log.h"

#define ENTRY_SIZE    256

/**
 * @brief Structure of static variable to store the log files
 * 
 */
typedef struct ddr_log_files_e {
    FILE *log;
    FILE *sequences;
    FILE *defconfig;
    FILE *trace;
    FILE *cinit_cfg_log;
    FILE *regmap_dump;
    time_t start_time_sec;
} ddr_log_files_t;


/**
 * @brief Static variable to store the log times
 * 
 */
static ddr_log_files_t s_log_files = {NULL, NULL, NULL, NULL, NULL, NULL, 0};


#ifndef CONFIG_FILENAME
    #define CONFIG_FILENAME    "./testbench_defconfig"
#endif

#ifndef LOG_FILENAME
    #define LOG_FILENAME       "./dwc_ddrctl_cinit.log"
#endif
#ifndef SEQ_FILENAME
    #define SEQ_FILENAME       "./dwc_ddrctl_cinit.seq"
#endif

#ifndef TRACE_FILENAME
    #define TRACE_FILENAME     "./dwc_ddrctl_sinit_trace.log"
#endif

#ifndef CINIT_CFG_LOG_FILENAME
    #define CINIT_CFG_LOG_FILENAME     "./dwc_ddrctl_cinit_config.log"
#endif

#ifndef CINIT_REGMAP_PRINT_FILENAME
    #define CINIT_REGMAP_PRINT_FILENAME     "./ddrctl_cinit_regmap.log"
#endif


/**
 * @brief Function to get the Pointer FILE pointer to the log type
 * 
 * @param log_type  log type
 * @return FILE**   pointer to FILE pointer
 */
static FILE **_log_type_file(ddr_bsp_log_type_t log_type)
{
    FILE **log_file;

    switch (log_type)
    {
        case SNPS_SEQUENCES_LOG:
            log_file = &(s_log_files.sequences);
            break;
        case SNPS_DEFCONFIG_LOG:
            log_file = &(s_log_files.defconfig);
            break;
        case SNPS_CONFIG_LOG:
            log_file = &(s_log_files.cinit_cfg_log);
            break;
        case SNPS_REGMAP_LOG:
            log_file = &(s_log_files.regmap_dump);
            break;
        case SNPS_CALL_TRACE_LOG:
#ifndef CINIT_TRACE_ON_LOG
            log_file = &(s_log_files.trace);
            break;
#else
            /* no break */
#endif
        case SNPS_MAIN_LOG:
        default:
            log_file = &(s_log_files.log);
            break;
    }

    return log_file;
}


/**
 * @brief Function to get the filename to the log type
 * 
 * @param log_type  log type
 * @return char*    log file name
 */
static char * _log_type_filename(ddr_bsp_log_type_t log_type)
{
    char * log_name;

    switch (log_type)
    {
        case SNPS_SEQUENCES_LOG:
            log_name = SEQ_FILENAME;
            break;
        case SNPS_DEFCONFIG_LOG:
            log_name = CONFIG_FILENAME;
            break;
        case SNPS_CONFIG_LOG:
            log_name = CINIT_CFG_LOG_FILENAME;
            break;
        case SNPS_REGMAP_LOG:
            log_name = CINIT_REGMAP_PRINT_FILENAME;
            break;
        case SNPS_CALL_TRACE_LOG:
#ifndef CINIT_TRACE_ON_LOG
            log_name = TRACE_FILENAME;
            break;
#else
            /* no break */
#endif
        case SNPS_MAIN_LOG:
        default:
            log_name = LOG_FILENAME;
            break;
    }

    return log_name;
}


/**
 * @brief Function to create the log file in the file system
 * 
 * @param log_type  log type
 */
void ddr_bsp_log_file_create(ddr_bsp_log_type_t log_type)
{
    FILE ** ptr_log_file;
    char  * log_name;

    ptr_log_file = _log_type_file(log_type);
    log_name     = _log_type_filename(log_type);

    if ((NULL == ptr_log_file) || (NULL != *ptr_log_file)) {
        return;
    }

    *ptr_log_file = fopen(log_name, "w");

    if (NULL == *ptr_log_file) {
        SNPS_ERROR("Unable to create log file (%s)", log_name);
        exit(-1);
    }
}


/**
 * @brief Function to close the log file in the file system
 * 
 * @param log_type  log type
 */
void ddr_bsp_log_file_close(ddr_bsp_log_type_t log_type)
{
    FILE ** ptr_log_file;

    ptr_log_file = _log_type_file(log_type);

    if ((NULL == ptr_log_file) || (NULL == *ptr_log_file)) {
        return;
    }

    fclose(*ptr_log_file);
    *ptr_log_file = NULL;
}


/**
 * @brief Function to write a log entry using a table format
 * 
 * @param log_type  log type
 * @param level     log level
 * @param file      log entry source file
 * @param function  log entry function
 * @param line      log entry line
 * @param format    log text format
 * @param ...       text format arguments
 */
void ddr_bsp_log_entry(ddr_bsp_log_type_t log_type, ddr_log_level_t level,
                       char *file, const char *function, const uint32_t line,
                       const char *format, ...)
{
    FILE ** ptr_log_file;
    va_list args;
    time_t  now_sec;
    char    entry[ENTRY_SIZE];

    now_sec = time(NULL);

    if (0 == s_log_files.start_time_sec) {
        s_log_files.start_time_sec = time(NULL);
    }

    snprintf(entry, ENTRY_SIZE, "%-5s|%5lu|%50s|%50s|%5u|%s\n",
            ddrctl_get_log_level_str(level), now_sec - s_log_files.start_time_sec,
            basename(file), function, line, format);

    va_start(args, format);
    vprintf(entry, args);
    va_end(args);

    ptr_log_file = _log_type_file(log_type);
    if ((NULL != ptr_log_file) && (NULL != *ptr_log_file)) {
        va_start(args, format);
        vfprintf(*ptr_log_file, entry, args);
        va_end(args);
        fflush(*ptr_log_file);
    }
}


/**
 * @brief Function to write a log line
 * 
 * @param log_type  log type
 * @param format    log text format
 * @param ...       text format arguments
 */
void ddr_bsp_log_write(ddr_bsp_log_type_t log_type, const char *format, ...)
{
    FILE ** ptr_log_file;
    va_list args;
    char    entry[ENTRY_SIZE];

    ptr_log_file = _log_type_file(log_type);
    if ((NULL != ptr_log_file) && (NULL != *ptr_log_file)) {
        snprintf(entry, ENTRY_SIZE, "%s\n", format);
        va_start(args, format);
        vfprintf(*ptr_log_file, entry, args);
        va_end(args);
        fflush(*ptr_log_file);
    }
}


/**
 * @brief Function to write a register write log line
 * 
 * @param log_type  log type
 * @param address   register address
 * @param data      register value to write
 */
void ddr_bsp_log_reg_write(ddr_bsp_log_type_t log_type, const uint32_t address,
                           const uint32_t data)
{
    FILE **ptr_log_file;

    ptr_log_file = _log_type_file(log_type);

    if ((NULL != ptr_log_file) && (NULL != *ptr_log_file)) {
        fprintf(*ptr_log_file, "dwc_ddrctl_wr(0x%.8x, 0x%.8x);\n", address, data);
    }
}

