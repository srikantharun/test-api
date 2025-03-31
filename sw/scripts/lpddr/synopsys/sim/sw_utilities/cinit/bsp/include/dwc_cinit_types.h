#ifndef CINIT_BSP_INCLUDE_DWC_CINIT_TYPES_H_
#define CINIT_BSP_INCLUDE_DWC_CINIT_TYPES_H_

/**
 * Macro to remove unused parameters warnings explicitly
 */
#define CINIT_UNUSED(var) (void)(var)

#define DWC_DDRCTL_MAX_APB_POLLING 1500

typedef enum ddr_bsp_log_type_e {
    SNPS_MAIN_LOG,
    SNPS_SEQUENCES_LOG,
    SNPS_DEFCONFIG_LOG,
    SNPS_CALL_TRACE_LOG,
    SNPS_CONFIG_LOG,
    SNPS_REGMAP_LOG
} ddr_bsp_log_type_t;


typedef enum ddr_log_level_e {
    DWC_LOG_DEBUG  = 0,
    DWC_LOG_INFO   = 1,
    DWC_LOG_WARN   = 2,
    DWC_LOG_ERROR  = 3,
    DWC_LOG_ASSERT = 4,
} ddr_log_level_t;


static inline const char * ddrctl_get_log_level_str(ddr_log_level_t level)
{
    switch (level) {
        case DWC_LOG_DEBUG:
            return "DEBUG";
        case DWC_LOG_WARN:
            return "WARN";
        case DWC_LOG_ERROR:
            return "ERROR";
        case DWC_LOG_ASSERT:
            return "ASSRT";
        case DWC_LOG_INFO:
        default:
            return "INFO";
    }
}

/**
 * @brief Type for the functions error return codes
 */
typedef enum ddrctl_error_e {
    DDRCTL_SUCCESS                        =   0,  /**< Success */
    DDRCTL_ERROR                          =   1,  /**< Error */
    DDRCTL_MEMORY_ERROR                   =   2,  /**< Memory error */
    DDRCTL_TIMEOUT                        =   3,  /**< Timeout */
    DDRCTL_NOT_SUPPORTED                  =   4,  /**< Not supported */
    DDRCTL_PARAM_ERROR                    =   5,  /**< Parameter error */
    DDRCTL_PHYINIT_ERROR                  =   6,  /**< Phyinit error */
    DDRCTL_PHY_TRAIN_FAILED               =   7,  /**< Phy Train failed */
    DDRCTL_PHY_MAILBOX_ERROR              =   8,  /**< Phy Mailbox error */
    DDRCTL_ENTRY_NOT_FOUND                =   9,  /**< Table entry not found */
    DDRCTL_INVALID_NULL_PTR               =  10,  /**< Null pointer */
    DDRCTL_ASSERT                         = 255,  /**< Assert */
} ddrctl_error_t;


/**
 * @brief Type for the enable/disable status
 */
typedef enum ddrctl_status_e {
    DDRCTL_ENABLE  = 1,  /**< Enable  */
    DDRCTL_DISABLE = 0,  /**< Disable */
} ddrctl_status_t;


static inline const char * ddrctl_status_to_str(ddrctl_status_t value)
{
    switch (value) {
        case DDRCTL_ENABLE:
            return "Enable";
        default:
            return "Disable";
    }
}

/**
 * @brief Type for represent True and False
 */
typedef enum ddrctl_bool_e {
    DDRCTL_TRUE  = 1,  /**< True  */
    DDRCTL_FALSE = 0,  /**< False */
} ddrctl_bool_t;


static inline const char * ddrctl_bool_to_str(ddrctl_bool_t value)
{
    switch (value) {
        case DDRCTL_TRUE:
            return "True";
        default:
            return "False";
    }
}


typedef enum ddrctl_io_e {
    DDRCTL_IO_IME_CFG_LOCK = 0,     /**< Controls ime_i_cfg_lock/ime_i_cfg_lock_dch1 IME input signal */
    DDRCTL_IO_IME_CFG_KEY_LOCK = 1, /**< Controls ime_i_cfg_key_lock/ime_i_cfg_key_lock_dch1 IME input signal */
} ddrctl_io_t;


static inline const char * ddrctl_io_to_str(ddrctl_io_t io_pin)
{
    switch (io_pin) {
        case DDRCTL_IO_IME_CFG_LOCK:
            return "IME_CFG_LOCK";
        case DDRCTL_IO_IME_CFG_KEY_LOCK:
            return "IME_CFG_KEY_LOCK";
        default:
            return "Unknown";
    }
}

#endif /* CINIT_BSP_INCLUDE_DWC_CINIT_TYPES_H_ */
