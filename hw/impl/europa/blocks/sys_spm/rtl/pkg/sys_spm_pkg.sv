// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

/// SYS-SPM Package
///
package sys_spm_pkg;

    import spm_pkg::*;

    parameter int SYS_SPM_MEM_SIZE_KB = 8192;
    parameter int ECC_PROTECTION_EN = 1;

    /*
    * SYS_SPM_MEM_SIZE_KB = SYS_SPM_MEM_MACRO_DEPTH_K
    *                       * SYS_SPM_NB_BANKS
    *                       * SYS_SPM_NB_SUB_BANKS
    *                       * SYS_SPM_NB_MINI_BANKS
    *                       * SYS_SPM_NB_SRAMS_PER_MINI_BANK
    */

    // To get a total of 8MiB using 8k deep SRAMs
    //  - Each SRAM has 64kb entries (64b * 8k deep)
    //  - We want 128 instances
    parameter int unsigned SYS_SPM_NB_BANKS      = 4;
    parameter int unsigned SYS_SPM_NB_SUB_BANKS  = 4;
    parameter int unsigned SYS_SPM_NB_MINI_BANKS = 4;
    parameter int unsigned SYS_SPM_NB_SRAMS_PER_MINI_BANK = 2;
    parameter int unsigned SYS_SPM_NB_REQ_PIPELINE = 3;
    parameter int unsigned SYS_SPM_NB_RSP_PIPELINE = 3;

    // AXI Targ - LT
    parameter int unsigned SYS_SPM_TARG_LT_AXI_ID_W = 4;
    typedef logic [SYS_SPM_TARG_LT_AXI_ID_W-1:0] sys_spm_targ_lt_axi_id_t;

    parameter int unsigned SYS_SPM_SYNC_STAGES = 3;

    typedef struct packed {
       spm_ecc_err_index_t    ecc_err_index;
       spm_ecc_err_syndrome_t ecc_err_syndrome;
       spm_ecc_err_type_t     ecc_err_type;
    } sys_spm_error_status_data_t;

endpackage
