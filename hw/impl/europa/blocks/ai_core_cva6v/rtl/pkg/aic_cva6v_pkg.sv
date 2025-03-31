// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>


/// AI Core CVA6V europa implementation package
///
package aic_cva6v_pkg;

    parameter int unsigned PAddrWidth     = cva6v_ai_core_pkg::CVA6UserCfg.PLEN;
    parameter int unsigned XWidth         = cva6v_ai_core_pkg::CVA6UserCfg.XLEN;
    parameter int unsigned PAddrSizeWidth = $clog2(cva6v_ai_core_pkg::CVA6UserCfg.PLEN);
    parameter int unsigned AxiStrbWidth   = cva6v_ai_core_pkg::AxiDataWidth / 8;

    parameter int unsigned PlatformIrqWidth = cva6v_ai_core_pkg::CVA6Cfg.PIRQ_WIDTH;

    // Types - RISCV
    typedef logic [PAddrWidth                     -1:0] aic_cva6v_paddr_t;
    typedef logic [XWidth                         -1:0] aic_cva6v_xwidth_t;
    typedef logic [PAddrSizeWidth                 -1:0] aic_cva6v_psize_t;

    // Types - AXI
    typedef logic [cva6v_ai_core_pkg::AxiIdWidth  -1:0] aic_cva6v_axi_id_t;
    typedef logic [AxiStrbWidth                   -1:0] aic_cva6v_axi_strb_t;
    typedef logic [cva6v_ai_core_pkg::AxiAddrWidth-1:0] aic_cva6v_axi_addr_t;
    typedef logic [cva6v_ai_core_pkg::AxiUserWidth-1:0] aic_cva6v_axi_user_t;
    typedef logic [cva6v_ai_core_pkg::AxiDataWidth-1:0] aic_cva6v_axi_data_t;

    // Types - MEM
    typedef logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] aic_cva6v_mem_be_t;
    typedef logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] aic_cva6v_mem_data_t;
    typedef logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] aic_cva6v_mem_addr_t;

    // Types - Perf
    typedef logic [PAddrWidth                             -2:0] aic_cva6v_perf_addr_t;
    typedef logic [cva6v_ai_core_pkg::PerfEventDeltaWidth -1:0] aic_cva6v_perf_delta_t;
    typedef logic [cva6v_ai_core_pkg::PerfEventAddrWidth  -1:0] aic_cva6v_perf_raptor_addr_t;
    typedef logic [4                                      -1:0] aic_cva6v_fu_status_t;

    typedef logic [PlatformIrqWidth-1:0] aic_cva6v_platf_irq_t;
endpackage
