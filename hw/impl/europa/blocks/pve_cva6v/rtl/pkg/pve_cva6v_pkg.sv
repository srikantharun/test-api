// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>


/// PVE CVA6V europa implementation package
///
package pve_cva6v_pkg;
  import cva6v_pve_pkg::*;
  import raptor_pkg::*;

  parameter int unsigned PLength        = CVA6VConfig.CVA6Cfg.PLEN;
  parameter int unsigned XLength        = CVA6VConfig.CVA6Cfg.XLEN;
  parameter int unsigned PAddrSizeWidth = $clog2(PLength);
  parameter int unsigned AxiStrbWidth   = AxiDataWidth / 8;
  parameter int unsigned PlatfIRQWidth  = CVA6VConfig.CVA6Cfg.PIRQ_WIDTH;
  parameter int unsigned EventPortCount = CVA6VConfig.CVA6Cfg.NrCommitPorts + 1;
  parameter int unsigned EventDelta     = $clog2(VRFBankCount*VRFPortWidth+1);

  // Types - RISCV
  typedef logic [XLength       -1:0]                     pve_cva6v_xwidth_t;
  typedef logic [MemRegionCount-1:0][PLength       -1:0] pve_cva6v_memreg_addr_t;
  typedef logic [MemRegionCount*PLength            -1:0] pve_cva6v_memreg_addr_1d_t;
  typedef logic [MemRegionCount-1:0][PAddrSizeWidth-1:0] pve_cva6v_memreg_size_t;
  typedef logic [MemRegionCount*PAddrSizeWidth     -1:0] pve_cva6v_memreg_size_1d_t;
  typedef logic [MemRegionCount-1:0]                     pve_cva6v_memreg_tcdm_t;
  typedef logic [PlatfIRQWidth -1:0]                     pve_cva6v_platf_irq_t;

  // Types - MEM
  typedef logic [MemPortCount  -1:0]                       pve_cva6v_mem_logic_t;
  typedef logic [MemPortCount  -1:0][MemPortBeWidth  -1:0] pve_cva6v_mem_be_t;
  typedef logic [MemPortCount*MemPortBeWidth         -1:0] pve_cva6v_mem_be_1d_t;
  typedef logic [MemPortCount  -1:0][MemPortWidth    -1:0] pve_cva6v_mem_data_t;
  typedef logic [MemPortCount*MemPortWidth           -1:0] pve_cva6v_mem_data_1d_t;
  typedef logic [MemPortCount  -1:0][MemPortAddrWidth-1:0] pve_cva6v_mem_addr_t;
  typedef logic [MemPortCount*MemPortAddrWidth       -1:0] pve_cva6v_mem_addr_1d_t;

  // Types - Raptor
  typedef fu_status_e [  FunctUnitCount-1:0] perf_cntr_fu_status_t;
  typedef logic       [4*FunctUnitCount-1:0] perf_cntr_fu_status_1d_t;

  // Types - Perf Counters
  typedef logic [EventPortCount-2:0][PLength-2:0]                        pve_cva6v_event_addr_full_t;
  typedef logic [PerfEventAddrWidth-1:0]                                 pve_cva6v_event_addr_last_t;
  typedef logic [EventPortCount-1:0][PerfEventAddrWidth-1:0]             pve_cva6v_event_addr_t;
  typedef logic [EventPortCount*PerfEventAddrWidth-1:0]                  pve_cva6v_event_addr_1d_t;
  typedef logic [EventPortCount-1:0][PerfEventCount-1:0][EventDelta-1:0] pve_cva6v_event_deltas_t;
  typedef logic [EventPortCount*PerfEventCount*EventDelta-1:0]           pve_cva6v_event_deltas_1d_t;

endpackage
