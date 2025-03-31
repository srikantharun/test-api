// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Config File for MMIO Agent
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef MMIO_CONFIG_SV
`define MMIO_CONFIG_SV

/** Configuration object to token agent. new configurations were added to support the RVV case */
class mmio_config extends uvm_object;
  `uvm_object_utils(mmio_config)

  string       m_mmio_name;
  bit          m_is_active;
  int unsigned m_int_req_vld_to_rdy_timeout_cycles = 20;
  int unsigned m_ext_req_vld_to_rdy_timeout_cycles = 100;
  int          m_internal_start_address = MMIO_INTERNAL_CHIP_OFFSET + MMIO_INTERNAL_ADDRESS_START;
  int          m_internal_end_address   = MMIO_INTERNAL_CHIP_OFFSET + MMIO_INTERNAL_ADDRESS_END;
  int          m_has_scoreboard;
  int unsigned banks_num;
  int unsigned sub_banks_num;
  string       m_memory_path;

  function new (string name = "mmio_config");
    super.new (name);
  endfunction

  function void set_defaults();  // Defaults to be used in development, will review later.
    m_int_req_vld_to_rdy_timeout_cycles = 20;
    m_ext_req_vld_to_rdy_timeout_cycles = 100;
    m_internal_start_address = MMIO_INTERNAL_CHIP_OFFSET + MMIO_INTERNAL_ADDRESS_START;
    m_internal_end_address   = MMIO_INTERNAL_CHIP_OFFSET + MMIO_INTERNAL_ADDRESS_END;
    m_has_scoreboard = 1;
    banks_num = 16;
    sub_banks_num = 4;
    m_memory_path = "hdl_top.dut.u_aic_ls.u_l1.u_l1_mem";
  endfunction

endclass

`endif // MMIO_CONFIG_SV


