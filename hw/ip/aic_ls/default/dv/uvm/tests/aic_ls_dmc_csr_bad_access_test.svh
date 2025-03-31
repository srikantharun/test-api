// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:  tests IFD/ODR CSR access, by attempting writing/reading all the unused memory range and making sure we're getting an error.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CSR_BAD_ACCESS_TEST_SV
`define GUARD_AIC_LS_DMC_CSR_BAD_ACCESS_TEST_SV

class aic_ls_dmc_csr_bad_access_test extends aic_ls_dmc_defmem_bad_access_test;
  `uvm_component_utils (aic_ls_dmc_csr_bad_access_test);

  function new (string name="aic_ls_dmc_csr_bad_access_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task test_seq();
    cfg_addr_t mem_addr, mem_addr_q[$];
    // uvm_reg m_reg_list[$];

    // regs are:
    // m_ifd0_regmod.hw_capability Addr: 0x2000050
    // m_ifd0_regmod.dbg_id Addr: 0x2000048
    // m_ifd0_regmod.dbg_scratch Addr: 0x2000040
    // m_ifd0_regmod.cmdgen_status Addr: 0x2000038
    // m_ifd0_regmod.dbg_observe Addr: 0x2000030
    // m_ifd0_regmod.dp_status Addr: 0x2000028
    // m_ifd0_regmod.dp_ctrl Addr: 0x2000020
    // m_ifd0_regmod.irq_status Addr: 0x2000018
    // m_ifd0_regmod.irq_en Addr: 0x2000010
    // m_ifd0_regmod.cmdblk_status Addr: 0x2000008
    // m_ifd0_regmod.cmdblk_ctrl Addr: 0x2000000


    for (int j=0; j < 1; j++) begin
      for (int i=AIC_LS_ENV_DMC_CSR_DEPTH+8; i < AIC_LS_ENV_DEVICE_OFFSET; i=i+8) begin  // last register is 0x50 + 8
        mem_addr = (m_env_cfg.m_cid_offset * m_env_cfg.m_cid) + AIC_LS_ENV_CMDBLK_CSR_OFFSET + (AIC_LS_ENV_DEVICE_OFFSET * j ) + i;
        `uvm_info (get_name(), $sformatf("pushing address 0x%0x to queue", mem_addr), UVM_HIGH)
        mem_addr_q.push_back(mem_addr);
      end
    end

    foreach (mem_addr_q[i]) begin
      cfg_test_axi_write(mem_addr_q[i]);
      cfg_test_axi_read(mem_addr_q[i]);
    end
  endtask

endclass

`endif
