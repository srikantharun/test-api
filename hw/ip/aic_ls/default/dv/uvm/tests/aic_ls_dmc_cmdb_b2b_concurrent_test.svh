// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS back to back IFD ODR
//   test while constantly being accessed via
//   AXI HP Slave IF.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_B2B_CONCURRENT_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_B2B_CONCURRENT_TEST_SV

class aic_ls_dmc_cmdb_b2b_concurrent_test extends aic_ls_dmc_cmdb_b2b_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_b2b_concurrent_test);

  function new (string name="aic_ls_dmc_cmdb_b2b_concurrent_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uvm_config_db#(uvm_object_wrapper)::set(this, "m_env.m_axi_system_env.master[1].sequencer.main_phase", "default_sequence", svt_axi_master_random_sequence::type_id::get());
    // Set the sequence length
    uvm_config_db#(int unsigned)::set(this, "m_env.m_axi_system_env.master[1].sequencer.svt_axi_master_random_sequence", "sequence_length", 2000);
    m_init_l1_en = 1;
    // target L1 start address, and MIFD0 (i.e. dev==0) will avoid it to avoid conflict in writing and reading through AXI SLV IF and through IFD/ODR
    cust_svt_axi_master_transaction::l1_bank_index = 0;
    aic_ls_axi_cfg_if_write_sequence::randomize_addr = 0; // disable randomization and use assignment instead to not conflict with cust_svt_axi_master_transaction addr generation
    m_set_odr_addr = 0; // use sequence randomization instead of randomizing in parent test class
  endfunction : build_phase

  virtual task pre_configure_seq(int dev);
    if (dev == 0) m_ifd_seq[dev].m_ag_mem_baseaddr += 32'h000_4000; // avoid start of L1 address because this address will be accessed via AXI HP Slave
  endtask

  virtual task test_seq();
    enable_cmdblk();
    for (int iter=0; iter < m_test_iteration; iter++) begin
      for (int dev=m_device_start; dev < m_device_end; dev++) begin
        automatic int a_dev  = dev;
        automatic int a_iter = iter;
        fork begin
          `uvm_info (get_name(), $sformatf("Iteration %0d of %0d for %s started", a_iter, m_test_iteration-1, AIC_LS_DMC_DEVICE_NAME[a_dev]), UVM_LOW)
          randomize_sequences(a_dev, (a_iter==m_test_iteration-1));
          pre_configure_seq(a_dev);
          case (a_dev)
            0: m_ifd_seq[0].start(null); // mvm ifd0
            1: m_ifd_seq[1].start(null); // mvm ifd1
            2: m_ifd_seq[2].start(null); // mvm ifd2
            3: m_ifd_seq[3].start(null); // mvm ifdw
            4: m_ifd_seq[4].start(null); // dwpu ifd0
            5: m_ifd_seq[5].start(null); // dwpu ifd1
            6: m_odr_seq[0].start(null); // mvm odr
            7: m_odr_seq[1].start(null); // dwpu_odr
          endcase
          `uvm_info (get_name(), $sformatf("Iteration %0d of %0d for %s fork-join_none started", a_iter, m_test_iteration-1, AIC_LS_DMC_DEVICE_NAME[a_dev]), UVM_LOW)
        end join_none
      end
      wait fork;
    end
    `uvm_info (get_name(), "Wait fork done!", UVM_LOW)
  endtask

endclass:aic_ls_dmc_cmdb_b2b_concurrent_test
`endif

