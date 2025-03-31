// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC simple concurrency test
//      This test preloads l1, and then launches a series of AXI burst reads from L1, and a burst of RVV L1 reads, 
//      timed in a concurrent manner, to make sure that RVV waits for AXI to be done before it actually reads
//      this test only launches RVV and AXI master port, w/o using IFDs, to keep it simple and easier to time.
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_SIMPLE_CONCURRENCY_TEST_SV
`define GUARD_AIC_LS_SIMPLE_CONCURRENCY_TEST_SV

// AXI master read sequence, using fixed axi transcation
class aic_ls_axi_master_fixed_read_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand bit[35:0]    mem_addr;
  rand bit          b2b_en;
  rand int unsigned burst_len = 1;

  /** UVM Object Utility macro */
  `uvm_object_utils(aic_ls_axi_master_fixed_read_sequence)

  /** Class Constructor */
  function new(string name = "aic_ls_axi_master_fixed_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_configuration get_cfg;
    cust_svt_axi_master_transaction read_txn;
    `uvm_info("aic_ls_axi_master_fixed_read_sequence: Body", "Entered", UVM_LOW)

    super.body();

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("aic_ls_axi_master_fixed_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    /** Set up the read transaction */
    `uvm_create(read_txn)
    read_txn.add_l1_base_addr = 0;
    if(!read_txn.randomize() with {
      addr        == mem_addr;
      xact_type   == svt_axi_transaction::READ;
      burst_type  == svt_axi_transaction::FIXED;
      burst_size  == svt_axi_transaction::BURST_SIZE_512BIT;
      atomic_type == svt_axi_transaction::NORMAL;
      burst_length == burst_len;
      if(b2b_en) {
        foreach(rready_delay[i]) {
          rready_delay[i] == 0;
        }
      }
    }) begin
      `uvm_fatal(get_name(), "read_txn randomization error!");
    end else begin
      `uvm_info(get_name(), $sformatf("mem_addr: 0x%0x read_txn: %s", mem_addr, read_txn.sprint()), UVM_HIGH)
    end

    /** Send the read transaction */
    `uvm_send(read_txn)

    /** Wait for the read transaction to complete */
    get_response(rsp);
    `uvm_info(get_name(), "axi rd rsp received", UVM_LOW)
    `uvm_info(get_name(), "Exiting", UVM_LOW)
  endtask : body

endclass : aic_ls_axi_master_fixed_read_sequence

class aic_ls_simple_concurrency_test extends aic_ls_rvv_basic_test;
  `uvm_component_utils (aic_ls_simple_concurrency_test);

  cfg_addr_t accessed_address;
  cfg_addr_t axi_address;
  cfg_addr_t rvv_address;

  function new (string name="aic_ls_simple_concurrency_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    rvv_repeat_cycles = 10;
    super.configure_phase(phase);
    m_test_iteration = 20;
  endtask

  virtual task test_seq();
    aic_ls_axi_master_fixed_read_sequence axi_read;
    hp_data_t rdata, bkdr_rdata;
    int index;

    `uvm_info(get_name(), "Start of test", UVM_LOW)

    init_l1();
    
    for (int iter=0; iter < m_test_iteration; iter++) begin
      // For simplicity, we will start with l1 start address, and just advance by 0x1000 every time.
      accessed_address = m_env_cfg.m_l1_full_start_addr + 'h1000*iter;
      axi_address = accessed_address;
      rvv_address = accessed_address - m_env_cfg.m_l1_full_start_addr;
      rvv_address[5:4] = $urandom_range(0,3); // make it choose sub-banks at random

      index = (axi_address - (m_env_cfg.m_l1_full_start_addr))/m_env_cfg.m_pword_size;

      `uvm_info (get_name(), $sformatf("Forcing address 0x%0x on the test! AXI address is 0x%0x and RVV address is 0x%0x", accessed_address, axi_address, rvv_address), UVM_LOW)
      rvv_seq.forced_address = rvv_address;

      // FD RD
      axi_read = aic_ls_axi_master_fixed_read_sequence::type_id::create("axi_read");
      if (!(axi_read.randomize() with {
          mem_addr        == axi_address;
          burst_len == 15;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for axi_read!")
      end
      
      // running axi read in the same time as rvv read
      fork
        begin
          axi_read.start(m_env.m_axi_system_env.master[1].sequencer);
        end
        begin
          repeat(4) @(posedge m_env.m_axi_system_env.vif.common_aclk); // waiting a bit so axi read has time to get to MMIO transaction level
          rvv_seq.start(m_env.m_rvv_agent.m_rvv_sequencer);  // we will run a bunch of rvv requests, to make sure we fill the spill registers and make rvv_ready go down.
        end
      join
      //#100ns;
      rdata = axi_read.rsp.data[0];
      // BD READ
      bkdr_rdata = hdl_read(index);  // compare axi read data with l1 data. not really the purpose of this test, but why not make sure?
      if (bkdr_rdata != rdata) begin
        `uvm_error(get_name(), $sformatf("BD_WR != FD_RD at L1 address: 0x%0x BD_WR: 0x%0x FD_RD: 0x%0x", axi_address, bkdr_rdata, rdata))
      end else begin
        `uvm_info (get_name(), $sformatf("[%0d] BD_WR == FD_RD to L1 address: 0x%0x is 0x%0x", iter, axi_address, rdata), UVM_LOW)
      end

      #10;
    end

    #20us;
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass:aic_ls_simple_concurrency_test
`endif

