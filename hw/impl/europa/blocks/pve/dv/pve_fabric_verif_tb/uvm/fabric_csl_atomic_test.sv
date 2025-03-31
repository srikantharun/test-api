//////////////////////////////////////////////////////////////
//  (C) Copyright Axelera AI 2024                           //
//  All Rights Reserved                                     //
//  Axelera AI Confidential                                 //
//  Owner : ana.stoisavljevic@axelera.ai                    //
//  Description: Send legal atomic traffic                  //
//////////////////////////////////////////////////////////////

`ifndef GUARD_FABRIC_CSL_ATOMIC_TEST_SV
`define GUARD_FABRIC_CSL_ATOMIC_TEST_SV

class fabric_csl_atomic_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_atomic_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]    axi_addr;
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  svt_axi_transaction::burst_size_enum axi_burst_size;
  int max_data_width;

  cust_atomic_seq atomic_seq;

  // Class constructor
  function new (string name="fabric_csl_atomic_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_atomic_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    atomic_seq = cust_atomic_seq::type_id::create("atomic_seq");
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_atomic_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;

repeat (10) begin
    foreach(env.axi_system_env.master[i]) begin
      if (i == 8) continue; // skip trace
      if (i == 9) continue; // skip ext noc
      if (i >= 10) continue; // atomic are supported only on LTF 

      axi_burst_size = 3;
      max_data_width = 8; // 8 bytes

      randcase
          1 : axi_addr = $urandom_range(`PVE_BASE + `DMA0_SA, `PVE_BASE + `DMA0_EA);
          1 : axi_addr = $urandom_range(`PVE_BASE + `DMA1_SA, `PVE_BASE + `DMA1_EA);
          1 : axi_addr = $urandom_range(`PVE_BASE + `CLINT_SA, `PVE_BASE + `CLINT_EA);
          //1 : axi_addr = $urandom_range(`PVE_BASE + `PERF_COUNTERS_SA, `PVE_BASE + `PERF_COUNTERS_EA); // FIXME: still not supported
          1 : axi_addr = $urandom_range(`PVE_BASE + `SPM_SA, `PVE_BASE + `SPM_EA);
      endcase

      axi_addr = axi_addr / max_data_width * max_data_width;


      atomic_seq.randomize() with {
        atomic_transaction_type == svt_axi_transaction::LOAD;
        _addr == axi_addr;
      };
      atomic_seq.start(env.axi_system_env.master[i].sequencer);

      atomic_seq.randomize() with {
        atomic_transaction_type == svt_axi_transaction::STORE;
        _addr == axi_addr;
      };
      atomic_seq.start(env.axi_system_env.master[i].sequencer);

      atomic_seq.randomize() with {
        atomic_transaction_type == svt_axi_transaction::SWAP;
        _addr == axi_addr;
      };
      atomic_seq.start(env.axi_system_env.master[i].sequencer);

      atomic_seq.randomize() with {
        atomic_transaction_type == svt_axi_transaction::COMPARE;
        _addr == axi_addr;
      };
      atomic_seq.start(env.axi_system_env.master[i].sequencer);
      #50ns;
    end
end
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_atomic_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:fabric_csl_atomic_test

`endif //GUARD_FABRIC_CSL_ATOMIC_TEST_SV

