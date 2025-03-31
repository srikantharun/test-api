// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_CAC_TEST_SV
`define GUARD_COMMON_SEQ_LIB_CAC_TEST_SV

class common_seq_lib_cac_fill_test extends common_seq_lib_base_test;
  // Registration with the factory
  `uvm_component_utils(common_seq_lib_cac_fill_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]      dst_addr, src_addr;

  // Class constructor
  function new (string name="common_seq_lib_cac_fill_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("common_seq_lib_cac_fill_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);

  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("common_seq_lib_cac_fill_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    //=========================//
    // run CACHE fill sequence //
    //=========================//

    src_addr = 40'h100;
    dst_addr = 40'h1200;

    #5000ns
    axi_cac_seq.randomize() with {
      src_addr     == local::src_addr;
      dst_addr     == local::dst_addr;
      size         == 1024; 
      bandwidth    == BURST_SIZE_512BIT;
      delay        == 0;
      reorder_data == 1; 
    };
    foreach (env.axi_system_env.master[i])
      axi_cac_seq.start(env.axi_system_env.master[i].sequencer);

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_cac_fill_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:common_seq_lib_cac_fill_test

`endif //GUARD_COMMON_SEQ_LIB_CAC_TEST_SV
