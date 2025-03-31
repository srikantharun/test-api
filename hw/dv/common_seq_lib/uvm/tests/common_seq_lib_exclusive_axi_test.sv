// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_EXCLUSIVE_AXI_TEST_SV
`define GUARD_COMMON_SEQ_LIB_EXCLUSIVE_AXI_TEST_SV

class common_seq_lib_exclusive_axi_test extends common_seq_lib_base_test;
  // Registration with the factory
  `uvm_component_utils(common_seq_lib_exclusive_axi_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_addr;
  axi_master_write_random_sequence  axi_ex_wr_csl_seq;
  axi_master_read_random_sequence   axi_ex_rd_csl_seq;
  bit[3:0] ex_trans_id;
  bit cac_modifiable;

  // Class constructor
  function new (string name="common_seq_lib_exclusive_axi_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("common_seq_lib_exclusive_axi_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_ex_wr_csl_seq = axi_master_write_random_sequence::type_id::create("axi_ex_wr_csl_seq");
    axi_ex_rd_csl_seq = axi_master_read_random_sequence::type_id::create("axi_ex_rd_csl_seq");
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("common_seq_lib_exclusive_axi_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    ex_trans_id = $urandom_range(0,15);
    axi_addr    = $urandom_range(0, 'hFFFFFFFFFF);
    cac_modifiable = $urandom_range(0,1);

    `uvm_info("EXCLUSIVE ACCESS", $sformatf("Send exclusive read and write with addr: %0h and trans_id: %0h",axi_addr, ex_trans_id), UVM_LOW)

    if(!axi_ex_rd_csl_seq.randomize() with {
      sequence_length == 1;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      trans_id        == ex_trans_id;
      cfg_addr        == axi_addr;
      delay           == 0;
      burst_size      == BURST_SIZE_128BIT;
      burst_length    == 1;
      cache_modifiable  == cac_modifiable;
    }) `uvm_error("EXCLUSIVE ACCESS", "Write seq not randomized!")

    axi_ex_rd_csl_seq.start(env.axi_system_env.master[0].sequencer);

    if(!axi_ex_wr_csl_seq.randomize() with {
      sequence_length == 1;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      trans_id        == ex_trans_id;
      cfg_addr        == axi_addr;
      delay           == 0;
      burst_size      == BURST_SIZE_128BIT;
      burst_length    == 1;
      cache_modifiable  == cac_modifiable;
    }) `uvm_error("EXCLUSIVE ACCESS", "Read seq not randomized!")

    axi_ex_wr_csl_seq.start(env.axi_system_env.master[0].sequencer);

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_exclusive_axi_test", "Objection dropped", UVM_HIGH)
 
  endtask : run_phase
  
endclass:common_seq_lib_exclusive_axi_test

`endif //GUARD_COMMON_SEQ_LIB_WRITE_RAND_TEST_SV
