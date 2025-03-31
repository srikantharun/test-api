/////////////////////////////////////////////////////////////////////
//  (C) Copyright Axelera AI 2024                                  //
//  All Rights Reserved                                            //
//  Axelera AI Confidential                                        //
//  Owner : ana.stoisavljevic@axelera.ai                           //
//  Description: Send legal exclusive traffic from all initiators. //
//  Randomize address in such way to hit different targets.        //
/////////////////////////////////////////////////////////////////////

`ifndef GUARD_FABRIC_CSL_EXCLUSIVE_AXI_TEST_SV
`define GUARD_FABRIC_CSL_EXCLUSIVE_AXI_TEST_SV

class fabric_csl_exclusive_axi_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_exclusive_axi_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0] axi_addr;
  axi_master_write_random_sequence  axi_ex_wr_seq;
  axi_master_read_random_sequence   axi_ex_rd_seq;
  bit[3:0] ex_trans_id;
  bit cac_modifiable;
  bit cac_bufferable;
  bit[2:0] axi_prot;
  bit axi_cache_allocate;
  bit axi_cache_other_allocate;

  int axi_len_max, axi_len;
  svt_axi_transaction::burst_size_enum axi_burst_size;
  int max_data_width;

  svt_axi_transaction::burst_type_enum axi_burst_type;

  // Class constructor
  function new (string name="fabric_csl_exclusive_axi_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_exclusive_axi_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    axi_ex_wr_seq = axi_master_write_random_sequence::type_id::create("axi_ex_wr_seq");
    axi_ex_rd_seq = axi_master_read_random_sequence::type_id::create("axi_ex_rd_seq");
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_exclusive_axi_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

repeat(10) begin
    foreach(env.axi_system_env.master[i]) begin
      if (i == init_trace) continue; // skip trace

      if (i < 10) begin
        //axi_burst_size = 3;
        axi_burst_size = $urandom_range(0,3);
        max_data_width = 8; // 8 bytes
      end
      else begin
        //axi_burst_size = 6;
        axi_burst_size = $urandom_range(0,4);
        max_data_width = 64; // 64 bytes
      end

      axi_len_max = 128 / (1 << axi_burst_size); // The maximum number of bytes that can be transferred in an exclusive transaction is 128.
      if (axi_len_max > 16) // The Length of an exclusive access must not exceed 16 transfers.
        axi_len_max = 16;
         
      axi_len = $urandom_range(1,axi_len_max);

      axi_burst_type = $urandom_range(0, 1); // based on issue #1712 WRAP is dropped

      if (axi_len == 16) // total number of transfers need to be power of 2, hence len must be power of 2
        axi_len = 16;
      else if (axi_len >= 8)
        axi_len = 8;
      else if (axi_len >= 4)
        axi_len = 4;
      else if (axi_len >= 2)
        axi_len = 2;
      else
        axi_len = 1;

      ex_trans_id = $urandom_range(0,15);
      axi_addr    = {$urandom_range(0, 'hFF), $urandom_range(0, 'hFFFF_FFFF)};
      cac_modifiable = $urandom_range(0,1);
      cac_bufferable = $urandom_range(0,1);
      axi_prot = $urandom_range(0,7);
      axi_cache_allocate = $urandom_range(0,1);
      axi_cache_other_allocate = $urandom_range(0,1);

      axi_addr = axi_legal_addr(i);

      axi_addr = axi_addr / (axi_len * (1 << axi_burst_size)) * (axi_len * (1 << axi_burst_size)); // addr must be aligned to the total number of bytes

      `uvm_info("EXCLUSIVE ACCESS", $sformatf("Send exclusive read and write with addr: %0h, trans_id: %0h, burst_size: %0s, burst_len: %0d",axi_addr, ex_trans_id, burst_size_t'(axi_burst_size), axi_len), UVM_LOW)
  
      if(!axi_ex_rd_seq.randomize() with {
        sequence_length      == 1;
        atomic_type          == svt_axi_transaction::EXCLUSIVE;
        trans_id             == ex_trans_id;
        cfg_addr             == axi_addr;
        delay                == 0;
        burst_size           == axi_burst_size;
        burst_type           == axi_burst_type;
        burst_length         == axi_len;
        cache_modifiable     == cac_modifiable;
        cache_bufferable     == cac_bufferable;
        burst_prot           == axi_prot;
        cache_allocate       == axi_cache_allocate;
        cache_other_allocate == axi_cache_other_allocate;
      }) `uvm_error("EXCLUSIVE ACCESS", "Write seq not randomized!")

      axi_ex_rd_seq.start(env.axi_system_env.master[i].sequencer);
      check_conn_matrix(axi_ex_rd_seq.response);

      if(!axi_ex_wr_seq.randomize() with {
        sequence_length      == 1;
        atomic_type          == svt_axi_transaction::EXCLUSIVE;
        trans_id             == ex_trans_id;
        cfg_addr             == axi_addr;
        delay                == 0;
        burst_size           == axi_burst_size;
        burst_type           == axi_burst_type;
        burst_length         == axi_len;
        cache_modifiable     == cac_modifiable;
        cache_bufferable     == cac_bufferable;
        cache_allocate       == axi_cache_allocate;
        cache_other_allocate == axi_cache_other_allocate;
        burst_prot           == axi_prot;
        max_bw               == max_data_width;
      }) `uvm_error("EXCLUSIVE ACCESS", "Read seq not randomized!")
  
      axi_ex_wr_seq.start(env.axi_system_env.master[i].sequencer);
      check_conn_matrix(axi_ex_wr_seq.response);

    end
end
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_exclusive_axi_test", "Objection dropped", UVM_HIGH)
 
  endtask : run_phase
  
endclass:fabric_csl_exclusive_axi_test

`endif //GUARD_FABRIC_CSL_EXCLUSIVE_AXI_TEST_SV
