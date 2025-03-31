//  (C) Copyright Axelera AI 2024         //
//  All Rights Reserved                   //
//  Axelera AI Confidential               //
//  Owner : ana.stoisavljevic@axelera.ai  //

`ifndef GUARD_FABRIC_CSL_READ_INTERLEAVE_TEST_SV
`define GUARD_FABRIC_CSL_READ_INTERLEAVE_TEST_SV

class fabric_csl_read_interleave_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_read_interleave_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]      axi_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0]      axi_addr_aligned;
  bit [`AXI_LP_DATA_WIDTH-1:0]      axi_write_data;
  axi_master_read_random_sequence   axi_rd_seq1[int];
  svt_axi_transaction::burst_size_enum axi_burst_size;
  
  // Class constructor
  function new (string name="fabric_csl_read_interleave_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_read_interleave_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);

  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_read_interleave_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;

    foreach (env.axi_system_env.master[i]) begin
      if (i == init_trace) continue; // skip trace

      if (i < 10) begin
        axi_burst_size = $urandom_range(0,3);
      end
      else begin
        axi_burst_size = $urandom_range(0,4);
      end

      for (int iter=0; iter<2; iter++) begin
        automatic int seq_no = iter;

        `uvm_info("fabric_csl_read_interleave_test", $sformatf("Create sequence %0d", iter), UVM_LOW)
        axi_rd_seq1[iter]  = axi_master_read_random_sequence::type_id::create($sformatf("axi_rd_seq1[%0d]", iter));
        axi_addr = axi_legal_addr(i);
        axi_addr = axi_addr /128 * 128; // 2 x burst_size alligned
        axi_addr_aligned = axi_addr;
        axi_addr_aligned = axi_addr * (20 * (1 << axi_burst_size)) / (20 * (1 << axi_burst_size));
        if (axi_addr_aligned % 'h1000 + (20 * (1 << axi_burst_size)) > 'h1000)
           axi_addr_aligned = axi_addr_aligned - (20 * (1 << axi_burst_size));
        if (iter == 0) begin
          `uvm_info("fabric_csl_read_interleave_test", $sformatf("Randomize sequence #0"), UVM_LOW)
          assert(axi_rd_seq1[iter].randomize() with {
            sequence_length     == 'd1;
            burst_type          == svt_axi_master_transaction::INCR;
            cfg_addr            == axi_addr_aligned;
            burst_length        == 'd20;
            delay               == 0;
            burst_size          == axi_burst_size;
            wait_rsp            == 0;
          });
        end
        else begin
          `uvm_info("fabric_csl_read_interleave_test", $sformatf("Randomize sequence #%0d", iter), UVM_LOW)
          assert(axi_rd_seq1[iter].randomize() with {
            sequence_length     == 'd1;
            burst_type          inside {svt_axi_transaction::INCR, svt_axi_transaction::FIXED};  // based on issue #1712 WRAP is dropped
            cfg_addr            == axi_addr;
            delay               == 0;
            burst_size          == axi_burst_size;
            wait_rsp            == 0;
          });
        end
        fork
          begin
          `uvm_info("fabric_csl_read_interleave_test", $sformatf("Kick off sequence #%0d", seq_no), UVM_LOW)
          axi_rd_seq1[seq_no].start(env.axi_system_env.master[i].sequencer);
          end
        join_none
      end //for
      wait fork;
    end

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_read_interleave_test", "Objection dropped", UVM_HIGH)
 
  endtask : run_phase
  
endclass: fabric_csl_read_interleave_test

`endif //GUARD_FABRIC_CSL_READ_INTERLEAVE_TEST_SV
