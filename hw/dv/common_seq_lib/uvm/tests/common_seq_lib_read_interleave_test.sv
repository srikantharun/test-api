// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_READ_INTERLEAVE_TEST_SV
`define GUARD_COMMON_SEQ_LIB_READ_INTERLEAVE_TEST_SV

class common_seq_lib_read_interleave_test extends common_seq_lib_base_test;
  // Registration with the factory
  `uvm_component_utils(common_seq_lib_read_interleave_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]      axi_addr;
  bit [`AXI_LP_ADDR_WIDTH-1:0]      axi_addr_aligned;
  bit [`AXI_LP_ADDR_WIDTH-1:0]      dst_addr;
  bit [`AXI_LP_DATA_WIDTH-1:0]      axi_write_data;
  bit [`AXI_HP_DATA_WIDTH-1:0]      dma_write_data[];
  axi_master_read_random_sequence   axi_rd_csl_seq1[int];
  
  // Class constructor
  function new (string name="common_seq_lib_read_interleave_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("common_seq_lib_read_interleave_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);

  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("common_seq_lib_read_interleave_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;

    for (int iter=0; iter<2; iter++) begin
        automatic int seq_no = iter;

        `uvm_info("common_seq_lib_read_interleave_test", $sformatf("Create sequence %0d", iter), UVM_LOW)
        axi_rd_csl_seq1[iter]  = axi_master_read_random_sequence::type_id::create($sformatf("axi_rd_csl_seq1[%0d]", iter));
        axi_addr = $urandom_range(0, 40'h1FFF);
        axi_addr = axi_addr /128 * 128; // 2 x burst_size alligned
        axi_addr_aligned = axi_addr;
        axi_addr_aligned[7:0] = 0;
        if (iter == 0) begin
          `uvm_info("common_seq_lib_read_interleave_test", $sformatf("Randomize sequence #0"), UVM_LOW)
          assert(axi_rd_csl_seq1[iter].randomize() with {
            sequence_length     == 'd1;
            burst_type          == svt_axi_master_transaction::INCR;
            cfg_addr            == axi_addr_aligned;
            burst_length        == 'd20;
            delay               == 0;
            burst_size          == BURST_SIZE_512BIT;
          });
        end
        else begin
          `uvm_info("common_seq_lib_read_interleave_test", $sformatf("Randomize sequence #%0d", iter), UVM_LOW)
          assert(axi_rd_csl_seq1[iter].randomize() with {
            sequence_length     == 'd1;
            cfg_addr            == axi_addr;
            delay               == 0;
            burst_size          == BURST_SIZE_512BIT;
          });
        end
        fork
          begin
          `uvm_info("common_seq_lib_read_interleave_test", $sformatf("Kick off sequence #%0d", seq_no), UVM_LOW)
          axi_rd_csl_seq1[seq_no].start(env.axi_system_env.master[0].sequencer);
          end
        join_none
      end //for
   wait fork;

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_read_interleave_test", "Objection dropped", UVM_HIGH)
 
  endtask : run_phase
  
endclass:common_seq_lib_read_interleave_test

`endif //GUARD_COMMON_SEQ_LIB_READ_INTERLEAVE_TEST_SV
