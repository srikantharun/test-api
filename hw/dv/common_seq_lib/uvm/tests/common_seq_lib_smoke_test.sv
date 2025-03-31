// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_SMOKE_TEST_SV
`define GUARD_COMMON_SEQ_LIB_SMOKE_TEST_SV

class common_seq_lib_smoke_test extends common_seq_lib_base_test;
  // Registration with the factory
  `uvm_component_utils(common_seq_lib_smoke_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]    axi_addr;
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  
  // Class constructor
  function new (string name="common_seq_lib_smoke_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("common_seq_lib_smoke_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("common_seq_lib_smoke_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;
    repeat(10) begin 
      axi_addr = $urandom_range(0, 36'hFFFF_FFFF);
      axi_wr_rand_seq.randomize() with {
        sequence_length == 'd1;
        cfg_addr        == axi_addr;
        cfg_data[0]     == {axi_write_data};
        `ifdef DUT
          burst_type          == svt_axi_master_transaction::INCR;
        `endif
        `ifdef AXE_AXI_ERR_SUB
          inj_err == 1;
        `endif
      };
      axi_wr_rand_seq.start(env.axi_system_env.master[0].sequencer);
      #50ns
      axi_rd_rand_seq.randomize() with {
        sequence_length == 'd1;
        cfg_addr        == axi_addr;
        `ifdef DUT
          burst_type          == svt_axi_master_transaction::INCR;
        `endif
        `ifdef AXE_AXI_ERR_SUB
          inj_err == 1;
        `endif
      };
      axi_rd_rand_seq.start(env.axi_system_env.master[0].sequencer);
    end
    
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_smoke_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:common_seq_lib_smoke_test

`endif //GUARD_COMMON_SEQ_LIB_SMOKE_TEST_SV

