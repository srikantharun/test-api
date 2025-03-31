//////////////////////////////////////////////////////////////
//  (C) Copyright Axelera AI 2024                           //
//  All Rights Reserved                                     //
//  Axelera AI Confidential                                 //
//  Owner : ana.stoisavljevic@axelera.ai                    //
//  Description: Send some traffic from all initiators.      //
//  Randomize address in such way to hit different targets. //
//////////////////////////////////////////////////////////////

`ifndef GUARD_FABRIC_CSL_CONNECTIVITY_TEST_SV
`define GUARD_FABRIC_CSL_CONNECTIVITY_TEST_SV

class fabric_csl_connectivity_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_connectivity_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]    axi_addr;
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  svt_axi_transaction::burst_size_enum axi_burst_size;
  int max_data_width;
 
  // Class constructor
  function new (string name="fabric_csl_connectivity_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_connectivity_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_connectivity_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;

    foreach(env.axi_system_env.master[i]) begin
      if (i == init_trace) continue; // skip trace

      if (i < 10) begin
        axi_burst_size = 3;
        max_data_width = 8; // 8 bytes
      end
      else begin
        axi_burst_size = 6;
        max_data_width = 64; // 64 bytes
      end
      randomize_axi_address();
      foreach (axi_addr_a[k]) begin

      axi_addr = axi_addr_a[k] / max_data_width * max_data_width;
      if (axi_addr % 4096 + (1<<axi_burst_size) > 4096)
          axi_addr = axi_addr / (1<<axi_burst_size) * (1<<axi_burst_size);

      axi_wr_rand_seq.randomize() with {
        sequence_length == 'd1;
        cfg_addr        == axi_addr;
        cfg_data[0]     == {8{axi_write_data}};
        burst_size      == axi_burst_size;
        max_bw          == max_data_width;
        burst_type      == svt_axi_transaction::INCR;
        inj_err         == 1;
      };
      axi_wr_rand_seq.start(env.axi_system_env.master[i].sequencer);
      check_conn_matrix(axi_wr_rand_seq.response);
      #50ns
      axi_rd_rand_seq.randomize() with {
        sequence_length == 'd1;
        cfg_addr        == axi_addr;
        burst_size      == axi_burst_size;
        burst_type      == svt_axi_transaction::INCR;
        inj_err         == 1;
      };
      axi_rd_rand_seq.start(env.axi_system_env.master[i].sequencer);
      check_conn_matrix(axi_rd_rand_seq.response);
    end
    end

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_connectivity_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:fabric_csl_connectivity_test

`endif //GUARD_FABRIC_CSL_CONNECTIVITY_TEST_SV

