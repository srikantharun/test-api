///////////////////////////////////////////////////////////
//  (C) Copyright Axelera AI 2024                        //
//  All Rights Reserved                                  //
//  Axelera AI Confidential                              //
//  Owner : ana.stoisavljevic@axelera.ai                 //
//  Description: Send random traffic from all initiators //
//               to all targets.                         //
///////////////////////////////////////////////////////////

`ifndef GUARD_FABRIC_CSL_RANDOM_TEST_SV
`define GUARD_FABRIC_CSL_RANDOM_TEST_SV

class fabric_csl_random_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_random_test)
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  svt_axi_transaction::burst_size_enum axi_burst_size;
  int max_data_w;
  
  // Class constructor
  function new (string name="fabric_csl_random_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_random_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_random_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);
    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;
    foreach(env.axi_system_env.master[i]) begin
      if (i == init_trace) continue; // skip trace
      randomize_axi_address();
      foreach(axi_addr_a[k]) begin
        if (i < 10) begin
          axi_burst_size = $urandom_range(0,3);
          max_data_w = 8; // 8 bytes
        end
        else begin
          axi_burst_size = $urandom_range(0,6);
          max_data_w = 64; // 64 bytes
        end
        if (axi_addr_a[k] % 'h1000 + (1 << axi_burst_size) > 'h1000) // 4K boundary
           axi_addr_a[k] = axi_addr_a[k] / (1 << axi_burst_size) * (1 << axi_burst_size); // align address to the burst_size

        `uvm_info("fabric_csl_random_test", $sformatf("INIT %s write to addr = %h",init_t'(i), axi_addr_a[k]), UVM_LOW);

        axi_wr_rand_seq.randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr_a[k];
          cfg_data[0]     == {8{axi_write_data}};
          burst_size      == axi_burst_size;
          max_bw          == max_data_w;
          inj_err         == 1;
          burst_type      inside {svt_axi_transaction::INCR, svt_axi_transaction::FIXED}; // based on issue #1712 WRAP is dropped
        };
        axi_wr_rand_seq.start(env.axi_system_env.master[i].sequencer);
        check_conn_matrix(axi_wr_rand_seq.response);
        #50ns
        `uvm_info("fabric_csl_random_test", $sformatf("INIT %s read from addr = %h",init_t'(i), axi_addr_a[k]), UVM_LOW);
        axi_rd_rand_seq.randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr_a[k];
          burst_size      == axi_burst_size;
          inj_err         == 1;
          burst_type      inside {svt_axi_transaction::INCR, svt_axi_transaction::FIXED};  // based on issue #1712 WRAP is dropped
        };
        axi_rd_rand_seq.start(env.axi_system_env.master[i].sequencer);
        check_conn_matrix(axi_rd_rand_seq.response);
      end
    end
    
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_random_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:fabric_csl_random_test

`endif //GUARD_FABRIC_CSL_RANDOM_TEST_SV

