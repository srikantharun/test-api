// *** (C) Copyright Axelera AI 2024                                                  *** //
// *** All Rights Reserved                                                            *** //
// *** Axelera AI Confidential                                                        *** //
// *** Owner : srinivas.prakash@axelera.ai                                            *** //
// *****************************************************************************************
// Description: This Class is used to test the bandwidth of any init-targ pair by     *** //
// flooding the bus with huge traffic pattern which can be controlled using +arg      *** //
// *****************************************************************************************

`ifndef GUARD_ENOC_BW_UTILIZATION_TEST_SV
`define GUARD_ENOC_BW_UTILIZATION_TEST_SV

class enoc_bw_utilization_test extends enoc_base_test;
  // Registration with the factory
  `uvm_component_utils(enoc_bw_utilization_test)
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  
  // Class constructor
  function new (string name="enoc_bw_utilization_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("enoc_bw_utilization_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    int mst_num=0;
    super.run_phase(phase);
    
    `uvm_info ("enoc_bw_utilization_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);
    repeat(num_rand_addr) begin
      gen_axi_addrs(/*is_rsvd*/ 0);
    end
    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;
    if((get_init_q.size > 0) && (rand_addr_q.size > 0)) begin //{
      foreach(get_init_q[k]) begin //{
        mst_num = get_init_q[k];

        if(get_init_q[k] == e_sdma_0_init_lt || get_init_q[k] == e_sdma_1_init_lt || get_init_q[k] == e_sdma_0_init_ht_0 || get_init_q[k] == e_sdma_0_init_ht_1 || get_init_q[k] == e_sdma_1_init_ht_0 || get_init_q[k] == e_sdma_1_init_ht_1)
          continue; //TODO:rm after rtl connection & #1350 fix
        foreach(rand_addr_q[i]) begin //{
          axi_mst_seq.randomize() with {
            sequence_length == 'd1;
            addr        == rand_addr_q[i];
            data[0]     == {8{axi_write_data}};
            init_num        == get_init_q[k];
            xact_type       == svt_axi_transaction::WRITE;
            b2b_txn         == 1;
          };
          axi_mst_seq.start(env.axi_system_env.master[mst_num].sequencer);
          chk_conn_matrix(axi_rand_wr_seq.write_transaction);
          $display("\n********************** WRITE_TXN *************************");
          check_address(rand_addr_q[i]);
          $display("INIT = %d, WR_ADDR = 0x%h", mst_num, rand_addr_q[i]);
          $display("**********************************************************\n");
          #50ns
          axi_mst_seq.randomize() with {
            sequence_length == 'd1;
            addr        == rand_addr_q[i];
            init_num        == get_init_q[k];
            xact_type       == svt_axi_transaction::READ;
            b2b_txn         == 1;
          };
          axi_mst_seq.start(env.axi_system_env.master[mst_num].sequencer);
          chk_conn_matrix(axi_rand_rd_seq.read_transaction);
          $display("\n********************** READ_TXN *************************");
          check_address(rand_addr_q[i]);
          $display("INIT = %d, RD_ADDR = 0x%h", mst_num, rand_addr_q[i]);
          $display("**********************************************************\n");
        end //}
      end //}
    end //}
    #10ns;
    //phase.phase_done.set_drain_time(this, 3ms);
    phase.drop_objection(this);
    `uvm_info ("enoc_bw_utilization_test", "Objection dropped", UVM_HIGH)
  endtask : run_phase
  
  
endclass:enoc_bw_utilization_test

`endif
