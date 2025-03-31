// *** (C) Copyright Axelera AI 2024                                                  *** //
// *** All Rights Reserved                                                            *** //
// *** Axelera AI Confidential                                                        *** //
// *** Owner : srinivas.prakash@axelera.ai                                            *** //
// *****************************************************************************************
// Description: This Class is used to check the sanity between RTL & the TB           *** //
// *****************************************************************************************

`ifndef GUARD_ENOC_SMOKE_TEST_SV
`define GUARD_ENOC_SMOKE_TEST_SV

class enoc_smoke_test extends enoc_base_test;
  // Registration with the factory
  `uvm_component_utils(enoc_smoke_test)
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  
  // Class constructor
  function new (string name="enoc_smoke_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("enoc_smoke_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    int mst_num=0;
    super.run_phase(phase);
    
    `uvm_info ("enoc_smoke_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);
    repeat(num_rand_addr) begin
      gen_axi_addrs(/*is_rsvd*/ 0);
    end
    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;
    if((get_init_q.size > 0) && (rand_addr_q.size > 0)) begin //{
      foreach(get_init_q[k]) begin //{
        mst_num = get_init_q[k];

        if(get_init_q[k] == e_sdma_0_init_lt || get_init_q[k] == e_sdma_1_init_lt || get_init_q[k] == e_sdma_0_init_ht_0 || get_init_q[k] == e_sdma_0_init_ht_1 || get_init_q[k] == e_sdma_1_init_ht_0 || get_init_q[k] == e_sdma_1_init_ht_1)
          continue; //skip the execution for SDMA //TODO:rm after rtl connection & pctl access 
        foreach(rand_addr_q[i]) begin //{
          axi_rand_wr_seq.randomize() with {
            sequence_length == 'd1;
            cfg_addr        == rand_addr_q[i];
            cfg_data[0]     == {8{axi_write_data}};
            init_num        == get_init_q[k];
          };
          axi_rand_wr_seq.start(env.axi_system_env.master[mst_num].sequencer);
          `uvm_info(get_type_name(), "\n********************** WRITE_TXN *************************", UVM_LOW)
          check_address(rand_addr_q[i]);
          //chk_conn_matrix(axi_rand_wr_seq.write_transaction); //TODO: en after conn_rtl_fix
          `uvm_info(get_type_name(), $sformatf("INIT = %d, WR_ADDR = 0x%h", mst_num, rand_addr_q[i]), UVM_LOW);
          `uvm_info(get_type_name(), "**********************************************************\n", UVM_LOW)
          #50ns
          axi_rand_rd_seq.randomize() with {
            sequence_length == 'd1;
            cfg_addr        == rand_addr_q[i];
            init_num        == get_init_q[k];
          };
          axi_rand_rd_seq.start(env.axi_system_env.master[mst_num].sequencer);
          `uvm_info(get_type_name(), "\n********************** READ_TXN *************************", UVM_LOW)
          check_address(rand_addr_q[i]);
          //chk_conn_matrix(axi_rand_rd_seq.read_transaction);
          `uvm_info(get_type_name(), $sformatf("INIT = %d, RD_ADDR = 0x%h", mst_num, rand_addr_q[i]), UVM_LOW);
          `uvm_info(get_type_name(), "**********************************************************\n", UVM_LOW)
        end //}
      end //}
    end //}
    #10ns;
    //phase.phase_done.set_drain_time(this, 3ms);
    phase.drop_objection(this);
    `uvm_info ("enoc_smoke_test", "Objection dropped", UVM_HIGH)
  endtask : run_phase
  
  
endclass:enoc_smoke_test

`endif
