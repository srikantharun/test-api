// *** (C) Copyright Axelera AI 2024                                                  *** //
// *** All Rights Reserved                                                            *** //
// *** Axelera AI Confidential                                                        *** //
// *** Owner : srinivas.prakash@axelera.ai                                            *** //
// *****************************************************************************************
// Description: This Class is used to check the exclusives between INITS & TARGS      *** //
// *****************************************************************************************

`ifndef GUARD_ENOC_EXCLUSIVES_TEST_SV
`define GUARD_ENOC_EXCLUSIVES_TEST_SV

class enoc_exclusives_test extends enoc_base_test;
  // Registration with the factory
  `uvm_component_utils(enoc_exclusives_test)
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  
  // Class constructor
  function new (string name="enoc_exclusives_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("enoc_exclusives_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    int mst_num=0;
    super.run_phase(phase);
    
    `uvm_info ("enoc_exclusives_test", "Objection raised", UVM_LOW)
    phase.raise_objection(this);
    `uvm_info (get_type_name(), "Enter 3A", UVM_LOW)
    // -----------------------------
    // #2211: Scenario 3b.EX-2I-A
    // -----------------------------
    // I1 ExRD
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
      `uvm_fatal(get_type_name(), "3A: I1 ExRD failed with RESP: OKAY");
            
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 
    

    // I2 ExRD
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_pve_1_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd21;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_pve_1_init_lt].sequencer);
    if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
      `uvm_fatal(get_type_name(), "3A: I2 ExRD failed with RESP: OKAY");

    // I2 ExWR
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_pve_1_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd21;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_pve_1_init_lt].sequencer);
    if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
      `uvm_fatal(get_type_name(), "3A: I2 ExWR failed with RESP: OKAY");

    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExWR
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3A: I1 ExWR failed with RESP: OKAY");
    
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExRD new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
      `uvm_fatal(get_type_name(), "3A: I1 new ExRD failed with RESP: OKAY");

    // I1 ExWR new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
      `uvm_fatal(get_type_name(), "3A: I1 new ExWR failed with RESP: OKAY");

    repeat(500) @(posedge tb_intf.enoc_clk);
    
    `uvm_info (get_type_name(), "Enter 3B", UVM_LOW)
    // -----------------------------
    // #2211: Scenario 3b.EX-2I-B
    // -----------------------------
    // I1 ExRD
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_64BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3B: I1 ExRD failed with RESP: OKAY");
            
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 
    
    // I2 NormalWR
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_pve_1_init_lt;
      atomic_type     == svt_axi_transaction::NORMAL;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_64BIT;
      burst_length    == 1;
      id              == 'd21;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_pve_1_init_lt].sequencer);
    //if (axi_mst_seq.transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3B: I2 NormalWR failed with RESP: OKAY");

    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExWR
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_64BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3B: I1 ExWR failed with RESP: OKAY");
    
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExRD new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_64BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3B: I1 new ExRD failed with RESP: OKAY");

    // I1 ExWR new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_64BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "3B: I1 new ExWR failed with RESP: OKAY");

    repeat(500) @(posedge tb_intf.enoc_clk);
    
    `uvm_info (get_type_name(), "Enter 4", UVM_LOW)
    // -----------------------------
    // #2211: Scenario 4.EX-MULTI-A
    // -----------------------------
    // I1 ExRD
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "4: I1 ExRD failed with RESP: OKAY");
            
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 
    
    // I2 NormalWR
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_pve_1_init_lt;
      atomic_type     == svt_axi_transaction::NORMAL;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd21;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_pve_1_init_lt].sequencer);
    //if (axi_mst_seq.transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "4: I2 NormalWR failed with RESP: OKAY");

    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExRD new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::READ;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_rd_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "4: I1 new ExRD failed with RESP: OKAY");

    // I1 ExWR new
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd31;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "4: I1 new ExWR failed with RESP: OKAY");
    
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 

    // I1 ExWR old
    axi_mst_seq.randomize() with {
      sequence_length == 'd1;
      addr            == `SYS_SPM_TARG_SA;
      init_num        == e_apu_init_lt;
      atomic_type     == svt_axi_transaction::EXCLUSIVE;
      xact_type       == svt_axi_transaction::WRITE;
      burst_type      == svt_axi_transaction::INCR;
      burst_size      == svt_axi_transaction::BURST_SIZE_32BIT;
      burst_length    == 1;
      id              == 'd11;
    };
    axi_mst_seq.start(env.axi_system_env.master[e_apu_init_lt].sequencer);
    //if (axi_mst_seq.ex_wr_transaction.get_response_status() != svt_axi_transaction::OKAY)
    //  `uvm_fatal(get_type_name(), "4: I1 ExWR old failed with RESP: OKAY");
    
    // Random delay
    repeat($urandom_range(0,10)) @(posedge tb_intf.enoc_clk); 
    //phase.phase_done.set_drain_time(this, 3ms);
    phase.drop_objection(this);
    `uvm_info ("enoc_exclusives_test", "Objection dropped", UVM_LOW)
  endtask : run_phase
  
  
endclass:enoc_exclusives_test

`endif

