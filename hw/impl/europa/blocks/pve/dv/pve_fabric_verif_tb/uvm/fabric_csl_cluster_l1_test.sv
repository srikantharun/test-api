//////////////////////////////////////////////////////////////
//  (C) Copyright Axelera AI 2024                           //
//  All Rights Reserved                                     //
//  Axelera AI Confidential                                 //
//  Owner : ana.stoisavljevic@axelera.ai                    //
//  Description: Send traffic from all clusters to all L1   //
//               memories in parallel.                      //
//               Following are sent in parallel:            //
//               Cl0 -> WR L0                               //
//               Cl1 -> RD L0                               //
//               Cl1 -> WR L1                               //
//               Cl2 -> RD L1                               //
//               ***                                        //
//               Cl6 -> WR L2                               //
//               Cl7 -> RD L2                               //
//               Cl7 -> WR L3                               //
//               Cl0 -> RD L3                               //
//////////////////////////////////////////////////////////////

`ifndef GUARD_FABRIC_CSL_CLUSTER_TO_L1_TEST_SV
`define GUARD_FABRIC_CSL_CLUSTER_TO_L1_TEST_SV

class fabric_csl_cluster_to_l1_test extends fabric_csl_base_test;
  // Registration with the factory
  `uvm_component_utils(fabric_csl_cluster_to_l1_test)
  bit [`AXI_LP_ADDR_WIDTH-1:0]    axi_addr[8];
  bit [`AXI_LP_DATA_WIDTH-1:0]    axi_write_data;
  svt_axi_transaction::burst_size_enum axi_burst_size;
  int max_data_width;

  axi_master_write_random_sequence    axi_wr_rand_p_seq[8];
  axi_master_read_random_sequence     axi_rd_rand_p_seq[8];
 
  // Class constructor
  function new (string name="fabric_csl_cluster_to_l1_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("fabric_csl_cluster_to_l1_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    for (int i =  init_cl0cpu0; i <= init_cl3cpu1; i++) begin
       axi_wr_rand_p_seq[i] = axi_master_write_random_sequence::type_id::create($sformatf("axi_wr_rand_p_seq[%0d]",i));
       axi_rd_rand_p_seq[i] = axi_master_read_random_sequence::type_id::create($sformatf("axi_rd_rand_p_seq[%0d]",i));
    end
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("fabric_csl_cluster_to_l1_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    axi_write_data             = 64'hDEAD_BEEF_FACE_CAFE;

    axi_burst_size = 3;
    max_data_width = 8; // 8 bytes

    axi_addr[0] = $urandom_range(`PVE_BASE + `L1_0_SA, `PVE_BASE + `L1_0_EA);
    axi_addr[1] = $urandom_range(`PVE_BASE + `L1_1_SA, `PVE_BASE + `L1_1_EA);
    axi_addr[2] = $urandom_range(`PVE_BASE + `L1_2_SA, `PVE_BASE + `L1_2_EA);
    axi_addr[3] = $urandom_range(`PVE_BASE + `L1_3_SA, `PVE_BASE + `L1_3_EA);
    axi_addr[4] = $urandom_range(`PVE_BASE + `L1_0_SA, `PVE_BASE + `L1_0_EA);
    axi_addr[5] = $urandom_range(`PVE_BASE + `L1_1_SA, `PVE_BASE + `L1_1_EA);
    axi_addr[6] = $urandom_range(`PVE_BASE + `L1_2_SA, `PVE_BASE + `L1_2_EA);
    axi_addr[7] = $urandom_range(`PVE_BASE + `L1_3_SA, `PVE_BASE + `L1_3_EA);

    foreach (axi_addr[i])
       if (axi_addr[i] % 4096 + (1<<axi_burst_size) > 4096)
         axi_addr[i] = axi_addr[i] / (1<<axi_burst_size) * (1<<axi_burst_size);

    for(int j = init_cl0cpu0; j <= init_cl3cpu1; j++) begin
      automatic int i;
      automatic int cl_nxt;
      i = j;
      cl_nxt = (i + 1) % 8;

      fork
        `uvm_info ("fabric_csl_cluster_to_l1_test", $sformatf("Send write sequence from cluster #%0d to L%0d",i, (i % 4)), UVM_LOW)
        axi_wr_rand_p_seq[i].randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr[i];
          cfg_data[0]     == {8{axi_write_data}};
          burst_size      == axi_burst_size;
          max_bw          == max_data_width;
          burst_type      == svt_axi_transaction::INCR;
        };
        axi_wr_rand_p_seq[i].start(env.axi_system_env.master[i].sequencer);
  
        `uvm_info ("fabric_csl_cluster_to_l1_test", $sformatf("Send read sequence from cluster #%0d to L%0d",cl_nxt, (i % 4)), UVM_LOW)
        axi_rd_rand_p_seq[cl_nxt].randomize() with {
          sequence_length == 'd1;
          cfg_addr        == axi_addr[i];
          burst_size      == axi_burst_size;
          burst_type      == svt_axi_transaction::INCR;
        };
        axi_rd_rand_p_seq[cl_nxt].start(env.axi_system_env.master[cl_nxt].sequencer);
      join_none
    end
    wait fork;

    for(int j = init_cl0cpu0; j <= init_cl3cpu1; j++) begin
        check_conn_matrix(axi_wr_rand_p_seq[j].response);
        check_conn_matrix(axi_rd_rand_p_seq[j].response);
    end

    #100ns;
    phase.drop_objection(this);
    `uvm_info ("fabric_csl_cluster_to_l1_test", "Objection dropped", UVM_HIGH)
  
  endtask : run_phase
  
endclass:fabric_csl_cluster_to_l1_test

`endif //GUARD_FABRIC_CSL_CLUSTER_TO_L1_TEST_SV

