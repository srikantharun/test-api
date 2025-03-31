// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef GUARD_COMMON_SEQ_LIB_DMA_TEST_SV
`define GUARD_COMMON_SEQ_LIB_DMA_TEST_SV


class common_seq_lib_dma_test extends common_seq_lib_base_test;
  // Registration with the factory
  `uvm_component_utils(common_seq_lib_dma_test)
  bit [`AXI_HP_ADDR_WIDTH-1:0]    dst_addr, src_addr;
  bit [`AXI_HP_DATA_WIDTH -1 : 0] data[int];

  // Class constructor
  function new (string name="common_seq_lib_dma_test", uvm_component parent);
    super.new (name, parent);
    //axi_seq           = axi_master_sequence::type_id::create("axi_seq");
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("common_seq_lib_dma_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("common_seq_lib_dma_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

    //==================//
    // run DMA sequence //
    //==================//


    base_test_cfg.SRC_ADDR = 40'h0;
    base_test_cfg.DST_ADDR = 40'h8000;
    base_test_cfg.BW = BW_full;
    base_test_cfg.DATA_BSIZE = 8*SIZE_1K;
    base_test_cfg.INITIATOR = SDMA;

    dma_read();
    dma_write();

#3000;

    base_test_cfg.SRC_ADDR = 40'h2040;
    base_test_cfg.DST_ADDR = 40'h8000;
    base_test_cfg.BW = BW_half;
    base_test_cfg.DATA_BSIZE = 8*SIZE_1K;
    base_test_cfg.INITIATOR = SDMA;

    dma_read();
    dma_write();

#3000;

    base_test_cfg.SRC_ADDR = 40'h8000;
    base_test_cfg.DST_ADDR = 40'h10000;
    base_test_cfg.BW = BW_full;
    base_test_cfg.DATA_BSIZE = 8*SIZE_1K;
    base_test_cfg.INITIATOR = SDMA;
    dma_move();

/*
VERSION II - start sequence using tasks and setting inputs
    src_addr = 40'h0;
    dst_addr = 40'h8000;

    dma_read(SDMA, src_addr, 8*SIZE_1K, BW_full, data);
    `uvm_info ("common_seq_lib_dma_test", $sformatf("data size is %0d", data.size()), UVM_LOW)
    foreach (data[i])
      `uvm_info ("common_seq_lib_dma_test", $sformatf("data[%0d] = %0h", i, data[i]), UVM_LOW)

    dma_write(SDMA, dst_addr, 8*SIZE_1K, BW_full, data);

#3000;
    src_addr = 40'h2040;
    dst_addr = 40'h8000;
    dma_read(SDMA, src_addr, 8*SIZE_1K, BW_half, data);
    `uvm_info ("common_seq_lib_dma_test", $sformatf("data size is %0d", data.size()), UVM_LOW)
    foreach (data[i])
      `uvm_info ("common_seq_lib_dma_test", $sformatf("data[%0d] = %0h", i, data[i]), UVM_LOW)

    dma_write(SDMA, dst_addr, 8*SIZE_1K, BW_half, data);
#3000;
    src_addr = 40'h8000;
    dst_addr = 40'h10000;
    dma_move(SDMA, src_addr, dst_addr, 8*SIZE_1K, BW_full);

// VERSION I - start sequence from user test
    axi_dma_seq.randomize() with {
      src_addr    == local::src_addr;
      dst_addr    == local::dst_addr;
      size        == 8192; 
      bandwidth   == BURST_SIZE_512BIT;
      delay       == 0; 
    };
    foreach (env.axi_system_env.master[i])
      axi_dma_seq.start(env.axi_system_env.master[i].sequencer);
*/
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("common_seq_lib_dma_test", "Objection dropped", UVM_HIGH)

  endtask : run_phase

endclass:common_seq_lib_dma_test

`endif //GUARD_COMMON_SEQ_LIB_DMA_TEST_SV
