// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Base testcase to check the DMA acceses
// Owner: Roswin Benny <roswin.benny@axelera.ai>

`ifndef __AI_CORE_DMA_BASE_TEST__
`define __AI_CORE_DMA_BASE_TEST__

class ai_core_dma_base_test extends ai_core_base_test;

  bit [`AXI_LP_ADDR_WIDTH-1:0]  axi_addr;
  bit [`AXI_LP_DATA_WIDTH-1:0]  axi_write_data;

  // AXI write and read sequences
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence  axi_rd_seq;

  // Class constructor
  extern function new (string name = "ai_core_dma_base_test", uvm_component parent);

  // Build phase
  extern virtual function void build_phase(uvm_phase phase);

  // Start of simulation phase
  extern virtual function void start_of_simulation_phase (uvm_phase phase);

  // Configure phase
  extern virtual task configure_phase (uvm_phase phase);

   // main phase
  extern virtual task main_phase (uvm_phase phase);


  // Run phase
  extern virtual task run_phase(uvm_phase phase);

  // Custom methods

  /*  Method to configure and perform a data transfer in the AI core DMA.
  *   Have to define source and destination addresses, as well as which master to use for each address.
  *   The channel to be used can also be selected with p_n_dma_channel; if not defined or set to zero,
  *   the method will search for a free channel in the DMA, or return an error if none is found.
  *   By default, the data transfer is exectuted; if p_b_data_transfer is set to zero, the method
  *   only configures the respective channel (or the free channel) with the source and destination info.
  */
  extern virtual task dmac_data_transfer( input bit [`AXI_LP_ADDR_WIDTH-1:0] p_source_addr                  ,
                                          input bit                          p_b_source_master      = 1'b0  ,
                                          input bit [`AXI_LP_ADDR_WIDTH-1:0] p_destination_addr             ,
                                          input bit                          p_b_destination_master = 1'b0  ,
                                          input int                          p_n_dma_channel        = 'd0   ,
                                          input bit                          p_b_data_transfer      = 1'b1  );

  extern virtual task stimulus_data_transfer( input string                       p_s_source_mem                 ,
                                              input bit [`AXI_LP_ADDR_WIDTH-1:0] p_source_addr                  ,
                                              input bit                          p_b_source_master      = 1'b0  ,
                                              input string                       p_s_destination_mem            ,
                                              input bit [`AXI_LP_ADDR_WIDTH-1:0] p_destination_addr             ,
                                              input bit                          p_b_destination_master = 1'b0  ,
                                              input int                          p_n_dma_channel        = 'd0   );

  
  // Registration with the factory
  `uvm_component_utils(ai_core_dma_base_test)

endclass : ai_core_dma_base_test

function ai_core_dma_base_test::new (string name="ai_core_dma_base_test", uvm_component parent);
  super.new (name, parent);
endfunction : new

function void ai_core_dma_base_test::build_phase(uvm_phase phase);
  `uvm_info (get_type_name(), "Build phase entered", UVM_HIGH)

  super.build_phase(phase);
  axi_wr_seq    = axi_master_write_sequence::type_id::create("axi_wr_seq");
  axi_rd_seq    = axi_master_read_sequence::type_id::create("axi_rd_seq");
endfunction : build_phase

function void ai_core_dma_base_test::start_of_simulation_phase (uvm_phase phase);
  super.start_of_simulation_phase(phase);
 endfunction: start_of_simulation_phase


task ai_core_dma_base_test::configure_phase (uvm_phase phase);
  super.configure_phase(phase);

  phase.raise_objection(this);

  `uvm_info (get_type_name(), "Setting DMA OSR and LEN to be 15", UVM_NONE)

  for(int ch = 1; ch <= `AI_CORE_DMA_NUM_CHANNELS; ch++) begin
    // Based on discussions at https://git.axelera.ai/ai-hw-team/triton/-/issues/1076
    // Set OSR to 15 for all DMA channels
    env.m_ral.write_reg (LP_DMA_REGMOD, 4'hF, $sformatf("ch%0d_cfg",ch), "src_osr_lmt");  // SRC_OSR_LMT
    env.m_ral.write_reg (LP_DMA_REGMOD, 4'hF, $sformatf("ch%0d_cfg",ch), "dst_osr_lmt");  // DST_OSR_LMT
    // Set LEN to 15
    env.m_ral.write_reg (LP_DMA_REGMOD, 1'b1, $sformatf("ch%0d_ctl",ch), "arlen_en" );
    env.m_ral.write_reg (LP_DMA_REGMOD, 'd15, $sformatf("ch%0d_ctl",ch), "arlen"    );
    env.m_ral.write_reg (LP_DMA_REGMOD, 1'b1, $sformatf("ch%0d_ctl",ch), "awlen_en" );
    env.m_ral.write_reg (LP_DMA_REGMOD, 'd15, $sformatf("ch%0d_ctl",ch), "awlen"    );
  end

  //Configuring the rv_plic
  env.m_ral.write_reg (RV_PLIC_REGMOD, 'h1, "prio15");
  env.m_ral.write_reg (RV_PLIC_REGMOD, 'h1, "prio16");

  phase.drop_objection(this);

endtask: configure_phase

task ai_core_dma_base_test::main_phase (uvm_phase phase);
  super.main_phase(phase);
endtask: main_phase

task ai_core_dma_base_test::run_phase(uvm_phase phase);
  super.run_phase(phase);
endtask : run_phase

// Programming Flow for Single Block Transfer
task ai_core_dma_base_test::dmac_data_transfer(
  input bit [`AXI_LP_ADDR_WIDTH-1:0] p_source_addr                  ,
  input bit                          p_b_source_master      = 1'b0  ,
  input bit [`AXI_LP_ADDR_WIDTH-1:0] p_destination_addr             ,
  input bit                          p_b_destination_master = 1'b0  ,
  input int                          p_n_dma_channel        = 'd0   ,
  input bit                          p_b_data_transfer      = 1'b1
);

  int free_chn_number;
  bit [63:0] ai_core_read_value;
  int block_ts_size;
  bit [2:0] tr_width;

  // Enable DMA and interrupts
  env.m_ral.write_reg (LP_DMA_REGMOD, 'h3, "dmac_cfgreg");
  env.regmodel.aic_rv_plic_regmod.ie0[0].write(status, 'h01_8000);                                //enabling interrupt 15 and 16
  `uvm_info(get_type_name(), $sformatf("Enabled DMAC"), UVM_LOW)

  /* Step 1: Software reads the DMAC Channel Enable Register (DMAC_ChEnReg) to choose a free (unused) channel. */
  env.m_ral.read_reg(.regblock_num(LP_DMA_REGMOD), .name("dmac_chenreg"), .data(ai_core_read_value));
  `uvm_info(get_type_name(), $sformatf("Read value from LP_DMA_REGMOD.dmac_chenreg = 'h%0h", ai_core_read_value), UVM_LOW)

  // If DMA channel is not defined (channel == 0), search for a free channel
  if(p_n_dma_channel == 'd0) begin
    for(int i = 0; i < `AI_CORE_DMA_NUM_CHANNELS; i++) begin
      if(ai_core_read_value[i] == 1'b0) begin
        free_chn_number = i+1;
        `uvm_info(get_type_name(), $sformatf("Channel %0d is free", free_chn_number), UVM_LOW)
        break;
      end
    end
    if(free_chn_number == 'd0) begin
      `uvm_error(get_type_name(), $sformatf("There is no free channel on the DMA"))
    end else begin
      `uvm_info(get_type_name(), $sformatf("Using channel = 'd%0d", free_chn_number), UVM_LOW)
    end
  end else begin // Else, use provided channel and check if it is free
    free_chn_number = p_n_dma_channel;
    if(ai_core_read_value[free_chn_number] == 1'b1) begin
      `uvm_error(get_type_name(), $sformatf("Channel %0d is already in use", free_chn_number))
    end else begin
      `uvm_info(get_type_name(), $sformatf("Using channel = 'd%0d", free_chn_number), UVM_LOW)
    end
  end

  /* Step 2: Software programs CHx_CFG register with multi-block type value of both source and destination peripheral to be 2'b00. */
  env.m_ral.write_reg (LP_DMA_REGMOD, 2'b00, $sformatf("ch%0d_cfg",free_chn_number), "src_multblk_type");  // SRC_MULTBLK_TYPE
  env.m_ral.write_reg (LP_DMA_REGMOD, 2'b00, $sformatf("ch%0d_cfg",free_chn_number), "dst_multblk_type");  // DST_MULTBLK_TYPE
  `uvm_info(get_type_name(), $sformatf("Write value to LP_DMA_REGMOD.ch%0d_cfg = 'h%0h", free_chn_number, 4'b0000), UVM_LOW)

  /* Step 3: Software programs CHx_SAR and/or CHx_DAR, CHx_BLOCK_TS and CHx_CTL registers with appropriate values for the block. */

  // Source address register
  env.m_ral.write_reg (LP_DMA_REGMOD, p_source_addr, $sformatf("ch%0d_sar",free_chn_number));
  `uvm_info(get_type_name(), $sformatf("Write value to LP_DMA_REGMOD.ch%0d_sar = 'h%0h", free_chn_number, p_source_addr), UVM_LOW)

  // Destination address register
  env.m_ral.write_reg (LP_DMA_REGMOD, p_destination_addr, $sformatf("ch%0d_dar",free_chn_number));
  `uvm_info(get_type_name(), $sformatf("Write value to LP_DMA_REGMOD.ch%0d_dar = 'h%0h", free_chn_number, p_destination_addr), UVM_LOW)

  // Block transfer size
  env.m_ral.write_reg (LP_DMA_REGMOD, 'd63, $sformatf("ch%0d_block_ts",free_chn_number)); //TODO : Randomise later, currently maxi value
  `uvm_info(get_type_name(), $sformatf("Write value to LP_DMA_REGMOD.ch%0d_block_ts = 'd63", free_chn_number), UVM_LOW)

  // Control register
  std::randomize(tr_width) with {
    (block_ts_size == 'd0   ) -> (tr_width == 3'b110);
    (block_ts_size == 'd1   ) -> (tr_width == 3'b101);
    (block_ts_size == 'd3   ) -> (tr_width == 3'b100);
    (block_ts_size == 'd7   ) -> (tr_width == 3'b011);
    (block_ts_size == 'd15  ) -> (tr_width == 3'b010);
    (block_ts_size == 'd31  ) -> (tr_width == 3'b001);
    (block_ts_size == 'd63  ) -> (tr_width == 3'b000);
  };
  // lp dma controller has only one master
  env.m_ral.write_reg (LP_DMA_REGMOD, p_b_source_master      , $sformatf("ch%0d_ctl",free_chn_number), "sms"         );  // SMS
  env.m_ral.write_reg (LP_DMA_REGMOD, p_b_destination_master , $sformatf("ch%0d_ctl",free_chn_number), "dms"         );  // DMS
  env.m_ral.write_reg (LP_DMA_REGMOD, tr_width               , $sformatf("ch%0d_ctl",free_chn_number), "src_tr_width");  // Source Transfer Width is 64 bits
  env.m_ral.write_reg (LP_DMA_REGMOD, tr_width               , $sformatf("ch%0d_ctl",free_chn_number), "dst_tr_width");  // Destination Transfer Width is 64 bits

  env.m_ral.read_reg(.regblock_num(LP_DMA_REGMOD), .name($sformatf("ch%0d_ctl",free_chn_number)), .data(ai_core_read_value));
  `uvm_info(get_type_name(), $sformatf("Read value from LP_DMA_REGMOD.ch%0d_ctl = 'h%0h", free_chn_number, ai_core_read_value), UVM_LOW)

  if(p_b_data_transfer == 1'b1) begin // by default, the data transfer is performed by the DMA
    /* Step 4: Software enables the channel by writing 1 to the appropriate bit location in DMAC_ChEnReg register. */
    env.m_ral.read_reg(.regblock_num(LP_DMA_REGMOD), .name("dmac_chenreg"), .data(ai_core_read_value));
    `uvm_info(get_type_name(), $sformatf("Read value from LP_DMA_REGMOD.dmac_chenreg = 'h%0h", ai_core_read_value), UVM_LOW)
    ai_core_read_value[free_chn_number - 1 + 8] = 1'b1; // chX_en_we
    ai_core_read_value[free_chn_number - 1]     = 1'b1; // chX_en
    env.m_ral.write_reg (LP_DMA_REGMOD, ai_core_read_value, "dmac_chenreg");
    env.m_ral.read_reg(.regblock_num(LP_DMA_REGMOD), .name("dmac_chenreg"), .data(ai_core_read_value));
    `uvm_info(get_type_name(), $sformatf("Read value from LP_DMA_REGMOD.dmac_chenreg = 'h%0h", ai_core_read_value), UVM_LOW)

    /* Step 5 */

    /* Step 6: Software waits for the block transfer completion interrupt/polls the block transfer completion
    indication bit (BLOCK_TFR_DONE) in CHx_IntStatusReg register till the bit is 1. */
    fork begin
      fork
        do begin
          env.m_ral.read_reg(.regblock_num(LP_DMA_REGMOD), .name("dmac_chenreg"), .data(ai_core_read_value));
          `uvm_info(get_type_name(),$sformatf("Pooling LP_DMA_REGMOD.dmac_chenreg = 'h%0h", ai_core_read_value),UVM_LOW)
        end while(ai_core_read_value[free_chn_number-1] != 'h0);
        begin
          #10000;
          `uvm_error(get_type_name(),$sformatf("Timeout in DMA"))
          $finish();
        end
      join_any
      disable fork;
    end join

    `uvm_info(get_type_name(),$sformatf("Finished data transfer for channel %0d", free_chn_number),UVM_LOW)

    // Disable DMA and interrupts
    env.m_ral.write_reg (LP_DMA_REGMOD, 'h0, "dmac_cfgreg");
    env.regmodel.aic_rv_plic_regmod.ie0[0].write(status, 'h00_0000); //disabling interrupt 15 and 16
    `uvm_info(get_type_name(), $sformatf("Disabled DMAC"), UVM_LOW)
  end

endtask : dmac_data_transfer

task ai_core_dma_base_test::stimulus_data_transfer(
  input string                       p_s_source_mem                 ,
  input bit [`AXI_LP_ADDR_WIDTH-1:0] p_source_addr                  ,
  input bit                          p_b_source_master      = 1'b0  ,
  input string                       p_s_destination_mem            ,
  input bit [`AXI_LP_ADDR_WIDTH-1:0] p_destination_addr             ,
  input bit                          p_b_destination_master = 1'b0  ,
  input int                          p_n_dma_channel        = 'd0
);


  dmac_data_transfer(p_source_addr, p_b_source_master, p_destination_addr, p_b_destination_master, p_n_dma_channel);
  //data integrity check is added in c test, because only cva6v can access L2,DDR,SYS SPM

endtask : stimulus_data_transfer


`endif	// __AI_CORE_DMA_BASE_TEST__
