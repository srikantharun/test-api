// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //

`ifndef GUARD_PIPELINE_BASE_TEST_SV
`define GUARD_PIPELINE_BASE_TEST_SV

`define DELAY_AFTER_INIT 0

class pipeline_base_test extends common_seq_lib_base_test;

  axi_master_write_random_sequence  axi_write_pipeline_csl_seq[int];
  axi_master_read_random_sequence  axi_read_pipeline_csl_seq[int];

  bit [7 : 0] graph_ddr_buff[bit[`AXI_HP_ADDR_WIDTH-1 : 0]];
  bit [7 : 0] pp_ddr_buff[bit[`AXI_HP_ADDR_WIDTH-1 : 0]];
  bit [7 : 0] l2_buff[bit[`AXI_HP_ADDR_WIDTH-1 : 0]];
  
  bit [`AXI_HP_ADDR_WIDTH -1 : 0]  axi_l2_addr;
  bit [`AXI_HP_ADDR_WIDTH -1 : 0]  axi_ddr_addr;
  bit [`AXI_HP_ADDR_WIDTH -1 : 0]  axi_g_ddr_addr;
  bit [`AXI_HP_DATA_WIDTH -1 : 0]  data;
  bit [`AXI_HP_DATA_WIDTH -1 : 0]  wr_data[int];

  //bit [`AXI_HP_ADDR_WIDTH -1 : 0]  graph_lpddr_lb_addr, pp_lpddr_lb_addr, l2_lb_addr, graph_lpddr_hb_addr, pp_lpddr_hb_addr, l2_hb_addr;
  bit pp_ddr_buff_updated, graph_ddr_buff_updated;

  // Registration with the factory
  `uvm_component_utils(pipeline_base_test)

  // Class constructor
  function new (string name="pipeline_base_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("pipeline_base_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    for (int init=0; init < 5; init++) begin
      axi_write_pipeline_csl_seq[init]  = axi_master_write_random_sequence::type_id::create($sformatf("axi_write_pipeline_csl_seq[%0d]", init));
      axi_read_pipeline_csl_seq[init]  = axi_master_read_random_sequence::type_id::create($sformatf("axi_read_pipeline_csl_seq[%0d]", init));
    end
  endfunction : build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info ("pipeline_base_test", "Objection raised", UVM_HIGH)
    phase.raise_objection(this);

// 1. PCIe write to PP LPDDR
// 2. DEC read then write from PP LPDDR
// 3. PVE read from PP LPDDR -> PVE write to both DDRs
// 4. SDMA read from GRAPH LPDDR and write to L2
// 5. AICORE read and write to L2
// 6. either AICORE or DMA read from L2 and write to both DDRs
// 7. PVE read from either DDR (which ever is ready) and write to both DDRs
// 8. PCIe read from either DDR (which ever is ready)

    for (int i = 0; i < 64; i++)
      data[(i+1)*8-1 -: 8]  = i;
    wr_data[0] = data;
    for (int iter=1; iter < 500; iter++) begin
      assert(randomize(data));
      wr_data[iter] = data;
    end    

foreach(wr_data[i]) begin
    assert(randomize(axi_ddr_addr) with {
                     axi_ddr_addr inside {[`PP_DDR_BASE_ADDR : `PP_DDR_END_ADDR]};
                     axi_ddr_addr[5:0] == 0; // 512 bit aligned
          });
    assert(randomize(axi_g_ddr_addr) with {
                     axi_g_ddr_addr inside {[`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]};
                     axi_g_ddr_addr[5:0] == 0; // 512 bit aligned
          });
    assert(randomize(axi_l2_addr) with {
                     axi_l2_addr inside {[`L2_BASE_ADDR : `L2_END_ADDR]};
                     axi_l2_addr[5:0] == 0; // 512 bit aligned
          });
// TODO: for each part of sequence add ifdef for initiator 
// 1. PCIe write to PP LPDDR
   `uvm_info(get_name,"Step 1. PCIe write to PP LPDDR", UVM_LOW)
   write_seq(PCIE, wr_data[i], axi_ddr_addr, pp_ddr_buff);

// 2. DEC read then write from PP LPDDR

   `uvm_info(get_name,"Step 2. DEC read then write from PP LPDDR", UVM_LOW)
   read_seq (DEC, axi_ddr_addr, pp_ddr_buff);

   //assert(randomize(wr_data));
   wr_data[i] = get_buff_data(axi_ddr_addr, pp_ddr_buff);
   wr_data[i] = wr_data[i] << 8;

   write_seq(DEC, wr_data[i], axi_ddr_addr, pp_ddr_buff);

// 3. PVE read from PP LPDDR -> PVE write to both DDRs
   `uvm_info(get_name,"Step 3. PVE read from PP LPDDR -> PVE write to both DDRs", UVM_LOW)
   read_seq (PVE, axi_ddr_addr, pp_ddr_buff);

   //assert(randomize(wr_data[i]));
   wr_data[i] = get_buff_data(axi_ddr_addr, pp_ddr_buff);
   wr_data[i] = wr_data[i] << 8;

   write_seq(PVE, wr_data[i], axi_ddr_addr, pp_ddr_buff);
   write_seq(PVE, wr_data[i], axi_g_ddr_addr, graph_ddr_buff);

// 4. SDMA read from GRAPH LPDDR and write to L2
   `uvm_info(get_name,"Step 4. SDMA read from GRAPH LPDDR and write to L2", UVM_LOW)
   read_seq (SDMA, axi_g_ddr_addr, graph_ddr_buff);
   wr_data[i] = get_buff_data(axi_g_ddr_addr, graph_ddr_buff);
   write_seq(SDMA, wr_data[i], axi_l2_addr, l2_buff);

// 5. AICORE read and write to L2
   `uvm_info(get_name,"Step 5. AICORE read and write to L2", UVM_LOW)
   read_seq(AIC, axi_l2_addr, l2_buff);
   //assert(randomize(wr_data[i]));
   wr_data[i] = get_buff_data(axi_l2_addr, l2_buff);
   wr_data[i] = wr_data[i] << 8;
   write_seq(AIC, wr_data[i], axi_l2_addr, l2_buff);

// 6. either AICORE or DMA read from L2 and write to both DDRs
   `uvm_info(get_name,"Step 6. either AICORE or DMA read from L2 and write to both DDRs", UVM_LOW)
    // we need to wait for AIC to get completion for previous write before we read from L2

    randcase
      1:  begin
            `uvm_info(get_name,"Step 6.a AICORE read from L2", UVM_LOW)
            read_seq(AIC, axi_l2_addr, l2_buff);
            `uvm_info(get_name,"Step 6.a AICORE read from L2 done", UVM_LOW)
          end 
      1:  begin
            `uvm_info(get_name,"Step 6.a DMA read from L2", UVM_LOW)
            read_seq(SDMA, axi_l2_addr, l2_buff);
            `uvm_info(get_name,"Step 6.a DMA read from L2 done", UVM_LOW)
          end
    endcase

    wr_data[i] = get_buff_data(axi_l2_addr, l2_buff);

    randcase
      1 : begin
            fork
              begin
                `uvm_info(get_name,"Step 6.b AIC write to PP DDR", UVM_LOW)
                write_seq(AIC, wr_data[i], axi_ddr_addr, pp_ddr_buff);
                pp_ddr_buff_updated = 1;
                `uvm_info(get_name,"Step 6.b AIC write to PP DDR done", UVM_LOW)
              end
              begin
                `uvm_info(get_name,"Step 6.b DMA write to GRAPH DDR", UVM_LOW)
                write_seq(SDMA, wr_data[i], axi_g_ddr_addr, graph_ddr_buff);
                graph_ddr_buff_updated = 1;
                `uvm_info(get_name,"Step 6.b DMA write to GRAPH DDR done", UVM_LOW)
              end
            join_any
          end
        1 : begin
              fork
                begin
                  `uvm_info(get_name,"Step 6.b DMA write to PP DDR", UVM_LOW)
                  write_seq(SDMA, wr_data[i], axi_ddr_addr, pp_ddr_buff);
                  pp_ddr_buff_updated = 1;
                  `uvm_info(get_name,"Step 6.b DMA write to PP DDR done", UVM_LOW)
                end
                begin
                  `uvm_info(get_name,"Step 6.b AIC write to GRAPH DDR", UVM_LOW)
                  write_seq(AIC, wr_data[i], axi_g_ddr_addr, graph_ddr_buff);
                  graph_ddr_buff_updated = 1;
                  `uvm_info(get_name,"Step 6.b AIC write to GRAPH DDR done", UVM_LOW)
                end
              join_any
            end
    endcase

// 7. PVE read from either DDR (which ever is ready) and write to both DDRs
// 8. PCIe read from either DDR (which ever is ready)
   `uvm_info(get_name,"Step 7. PVE read from either DDR (which ever is ready) and write to both DDRs", UVM_LOW)
    randcase
      pp_ddr_buff_updated : 
          begin
            read_seq(PVE, axi_ddr_addr, pp_ddr_buff);

            //assert(randomize(wr_data[i]));
            wr_data[i] = get_buff_data(axi_ddr_addr, pp_ddr_buff);
            wr_data[i] = wr_data[i] << 8;

            write_seq(PVE, wr_data[i], axi_ddr_addr, pp_ddr_buff);
            fork
              begin
                wait(graph_ddr_buff_updated == 1);// check if other DDR sequence is finished in previous step
                write_seq(PVE, wr_data[i], axi_g_ddr_addr, graph_ddr_buff);
              end
              begin
                `uvm_info(get_name,"Step 8. PCIe read from either DDR (which ever is ready)", UVM_LOW)
                read_seq(PCIE, axi_ddr_addr, pp_ddr_buff);
              end
            join
          end
      graph_ddr_buff_updated : 
          begin
            read_seq(PVE, axi_g_ddr_addr, graph_ddr_buff);

            //assert(randomize(wr_data[i]));
            wr_data[i] = get_buff_data(axi_g_ddr_addr, graph_ddr_buff);
            wr_data[i] = wr_data[i] << 8;

            write_seq(PVE, wr_data[i], axi_g_ddr_addr, graph_ddr_buff);
            fork
              begin
                wait(pp_ddr_buff_updated == 1);// check if other DDR sequence is finished in previous step
                write_seq(PVE, wr_data[i], axi_ddr_addr, pp_ddr_buff);
              end
              begin
                `uvm_info(get_name,"Step 8. PCIe read from either DDR (which ever is ready)", UVM_LOW)
                read_seq(PCIE, axi_g_ddr_addr, graph_ddr_buff);
              end
            join
          end
    endcase
    graph_ddr_buff_updated = 0;
    pp_ddr_buff_updated = 0;
end // foreach
    #100ns;
    phase.drop_objection(this);
    `uvm_info ("pipeline_base_test", "Objection dropped", UVM_HIGH)

  endtask : run_phase
task read_seq (init_t init, bit[`AXI_HP_ADDR_WIDTH-1 : 0] axi_addr, ref bit[7:0] buffer[bit[`AXI_HP_ADDR_WIDTH-1 : 0]]);
  burst_size_t burst_sz;
  bit [`AXI_HP_DATA_WIDTH -1 : 0] axi_data;
  int burst_len, n_bytes, start_byte, end_byte, tot_bytes;
  bit[7:0] read_data_buff[bit[`AXI_HP_ADDR_WIDTH-1 : 0]];

  case (axi_addr) inside
    [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]  : `uvm_info(get_name, $sformatf("%s read from GRAPH DDR", init), UVM_LOW)
    [`PP_DDR_BASE_ADDR    : `PP_DDR_END_ADDR]     : `uvm_info(get_name, $sformatf("%s read from PP DDR", init), UVM_LOW)
    [`L2_BASE_ADDR        : `L2_END_ADDR]         : `uvm_info(get_name, $sformatf("%s read from L2", init), UVM_LOW)
    default : `uvm_error(get_name, "wrong address range")
  endcase

  case(init)
    PCIE,
    DEC:  begin
            burst_sz = BURST_SIZE_128BIT;
            burst_len = 4;
          end
    PVE,
    SDMA,
    AIC:  begin
            burst_sz = BURST_SIZE_512BIT;
            burst_len = 1;
          end
  endcase

  n_bytes = (1<<burst_sz);

  fork
    begin // read request
      axi_read_pipeline_csl_seq[init].randomize() with {
         sequence_length == 1;
         cfg_addr        == axi_addr;
         burst_size      == burst_sz;
         burst_type      == INCR;
         delay           == 0;
         burst_length    == burst_len;
       };
      axi_read_pipeline_csl_seq[init].response_received[0] = 0; // reset first in case last call of the sequence left this field set
      //axi_read_pipeline_csl_seq[init].start(env.axi_system_env.master[init].sequencer);
      axi_read_pipeline_csl_seq[init].start(env.axi_system_env.master[0].sequencer);
    end
    begin // wait for response, check data match what we have in buffer
      `uvm_info(get_name,$sformatf("%s waiting for read response", init), UVM_LOW)
      wait(axi_read_pipeline_csl_seq[init].response_received[0]); 
      `uvm_info(get_name,$sformatf("%s received read response", init), UVM_LOW)
      if (axi_read_pipeline_csl_seq[init].rsp.get_response_status() == svt_axi_transaction::OKAY) begin

        start_byte = axi_addr - (axi_addr >> BURST_SIZE_512BIT << BURST_SIZE_512BIT); // full band alligned address 
        end_byte   = (start_byte + n_bytes) / n_bytes * n_bytes;
        tot_bytes = 0;

        foreach (axi_read_pipeline_csl_seq[init].rsp.data[i]) begin
          for (int nb=start_byte; nb < end_byte; nb++) begin
            read_data_buff[axi_addr+tot_bytes] = axi_read_pipeline_csl_seq[init].rsp.data[i][((nb + 1)*8-1) -: 8];
            tot_bytes++;
          end
          start_byte = end_byte % (1 << BURST_SIZE_512BIT);
          end_byte   = (start_byte + n_bytes) / n_bytes * n_bytes;
        end
        foreach (read_data_buff[i])
          `uvm_info(get_name,$sformatf("read_data_buff[%0h] = %0h", i, read_data_buff[i]), UVM_DEBUG);
      end else begin
        `uvm_error("Test: read_seq", "Error reponse received!");
      end
      foreach (read_data_buff[i])
        if (read_data_buff[i] != buffer[i]) begin
          `uvm_info("Test: read_seq",$sformatf("Data mismatch! Read (byte)address: %0h, Read data: %0h, Expect data: %0h", i, read_data_buff[i], buffer[i]), UVM_LOW);
          `uvm_error("Test: read_seq","Data mismatch!");
        end
    end
  join
endtask

task write_seq(init_t init, bit [`AXI_HP_DATA_WIDTH -1 : 0] wr_data, bit[`AXI_HP_ADDR_WIDTH-1 : 0] axi_addr, ref bit[7:0] buffer[bit[`AXI_HP_ADDR_WIDTH-1 : 0]]);
  burst_size_t burst_sz;
  bit [`AXI_HP_DATA_WIDTH -1 : 0] axi_data[];
  bit [`AXI_HP_DATA_WIDTH -1 : 0] data_reordered;
  int burst_len, byte_offset, end_byte;

  case (axi_addr) inside
    [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR] : `uvm_info(get_full_name(), $sformatf("%s write to GRAPH DDR", init), UVM_LOW)
    [`PP_DDR_BASE_ADDR : `PP_DDR_END_ADDR]       : `uvm_info(get_full_name(), $sformatf("%s write to PP DDR", init), UVM_LOW)
    [`L2_BASE_ADDR : `L2_END_ADDR]               : `uvm_info(get_full_name(), $sformatf("%s write to L2", init), UVM_LOW)
    default : `uvm_error(get_full_name(), "wrong address range")
  endcase

  case(init)
    PCIE,
    DEC:  begin
            burst_sz = BURST_SIZE_128BIT;
            burst_len = 4; 
          end
    PVE,
    SDMA,
    AIC:  begin
            burst_sz = BURST_SIZE_512BIT;
            burst_len = 1;
          end
  endcase

  byte_offset = axi_addr - (axi_addr >> BURST_SIZE_512BIT << BURST_SIZE_512BIT); // full band alligned address
  data_reordered = wr_data << byte_offset*8 | wr_data >> (512 - byte_offset*8);
  end_byte = 64 - byte_offset % (1 << burst_sz);

  `uvm_info("write_seq", $sformatf("Send write sequence with burst size: %s, burst_len: %0d", burst_sz, burst_len), UVM_LOW)
  `uvm_info("write_seq", $sformatf("Send write sequence with data = %0h", wr_data), UVM_LOW)
  `uvm_info("write_seq", $sformatf("Send write sequence with data reordered = %0h", data_reordered), UVM_LOW)

  axi_write_pipeline_csl_seq[init].randomize() with {
    sequence_length == 1;
    cfg_addr        == axi_addr;
    burst_size      == burst_sz;
    burst_type      == INCR;
    delay           == 0;
    burst_length    == burst_len;
    foreach (cfg_data[i])
      cfg_data[i]   == data_reordered;
  };
  //axi_write_pipeline_csl_seq[init].start(env.axi_system_env.master[init].sequencer);
  axi_write_pipeline_csl_seq[init].start(env.axi_system_env.master[0].sequencer);

  // save written data to a buffer
  for (int nb=0; nb < end_byte ; nb++) 
    buffer[axi_addr+nb] = wr_data[((nb + 1)*8-1) -: 8];

  foreach(buffer[i])
    `uvm_info("Test: write_seq",$sformatf("write_buff_data[%0h] = %0h", i, buffer[i]), UVM_DEBUG);

endtask

virtual task init_data();
 `uvm_info("Test", "SKIP Init data.", UVM_LOW) 
endtask : init_data

virtual task check_read_data_against_init();
 `uvm_info("Test", "SKIP checking read data against init data.", UVM_LOW) 
endtask : check_read_data_against_init

function bit [`AXI_HP_DATA_WIDTH -1 : 0] get_buff_data(input bit[`AXI_HP_ADDR_WIDTH-1 : 0] addr, input bit[7:0] buffer[bit[`AXI_HP_ADDR_WIDTH-1 : 0]]);
   bit [`AXI_HP_DATA_WIDTH -1 : 0] data;
   data = 0;
   for (int i=0; i<64; i++)
     data[((i+1)*8-1) -: 8] = buffer[addr+i];
   return data;
endfunction : get_buff_data

endclass:pipeline_base_test

`endif //GUARD_PIPELINE_BASE_TEST_SV
