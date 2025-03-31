

  task `BASE_TEST::check_read_data_against_init();
    `uvm_info("common_seq_lib_base_test", "Init data check.", UVM_LOW)
    fork
      begin
      axi_rd_rand_seq.randomize() with {
        sequence_length     == 'd3;
        cfg_addr            == 'h0;
        delay               == 0;
        burst_size          == BURST_SIZE_512BIT;
        burst_length        == 64; // Read 4KB of data
      };
      foreach (env.axi_system_env.master[i])
        axi_rd_rand_seq.start(env.axi_system_env.master[i].sequencer);
      end
      begin
        for (int rsp_cnt = 0; rsp_cnt < 3; rsp_cnt++) begin
          `uvm_info("init_data: wait response", $sformatf("AXI READ wait for response #%0d!", rsp_cnt+1), UVM_LOW);
          wait(axi_rd_rand_seq.response_received[rsp_cnt] == 1);
          foreach (axi_rd_rand_seq.rsp.data[i]) begin
            if (axi_rd_rand_seq.rsp.data[i] != axi_rd_rand_seq.rsp.addr / 64 + i / (1 << (6-axi_rd_rand_seq.rsp.burst_size)))
              `uvm_error(get_name,$sformatf("Data mismatch! Addr: %0h, Burst_size: %0h Read data: %0h, Init data: %0h",axi_rd_rand_seq.rsp.addr, axi_rd_rand_seq.rsp.burst_size, axi_rd_rand_seq.rsp.data[i], axi_rd_rand_seq.rsp.addr / 64 + i / (1 << (6-axi_rd_rand_seq.rsp.burst_size))))
            else
              `uvm_info(get_name,$sformatf("Data match! Addr: %0h, Burst_size: %0h Read data: %0h",axi_rd_rand_seq.rsp.addr, axi_rd_rand_seq.rsp.burst_size, axi_rd_rand_seq.rsp.data[i]), UVM_DEBUG)
          end
          `uvm_info("init_data: wait response", $sformatf("AXI READ response #%0d received!", rsp_cnt+1), UVM_LOW);
        end // for rsp_cnt
      end
    join
    `uvm_info("common_seq_lib_base_test", "Init data check done.", UVM_LOW)
  endtask : check_read_data_against_init

  task `BASE_TEST::init_data();
    bit [`AXI_HP_DATA_WIDTH-1:0]      wr_data[];
    `uvm_info("common_seq_lib_base_test", "Init data.", UVM_LOW)
    // Init 12K of data in slave memory
    wr_data = new[192];
    for (int i = 0; i < 192; i++)
      wr_data[i]  = i;
    axi_wr_rand_seq.randomize() with {
      sequence_length     == 'd3;
      cfg_addr            == 'h0;
      delay               == 0;
      burst_size          == BURST_SIZE_512BIT;
      burst_length        == 64; // Fill in 4KB of data
      foreach (wr_data[i])
        cfg_data[i] == wr_data[i];
    };

    foreach (env.axi_system_env.master[i])
      axi_wr_rand_seq.start(env.axi_system_env.master[i].sequencer);
    `uvm_info("common_seq_lib_base_test", "Init data done.", UVM_LOW)
  endtask : init_data

  //===============================================================//
  // dma_read task - create and run axi sequence
  //                 with given iputs
  //  init      - initiator(provide master number for DMA)
  //  axi_addr  - source address
  //  Bsize     - posible values SIZE_32B, SIZE_64B,
  //              SIZE_128B, SIZE_256B, SIZE_512B, SIZE_1K
  //              SIZE_1M or multiples of it e.g. 2*SIZE_1K
  //  bandwidth - we can set bandwidth to following values
  //              BW_full, BW_half, BW_quarter2, BW_8th, BW_16th
  //  axi_data  - output, response data will be put here
  //===============================================================//


  //task dma_read(init_t init,
  //              bit [`AXI_HP_ADDR_WIDTH : 0] axi_addr,
  //              int Bsize,
  //              bw_t bandwidth=BW_full,
  //              ref bit [`AXI_HP_DATA_WIDTH -1 : 0] axi_data[int]);

  task `BASE_TEST::dma_read();

    init_t init;
    bit [`AXI_HP_ADDR_WIDTH : 0] axi_addr;
    int Bsize;
    bw_t bandwidth=BW_full;
    bit [`AXI_HP_DATA_WIDTH -1 : 0] axi_data[int];
    burst_size_t burst_sz, max_bw;
    int burst_len, n_bytes, start_byte, end_byte, tot_bytes=0, rd_rsp_cnt, tot_len=0;
    bit[7:0] read_data_buff[bit[`AXI_HP_ADDR_WIDTH-1 : 0]];

    if (!uvm_config_db#(test_cfg)::get(this, "*", "base_test_cfg", base_test_cfg))
      `uvm_error("CONFIG_ERROR", "Failed to get base_test_cfg from configuration database")

    init = base_test_cfg.INITIATOR;
    axi_addr = base_test_cfg.SRC_ADDR;
    Bsize = base_test_cfg.DATA_BSIZE;
    bandwidth = base_test_cfg.BW;
    `uvm_info("DMA_RD", $sformatf("START DMA_RD with following inputs: init=%s, src_addr = %0h, amount of data = %0d, bandwidth = %s",init, axi_addr, Bsize ,bandwidth), UVM_LOW);

    case (axi_addr) inside
      [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]  : `uvm_info(get_name, $sformatf("%s read from GRAPH DDR", init), UVM_LOW)
      [`PP_DDR_BASE_ADDR    : `PP_DDR_END_ADDR]     : `uvm_info(get_name, $sformatf("%s read from PP DDR", init), UVM_LOW)
      [`L2_BASE_ADDR        : `L2_END_ADDR]         : `uvm_info(get_name, $sformatf("%s read from L2", init), UVM_LOW)
      default : `uvm_error(get_name, "wrong address range")
    endcase

    max_bw = BURST_SIZE_512BIT;
    burst_sz = BURST_SIZE_512BIT - bandwidth;

    `uvm_info("axi_dma_read_sequence:", "Entered", UVM_LOW)

    `uvm_info("axi_dma_read_sequence:",$sformatf("size in bytes: %0h, bandwidth: %s, burst_size: %0h, src_addr: %0h", Bsize, bandwidth, burst_sz, axi_addr), UVM_LOW)
    n_bytes = 1 << burst_sz;
    tot_bytes = 0;

    fork : dma_seq
    begin
      assert(axi_dma_rd_seq.randomize() with {
          cfg_addr        == axi_addr;
          delay           == 0;
          burst_size      == burst_sz;
          size            == Bsize;
        });

      `ifdef CSL_TB 
        axi_dma_rd_seq.start(env.axi_system_env.master[0].sequencer);
      `else
        axi_dma_rd_seq.start(env.axi_system_env.master[init].sequencer);
      `endif
      `uvm_info("axi_dma_read_sequence:",$sformatf("Read request sequence finished!"), UVM_LOW)
    end
    begin
      while (tot_bytes < Bsize) begin
        @axi_dma_rd_seq.response_received[rd_rsp_cnt]; // FIXME: check ID
        if (axi_dma_rd_seq.rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          start_byte = axi_addr - (axi_addr >> max_bw << max_bw); // full band alligned address 
          end_byte   = (start_byte + n_bytes) / n_bytes * n_bytes;
          `uvm_info("axi_dma_read_sequence:",$sformatf("start_byte: %0h, end_byte: %h, tot_bytes: %0h", start_byte, end_byte, tot_bytes), UVM_DEBUG)
          foreach (axi_dma_rd_seq.rsp.data[i]) begin
            for (int nb=start_byte; nb < end_byte; nb++) begin
              read_data_buff[axi_addr+tot_bytes] = axi_dma_rd_seq.rsp.data[i][((nb + 1)*8-1) -: 8];
              tot_bytes++;
            end
            start_byte = end_byte % (1 << max_bw);
            end_byte   = (start_byte + n_bytes) / n_bytes * n_bytes;
            axi_data[tot_len] = axi_dma_rd_seq.rsp.data[i];
            `uvm_info("axi_dma_read_sequence:",$sformatf("read_data[%0d] = %h",tot_len, axi_data[tot_len]), UVM_DEBUG)
            tot_len++;
          end
          foreach (read_data_buff[i])
            `uvm_info("axi_dma_read_sequence:",$sformatf("read_data_buff[%0h] = %0h", i, read_data_buff[i]), UVM_DEBUG)
        end else begin
          `uvm_error("axi_dma_read_sequence:", "Error reponse received!");
        end
        `uvm_info("axi_dma_read_sequence:",$sformatf("tot_bytes: %0h, byte size: %0h", tot_bytes, Bsize), UVM_DEBUG)
        rd_rsp_cnt++;
      end
      foreach(axi_dma_rd_seq.response_received[rd_rsp_cnt])
        axi_dma_rd_seq.response_received[rd_rsp_cnt] = 0;
      `uvm_info("axi_dma_read_sequence:",$sformatf("Wait for response finished!"), UVM_LOW)
    end
  join
  endtask

  //===============================================================//
  // dma_write task - run axi sequence with given iputs
  // 
  //  init      - initiator(provide master number for DMA)
  //  dst_addr  - destination address
  //  Bsize     - posible values SIZE_32B, SIZE_64B,
  //              SIZE_128B, SIZE_256B, SIZE_512B, SIZE_1K
  //              SIZE_1M or multiples of it e.g. 2*SIZE_1K
  //  bandwidth - we can set bandwidth to following values
  //              BW_full, BW_half, BW_quarter2, BW_8th, BW_16th
  //  data      - write data
  //===============================================================//


  //task dma_write(init_t init,
  //              bit [`AXI_HP_ADDR_WIDTH : 0] dst_addr,
  //              int Bsize,
  //              bw_t bandwidth=BW_full,
  //              ref bit [`AXI_HP_DATA_WIDTH -1 : 0] data[int]);

  task `BASE_TEST::dma_write();
    init_t init;
    bit [`AXI_HP_ADDR_WIDTH : 0] dst_addr;
    int Bsize;
    bw_t bandwidth=BW_full;
    bit [`AXI_HP_DATA_WIDTH -1 : 0] data[];

    burst_size_t burst_sz, max_bw;
    int delay=0;

    if (!uvm_config_db#(test_cfg)::get(this, "*", "base_test_cfg", base_test_cfg))
      `uvm_error("CONFIG_ERROR", "Failed to get base_test_cfg from configuration database")

    init = base_test_cfg.INITIATOR;
    dst_addr = base_test_cfg.DST_ADDR;
    Bsize = base_test_cfg.DATA_BSIZE;
    bandwidth = base_test_cfg.BW;
    `uvm_info("DMA_WR", $sformatf("START DMA_WR with following inputs: init=%s, dst_addr = %0h, amount of data = %0d, bandwidth = %s",init, dst_addr, Bsize ,bandwidth), UVM_LOW);

    case (dst_addr) inside
      [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]  : `uvm_info(get_name, $sformatf("%s write to GRAPH DDR", init), UVM_LOW)
      [`PP_DDR_BASE_ADDR    : `PP_DDR_END_ADDR]     : `uvm_info(get_name, $sformatf("%s write to PP DDR", init), UVM_LOW)
      [`L2_BASE_ADDR        : `L2_END_ADDR]         : `uvm_info(get_name, $sformatf("%s write to L2", init), UVM_LOW)
      default : `uvm_error(get_name, "wrong address range")
    endcase

    max_bw = BURST_SIZE_512BIT;
    burst_sz = BURST_SIZE_512BIT - bandwidth;

    //randomize data
    data = new[Bsize / (1 << burst_sz)];
    foreach(data[i])
      data[i] = {{$urandom}, {$urandom}, {$urandom}, {$urandom},
                 {$urandom}, {$urandom}, {$urandom}, {$urandom},
                 {$urandom}, {$urandom}, {$urandom}, {$urandom},
                 {$urandom}, {$urandom}, {$urandom}, {$urandom}};

    `uvm_info("DMA_WR:", "Entered", UVM_LOW)
    `uvm_info("DMA_WR:",$sformatf("size in bytes: %0h, data size: %0d, bandwidth: %s, burst_size: %0h, dst_addr: %0h", Bsize, data.size(), bandwidth, burst_sz, dst_addr), UVM_LOW)

    assert(axi_dma_wr_seq.randomize() with {
      cfg_addr        == dst_addr;
      delay           == delay;
      burst_size      == burst_sz;
      size            == Bsize;
      foreach (axi_data[i])
        axi_data[i]   == data[i];
    });
    `ifdef CSL_TB
      axi_dma_wr_seq.start(env.axi_system_env.master[0].sequencer);
    `else
      axi_dma_wr_seq.start(env.axi_system_env.master[init].sequencer);
    `endif

    `uvm_info("DMA_WR:", "Finished", UVM_LOW)
  endtask : dma_write

  //===============================================================//
  // dma_move task - run axi sequence with given iputs (read data
  //                 from s_addr and write data to d_addr)
  //  init      - initiator(provide master number for DMA)
  //  s_addr    - source address
  //  d_addr    - destination address
  //  Bsize     - posible values SIZE_32B, SIZE_64B,
  //              SIZE_128B, SIZE_256B, SIZE_512B, SIZE_1K
  //              SIZE_1M or multiples of it e.g. 2*SIZE_1K
  //  bandwidth - we can set bandwidth to following values
  //              BW_full, BW_half, BW_quarter2, BW_8th, BW_16th
  //===============================================================//

  //task dma_move(init_t init,
  //              bit [`AXI_HP_ADDR_WIDTH : 0] s_addr,
  //              bit [`AXI_HP_ADDR_WIDTH : 0] d_addr,
  //              size_t Bsize,
  //              bw_t bandwidth=BW_full);
  task `BASE_TEST::dma_move();

    init_t init;
    bit [`AXI_HP_ADDR_WIDTH : 0] s_addr;
    bit [`AXI_HP_ADDR_WIDTH : 0] d_addr;
    size_t Bsize;
    bw_t bandwidth=BW_full;

    burst_size_t burst_sz, max_bw;
    int delay=0;

    if (!uvm_config_db#(test_cfg)::get(this, "*", "base_test_cfg", base_test_cfg))
      `uvm_error("CONFIG_ERROR", "Failed to get base_test_cfg from configuration database")

    init = base_test_cfg.INITIATOR;
    d_addr = base_test_cfg.DST_ADDR;
    s_addr = base_test_cfg.SRC_ADDR;
    Bsize = base_test_cfg.DATA_BSIZE;
    bandwidth = base_test_cfg.BW;

    `uvm_info("DMA_MV", $sformatf("START DMA_MV with following inputs: init=%s, dst_addr = %0h, src_addr = %0h, amount of data = %0d, bandwidth = %s",init, d_addr, s_addr, Bsize ,bandwidth), UVM_LOW);

    case (s_addr) inside
      [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]  : `uvm_info(get_name, $sformatf("%s read_from GRAPH DDR", init), UVM_LOW)
      [`PP_DDR_BASE_ADDR    : `PP_DDR_END_ADDR]     : `uvm_info(get_name, $sformatf("%s read_from PP DDR", init), UVM_LOW)
      [`L2_BASE_ADDR        : `L2_END_ADDR]         : `uvm_info(get_name, $sformatf("%s read_from L2", init), UVM_LOW)
      default : `uvm_error(get_name, "wrong address range")
    endcase
 
    case (d_addr) inside
      [`GRAPH_DDR_BASE_ADDR : `GRAPH_DDR_END_ADDR]  : `uvm_info(get_name, $sformatf("%s write to GRAPH DDR", init), UVM_LOW)
      [`PP_DDR_BASE_ADDR    : `PP_DDR_END_ADDR]     : `uvm_info(get_name, $sformatf("%s write to PP DDR", init), UVM_LOW)
      [`L2_BASE_ADDR        : `L2_END_ADDR]         : `uvm_info(get_name, $sformatf("%s write to L2", init), UVM_LOW)
      default : `uvm_error(get_name, "wrong address range")
    endcase

    max_bw = BURST_SIZE_512BIT;
    burst_sz = BURST_SIZE_512BIT - bandwidth;

    `uvm_info("DMA_MV:", "Entered", UVM_LOW)
    `uvm_info("DMA_MV:",$sformatf("size in bytes: %0h, bandwidth: %s, burst_size: %0h, src_addr: %0h, dst_addr: %0h", Bsize, bandwidth, burst_sz, s_addr, d_addr), UVM_LOW)

    axi_dma_seq.randomize() with {
      src_addr    == s_addr;
      dst_addr    == d_addr;
      size        == Bsize; 
      burst_size  == burst_sz;
      delay       == 0; 
    };
    `ifdef CSL_TB
      axi_dma_seq.start(env.axi_system_env.master[0].sequencer);
    `else
      axi_dma_seq.start(env.axi_system_env.master[init].sequencer);
    `endif

    `uvm_info("DMA_MV:", "Finished!", UVM_LOW)
  endtask : dma_move


