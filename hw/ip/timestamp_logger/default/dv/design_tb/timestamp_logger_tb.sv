// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger TB
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`include "axi_intf.sv"

module timestamp_logger_tb;
  import tb_axi_pkg::*;

  localparam DW = 64;
  localparam AW = 40;
  localparam IDW = 4;
  localparam BW = 8;

  localparam NR_GROUPS = 4;
  localparam MEM_ST_ADDR = 'h4000;
  localparam MEM_DEPTH = 16;

  logic tb_clk;
  logic tb_rst_n;

  logic [NR_GROUPS-1:0] group_triggers;
  logic [NR_GROUPS-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] group_msgs;
  logic sync_start;

  axi_intf #(
    .DW (DW),
    .AW (AW),
    .IDW(IDW)
  ) axi_if ();

  axi_intf #(
    .DW (DW),
    .AW (AW),
    .IDW(IDW)
  ) axi_if_m ();

  assign axi_if.clk   = tb_clk;
  assign axi_if.rst_n = tb_rst_n;
  assign axi_if_m.clk   = tb_clk;
  assign axi_if_m.rst_n = tb_rst_n;

  axi_sl_driver #(
    .DW(DW),
    .AW(AW),
    .IDW(IDW)
  ) axi_s_drv = new(
    "SL_AXI", axi_if_m
  );

  axi_cmdblock_driver #(
    .DW(DW),
    .AW(AW),
    .IDW(IDW)
  ) tl_drv = new(
      "TL_AXI", axi_if
  );

  t_req wr_req, rd_req;

  // clock generation:
  initial begin
    tb_clk = 0;
    forever #((1.250) / 2) tb_clk = ~tb_clk;
  end

  // reset generation:
  initial begin
    tb_rst_n = 0;
    repeat (20) @(posedge tb_clk);
    #1;
    tb_rst_n = 1;
  end

  initial begin
    tl_drv.set_csr_base(0);  // csr
    tl_drv.set_id(2); // csr
    tl_drv.set_csr_base(MEM_ST_ADDR, .dev(1)); // mem
    tl_drv.set_id(3, .dev(1)); // mem

    $display("RUN!");
    fork
      tl_drv.run();
      axi_s_drv.run();
    join
    $display("RUN! Done");
  end


  // test:
  initial begin
    logic [AW-1:0] trace_st_addr, trace_size;
    logic [63:0] rd_data, exp;
    int time_stmp;
    time_stmp = 0;
    group_triggers = '0;
    group_msgs = '0;
    sync_start = 1'b0;

    wait (tb_rst_n);
    repeat (20) @(posedge tb_clk);

    //------------------------------------------------------------------------------------------------------
    //------------------------------------------- MEMORY ACCESS --------------------------------------------
    begin
      logic [63:0] exp_data[$];
      $display("Starting memory access test...");
      exp_data.push_back('headcafe << 32 | 'h2abe);
      exp_data.push_back('hbabeead << 32 | 'h1eef);
      exp_data.push_back('h5553111 << 32 | 'h3555);
      exp_data.push_back('h8888AAA << 32 | 'h1333);
      exp_data.push_back('h4567343 << 32 | 'h2343);
      exp_data.push_back('h2784272 << 32 | 'h3272);

      for (int i = 0; i < 6; i++) begin
        // miss-use csr function for writes towards the memory using the base override
        tl_drv.csr_wr(.reg_idx(i), .data(exp_data[i]), .dev(1));
      end

      // read back written data
      for (int i = 0; i < 6; i++) begin
        logic [63:0] rd_data, exp;
        // miss-use csr function for writes towards the memory using the base override
        tl_drv.csr_rd(.reg_idx(i), .data(rd_data), .dev(1));
        exp = exp_data.pop_front();
        if (exp != rd_data)
          $error("ERROR! Expected 0x%0h, but read 0x%0h on address 0x%0h @ %0t", exp, rd_data,
                 MEM_ST_ADDR + (i * 8), $time());
      end
    end
    //------------------------------------------------------------------------------------------------------

    begin
      $display("Starting basic trace test...");
      // while (tl_drv.is_busy()) @(posedge tb_clk);
      repeat (20) @(posedge tb_clk);
      trace_st_addr  = 'h1*8;
      trace_size = 'h5*8;

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ST_ADDR),
                            .data(trace_st_addr)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_LOG_SIZE),
                            .data(trace_size)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_BURST_SIZE),
                            .data('h1  /*burst per 2*/));

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_GROUP_EN_0_63),
                            .data(4'b0101));  // enable group 0 and 2

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                            .data('h0 | 1 << 0 /* enable */
                                      | 0 << 1 /* discard mode */
                                      | 0 << 2 /* local memory mode */
                                      | 0 << 4  /*cntr_division*/));

      // while (tl_drv.is_busy()) @(posedge tb_clk);
      repeat (40) @(posedge tb_clk);

      // init mem with zeros
      for (int i = 0; i < MEM_DEPTH; i++) begin
        // miss-use csr function for writes towards the memory using the base override
        tl_drv.csr_wr(.reg_idx(i), .data(0), .dev(1));
      end

    //   //------------------------------------------------------------------------------------------------------
    //   //--------------------------------------------    DROP   -----------------------------------------------
      repeat (4) @(posedge tb_clk);

      group_triggers = 'b0010;
      repeat (2) @(posedge tb_clk);
      group_triggers = 'b0000;
      repeat (8) @(posedge tb_clk);

      group_triggers = 'b0001;
      repeat (2) @(posedge tb_clk);
      group_triggers = 'b0000;
      repeat (8) @(posedge tb_clk);

      group_triggers = 'b1101;
      repeat (2) @(posedge tb_clk);
      group_triggers = 'b0000;
      repeat (18) @(posedge tb_clk);

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                            .data('h0 /* disable */));

      repeat (40) @(posedge tb_clk);

      $display("Checking... @ %0t", $time());
      begin
        logic [63:0] exp_data[$];
        exp_data.push_back('h2);
        exp_data.push_back('h3);
        exp_data.push_back('h2);
        exp_data.push_back('h1);
        exp_data.push_back('h3);
        exp_data.push_back('h0);  // should not be written at all
        exp_data.push_back('h0);  // should not be written at all

        // read back written data
        for (int i = 0; i < trace_size/8+2; i++) begin
          // miss-use csr function for writes towards the memory using the base override
          tl_drv.csr_rd(.reg_idx(i+(trace_st_addr/8)), .data(rd_data), .dev(1));
          exp = exp_data.pop_front();

          $display(" - entry %0d...", i);

          if (i >= (trace_size/8)) begin  // beyond end address, expect skipped (thus zero)
            if (0 != rd_data)
              $error("ERROR! Entry (0x%0h) found beyond end address! 0x%0h @ %0t", rd_data,
                    MEM_ST_ADDR + (i * 8), $time());
          end else begin
            if (time_stmp > (rd_data >> 32))
              $error(
                  "ERROR! Received timestamp (%0d) is not incremental compared to previous one (%0d)!",
                  rd_data >> 32, time_stmp);
            time_stmp = (rd_data >> 32);
            // if (exp != (rd_data & 'hFFFF))
            //   $error("ERROR! Expected triggers 0x%0h, but read 0x%0h on address 0x%0h @ %0t", exp,
            //          rd_data, MEM_ST_ADDR + (i * 8), $time());
          end
        end
      end
    end


    begin
      $display("Starting external mode test (eye-ball)...");
      trace_st_addr  = 'h400;
      trace_size = 'h400;

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ST_ADDR),
                            .data(trace_st_addr)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_LOG_SIZE),
                          .data(trace_size)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_BURST_SIZE),
                          .data('h1  /*burst per 2*/));

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                          .data('h0 | 1 << 0 /* enable */
                                    | 0 << 1 /* discard mode */
                                    | 1 << 2 /* external memory mode */
                                    | 0 << 4  /*cntr_division*/));
      repeat (4) @(posedge tb_clk);

      group_triggers = 'b0001;
      repeat (19) @(posedge tb_clk);
      group_triggers = 'b0;
      repeat (0) @(posedge tb_clk);

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                          .data('h0 /* disable */));
      repeat (40) @(posedge tb_clk);
    end


    begin
      $display("Starting sync start test...");
      trace_st_addr  = 'h1*8;
      trace_size = 'h4*8;

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ST_ADDR),
                            .data(trace_st_addr)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_LOG_SIZE),
                            .data(trace_size)); // external needs to be 1k aligned

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_COUNTER_CTRL), .data('h1 /* wait for sync */));

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_BURST_SIZE),
                          .data('h0  /*burst per 0*/));

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                          .data('h0 | 1 << 0 /* enable */
                                    | 0 << 1 /* discard mode */
                                    | 0 << 2 /* local memory mode */
                                    | 0 << 4  /*cntr_division*/));
      repeat (4) @(posedge tb_clk);

      // check entry count
      tl_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ENTRY_COUNT),
                            .data(rd_data));
      if (0 != rd_data)  // expecting only 6 items to be written
        $error("ERROR! Expected %0d entries, but got %0d @ %0t", 0, rd_data, $time());

      group_triggers = 'b0001;
      repeat (19) @(posedge tb_clk);
      group_triggers = 'b0;
      repeat (2) @(posedge tb_clk);

      // check entry count
      tl_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ENTRY_COUNT),
                            .data(rd_data));
      if (0 != rd_data)  // expecting 0 items to be written
        $error("ERROR! Expected %0d entries, but got %0d @ %0t", 0, rd_data, $time());


      // Enable counter by sync start
      sync_start = 1'b1;
      @(posedge tb_clk);
      #1ps;
      sync_start = 1'b0;
      repeat(2) @(posedge tb_clk);

      group_triggers = 'b0001;
      repeat (4) @(posedge tb_clk);
      group_triggers = 'b0;
      repeat (4) @(posedge tb_clk);

      // check entry count
      tl_drv.csr_rd(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_ENTRY_COUNT),
                            .data(rd_data));
      if (4 != rd_data)  // expecting only 4 items to be written
        $error("ERROR! Expected %0d entries, but got %0d @ %0t", 4, rd_data, $time());

      tl_drv.csr_wr(.reg_idx(timestamp_logger_csr_reg_pkg::TIMESTAMP_LOGGER_CSR_CTRL),
                          .data('h0 /* disable */));
      repeat (10) @(posedge tb_clk);
      // read back written data
      time_stmp=0;
      for (int i = 0; i < trace_size/8; i++) begin
        // miss-use csr function for writes towards the memory using the base override
        tl_drv.csr_rd(.reg_idx(i+(trace_st_addr/8)), .data(rd_data), .dev(1));

        $display(" - entry %0d...", i);

        if (i >= (trace_size/8)) begin  // beyond end address, expect skipped (thus zero)
          if (0 != rd_data)
            $error("ERROR! Entry (0x%0h) found beyond end address! 0x%0h @ %0t", rd_data,
                   MEM_ST_ADDR + (i * 8), $time());
        end else begin
          if (time_stmp > (rd_data >> 32))
            $error(
                "ERROR! Received timestamp (%0d) is not incremental compared to previous one (%0d)!",
                rd_data >> 32, time_stmp);
          time_stmp = (rd_data >> 32);
          if (time_stmp != (i + 2))
             $error("ERROR! Expected Timestamp to be %0d after sync start @ %0t", i+2, $time());
        end
      end
    end

    $finish;
  end

  timestamp_logger #(
    .NumGroups(4),
    .AxiSIdWidth(IDW),
    .AxiMIdWidth(IDW),
    .AxiAddrWidth(AW),
    .AxiDataWidth(DW),
    .GroupDefaultFifoDepth(3),
    .GroupMsgWidth('{3, 0, 2, 1}),
    .TimestampFifoDepth(4),

    .MemDepth(MEM_DEPTH),
    .UseMacro(0)
  ) i_dut (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),

    .i_scan_en(1'b0),

    .i_group_trigger(group_triggers),
    .i_group_message(group_msgs),

    .i_sync_start(sync_start),

    .i_axi_s_aw_id(axi_if.awid),
    .i_axi_s_aw_addr(axi_if.awaddr),
    .i_axi_s_aw_len(axi_if.awlen),
    .i_axi_s_aw_size(axi_if.awsize),
    .i_axi_s_aw_burst(axi_if.awburst),
    .i_axi_s_aw_valid(axi_if.awvalid),
    .o_axi_s_aw_ready(axi_if.awready),

    .i_axi_s_ar_id(axi_if.arid),
    .i_axi_s_ar_addr(axi_if.araddr),
    .i_axi_s_ar_len(axi_if.arlen),
    .i_axi_s_ar_size(axi_if.arsize),
    .i_axi_s_ar_burst(axi_if.arburst),
    .i_axi_s_ar_valid(axi_if.arvalid),
    .o_axi_s_ar_ready(axi_if.arready),

    .i_axi_s_w_data (axi_if.wdata),
    .i_axi_s_w_strb (axi_if.wstrb),
    .i_axi_s_w_last (axi_if.wlast),
    .i_axi_s_w_valid(axi_if.wvalid),
    .o_axi_s_w_ready(axi_if.wready),

    .o_axi_s_r_id(axi_if.rid),
    .o_axi_s_r_data(axi_if.rdata),
    .o_axi_s_r_resp(axi_if.rresp),
    .o_axi_s_r_last(axi_if.rlast),
    .o_axi_s_r_valid(axi_if.rvalid),
    .i_axi_s_r_ready(axi_if.rready),

    .o_axi_s_b_id(axi_if.bid),
    .o_axi_s_b_resp(axi_if.bresp),
    .o_axi_s_b_valid(axi_if.bvalid),
    .i_axi_s_b_ready(axi_if.bready),

    .o_axi_m_aw_id(axi_if_m.awid),
    .o_axi_m_aw_addr(axi_if_m.awaddr),
    .o_axi_m_aw_len(axi_if_m.awlen),
    .o_axi_m_aw_size(axi_if_m.awsize),
    .o_axi_m_aw_burst(axi_if_m.awburst),
    .o_axi_m_aw_valid(axi_if_m.awvalid),
    .i_axi_m_aw_ready(axi_if_m.awready),

    .o_axi_m_ar_id(axi_if_m.arid),
    .o_axi_m_ar_addr(axi_if_m.araddr),
    .o_axi_m_ar_len(axi_if_m.arlen),
    .o_axi_m_ar_size(axi_if_m.arsize),
    .o_axi_m_ar_burst(axi_if_m.arburst),
    .o_axi_m_ar_valid(axi_if_m.arvalid),
    .i_axi_m_ar_ready(axi_if_m.arready),

    .o_axi_m_w_data (axi_if_m.wdata),
    .o_axi_m_w_strb (axi_if_m.wstrb),
    .o_axi_m_w_last (axi_if_m.wlast),
    .o_axi_m_w_valid(axi_if_m.wvalid),
    .i_axi_m_w_ready(axi_if_m.wready),

    .i_axi_m_r_id(axi_if_m.rid),
    .i_axi_m_r_data(axi_if_m.rdata),
    .i_axi_m_r_resp(axi_if_m.rresp),
    .i_axi_m_r_last(axi_if_m.rlast),
    .i_axi_m_r_valid(axi_if_m.rvalid),
    .o_axi_m_r_ready(axi_if_m.rready),

    .i_axi_m_b_id(axi_if_m.bid),
    .i_axi_m_b_resp(axi_if_m.bresp),
    .i_axi_m_b_valid(axi_if_m.bvalid),
    .o_axi_m_b_ready(axi_if_m.bready),

    .o_ip_csr_req(),
    .i_ip_csr_rsp('0),

    .i_sram_impl('0),
    .o_sram_impl()
  );

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end

endmodule
