// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Sanity testbench for the glich-free clock mux
///
module axe_ccl_clk_mux_tb;

  ////////////////////////////////////////
  // Clock parameters for configuration //
  ////////////////////////////////////////
  // run at 20MHz
  localparam realtime TbCyclTime = 50.0ns;
  localparam realtime TbApplTime = 0.1;
  localparam realtime TbTestTime = 0.9;

  localparam int unsigned TbResetCycles   =     10;
  localparam int unsigned TbNumIterations =    100;
  localparam int unsigned TbMaxWaitCycles = 10_000;

  ////////////////////
  // DUT Parameters //
  ////////////////////
  localparam int unsigned TbNumClocks  = 5;
  localparam int unsigned TbSyncStages = 3;

  typedef logic [cc_math_pkg::index_width(TbNumClocks)-1:0] tb_select_t;

  ////////////////////
  // Clock Settings //
  ////////////////////
  typedef struct {
    realtime CyclTime;
    real     DutyCycl;
  } tb_clk_settings_t;

  localparam tb_clk_settings_t ClkSettings[TbNumClocks] = '{
    tb_clk_settings_t'{CyclTime:   0.8ns, DutyCycl: 0.5},
    tb_clk_settings_t'{CyclTime:   4.0ns, DutyCycl: 0.1},
    tb_clk_settings_t'{CyclTime:  11.1ns, DutyCycl: 0.5},
    tb_clk_settings_t'{CyclTime:   0.8ns, DutyCycl: 0.9},
    tb_clk_settings_t'{CyclTime: 134.8ns, DutyCycl: 0.6}
  };

  ////////////////////////////////
  // Clock and Reset Generation //
  ////////////////////////////////

  logic tb_clk_cfg, tb_rst_cfg_n;
  logic tb_clk_inp[TbNumClocks];
  logic tb_clk_oup;

  initial begin : proc_clk_cfg
    tb_clk_cfg = 1'b0;
    forever begin
      #(TbCyclTime/2.0);
      tb_clk_cfg = ~tb_clk_cfg;
    end
  end

  initial begin : proc_rst_cfg_n
    tb_rst_cfg_n = 1'b0;
    repeat (TbResetCycles) @(negedge tb_clk_cfg);
    tb_rst_cfg_n = 1'b1;
  end

  for (genvar clk_idx = 0; unsigned'(clk_idx) < TbNumClocks; clk_idx++) begin : gen_clk
    initial begin : proc_clk
      automatic realtime RiseTime = ClkSettings[clk_idx].CyclTime * (1.0 - ClkSettings[clk_idx].DutyCycl);
      automatic realtime FallTime = ClkSettings[clk_idx].CyclTime * (      ClkSettings[clk_idx].DutyCycl);

      forever begin
        tb_clk_inp[clk_idx] = 1'b0;
        #(RiseTime);
        tb_clk_inp[clk_idx] = 1'b1;
        #(FallTime);
      end
    end
  end

  ////////////////////////
  // Stimuli Generation //
  ////////////////////////
  tb_select_t             tb_select;
  logic                   tb_enable;
  logic [TbNumClocks-1:0] tb_active;
  logic                   tb_is_on;

  initial begin : proc_select
    automatic int unsigned rand_wait;
    automatic int unsigned rand_select;

    tb_select = tb_select_t'(0);

    @(posedge tb_rst_cfg_n);
    @(posedge tb_clk_cfg);

    /////////////////////
    // Random wiggling //
    /////////////////////
    $display("////////////////////////////////////////////////////////////////////////////////");
    $display("%t: Changeing settings every cycle", $time);
    $display("////////////////////////////////////////////////////////////////////////////////");
    repeat (TbNumIterations) begin
      rand_select = $urandom_range(TbNumClocks-1, 0);
      $display("%t: Selecting Clock[%0d]", $time, rand_select);
      tb_select <= #TbApplTime tb_select_t'(rand_select);
      @(posedge tb_clk_cfg);
    end

    ///////////////////////////////////
    // Keep select stable for longer //
    ///////////////////////////////////
    $display("////////////////////////////////////////////////////////////////////////////////");
    $display("%t: Changeing settings more slowly", $time);
    $display("////////////////////////////////////////////////////////////////////////////////");
    repeat (TbNumIterations) begin
      rand_select = $urandom_range(TbNumClocks-1, 0);
      rand_wait   = $urandom_range(TbMaxWaitCycles, 1);
      $display("%t: Selecting Clock[%0d]", $time, rand_select);
      tb_select <= #TbApplTime tb_select_t'(rand_select);
      repeat (rand_wait) @(posedge tb_clk_cfg);
    end

    $display("////////////////////////////////////////////////////////////////////////////////");
    $display("%t: Finish simulation", $time);
    $display("////////////////////////////////////////////////////////////////////////////////");
    $finish;
  end

  always_comb tb_enable = 1'b1;

  ///////////////////////
  // Design Under Test //
  ///////////////////////
  axe_ccl_clk_mux #(
    .NumClocks (TbNumClocks),
    .SyncStages(TbSyncStages)
  ) u_dut_cc_clk_mux (
    .i_clk_cfg  (tb_clk_cfg),
    .i_rst_cfg_n(tb_rst_cfg_n),
    .i_test_mode(1'b0),
    .i_select   (tb_select),
    .i_enable   (tb_enable),
    .o_active   (tb_active),
    .o_is_on    (tb_is_on),
    .i_clk      (tb_clk_inp),
    .o_clk      (tb_clk_oup)
  );
endmodule
