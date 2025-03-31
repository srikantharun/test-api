// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple testbench for Generic Performance Counter test
// Owner: Emre Kirkaya <emre.kirkaya@axelera.ai>

module tb_gen_perf_counter;

    // Definitions
    localparam TB_NUM_COUNTER   = 16;
    localparam TB_COUNTER_WIDTH = 32;
    localparam TB_NUM_MODE      = 4;

    // TB Signals
    logic  tb_clk;
    logic  tb_rst_n;

    logic [$clog2(TB_NUM_MODE) - 1 : 0]                         tb_mode_cnt;
    logic [TB_NUM_COUNTER - 1 : 0][TB_COUNTER_WIDTH - 1 : 0]    tb_in_cnt;
    logic [TB_NUM_COUNTER - 1 : 0]                              tb_en_cnt;
    logic [TB_NUM_COUNTER - 1 : 0][TB_NUM_MODE - 1 : 0]         tb_inc_cnt;

    logic [TB_NUM_COUNTER - 1 : 0]                              tb_wen_cnt;
    logic [TB_NUM_COUNTER - 1 : 0][TB_COUNTER_WIDTH - 1 : 0]    tb_out_cnt;

    logic [TB_NUM_COUNTER - 1 : 0][TB_COUNTER_WIDTH - 1 : 0]    tb_cnt_reg;

    // DUT instantiation
    gen_perf_counter #(
        .NUM_COUNTER    (TB_NUM_COUNTER),
        .COUNTER_WIDTH  (TB_COUNTER_WIDTH),
        .NUM_MODE       (TB_NUM_MODE)
    ) u_gen_perf_counter (
        //Clocka dn reset
        .i_clk        (tb_clk),
        .i_rst_n      (tb_rst_n),

        .i_mode_cnt   (tb_mode_cnt),
        .i_in_cnt     (tb_in_cnt),
        .i_en_cnt     (tb_en_cnt),
        .i_inc_cnt    (tb_inc_cnt),

        .o_wen_cnt    (tb_wen_cnt),
        .o_out_cnt    (tb_out_cnt)
    );

    // Test

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

    localparam COUNT_MODE = 0;

    // Stimulus
    initial begin
      tb_mode_cnt   = COUNT_MODE;
      tb_inc_cnt    = 'd0;
      tb_en_cnt     = 'd0;

        // Counter overflow test
      //for(int idx = 0; idx < TB_NUM_COUNTER; idx++) begin
      //    tb_in_cnt[idx] = 32'hffff_ffff;
      //end

      wait(tb_rst_n);

      for(int idx = 0; idx < TB_NUM_COUNTER; idx++) begin
          tb_inc_cnt[idx][COUNT_MODE] = 1'b1;
          tb_en_cnt[idx] = 1'b1;
      end

      repeat(200) @(posedge tb_clk);

      $finish;
    end

    // CSR emulation
    always_ff @(posedge tb_clk or negedge tb_rst_n)
    begin
        for(int idx = 0; idx < TB_NUM_COUNTER; idx++) begin
            if(!tb_rst_n)
                tb_cnt_reg[idx] <= '0;
            else if(tb_wen_cnt[idx])
                tb_cnt_reg[idx] <= tb_out_cnt[idx];
        end
    end

    assign tb_in_cnt = tb_cnt_reg;

endmodule
