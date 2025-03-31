// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Generic performance counter combinational logic section.
// Counter output to be connected to a CSR register input and the same
// CSR output needs to be connected to the counter input. Numbe of counter
// and counter width can be adjusted based on the parameters. Counter modes
// represents different incrementers to the same counters. The number of
// observable signal can be increased in this way.
//
// Owner: Emre Kirkaya <emre.kirkaya@axelera.ai>

module gen_perf_counter #(
    // Number of generic counter
    parameter int unsigned NUM_COUNTER    = 16,
    // Counter register width
    parameter int unsigned COUNTER_WIDTH  = 32,
    // Number of counter mode
    parameter int unsigned NUM_MODE       = 4
)(
    input   wire  i_clk,
    input   wire  i_rst_n,

    // Counter mode input
    input   logic [$clog2(NUM_MODE) - 1 : 0]                    i_mode_cnt,
    // Counter input value coming from CSR regs
    input   logic [NUM_COUNTER - 1 : 0][COUNTER_WIDTH - 1 : 0]  i_in_cnt,
    // Counter enable for each counter
    input   logic [NUM_COUNTER - 1 : 0]                         i_en_cnt,
    // Counter incrementer for each counter to be selected based on mode
    input   logic [NUM_COUNTER - 1 : 0][NUM_MODE - 1 : 0]       i_inc_cnt,

    // Write enable signal for counter output to the CSR regs
    output  logic [NUM_COUNTER - 1 : 0]                         o_wen_cnt,
    // Counter output value to be written to the CSR regs
    output  logic [NUM_COUNTER - 1 : 0][COUNTER_WIDTH - 1 : 0]  o_out_cnt
);

    always_comb begin
        for(int idx = 0; idx < NUM_COUNTER;  idx++) begin
            // Increment counter
            o_out_cnt[idx]  = i_in_cnt[idx] + 1'b1;
            // Write enable counter register if the counter enabled and incremented and not full
            o_wen_cnt[idx]  = i_en_cnt[idx] && i_inc_cnt[idx][i_mode_cnt] && !(&i_in_cnt[idx]);
        end
    end

endmodule
