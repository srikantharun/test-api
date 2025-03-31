// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC BIST comparator
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_COMP_SV
`define IMC_BIST_COMP_SV

// verilog_lint: waive-start line-length
module imc_bist_comp
  import imc_bist_pkg::expect_type_e;
  import imc_bist_pkg::compare_bus_t;
  import imc_bist_pkg::E_NEIGHBOR;
  import imc_bist_pkg::E_GOLDEN_ZEROES;
  import imc_bist_pkg::E_GOLDEN_ONES;
  import imc_bist_pkg::E_GOLDEN_55;
  import imc_bist_pkg::E_GOLDEN_AA;
  import imc_bist_pkg::NUM_COMPARATORS;
  import mvm_pkg::DATA_W;
  import imc_bank_pkg::IMC_NB_COLS_PER_BANK;
  import imc_bank_pkg::IMC_BANK_COL_PW;
  //import imc_bank_pkg::IMC_OUT_DATA_W;
  import mvm_pkg::MVM_IMC_OUT_DATA_W;
#(
  parameter int unsigned PAIR_ID = 0,
  parameter int unsigned INPUT_DELAY = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  // <-> Upstream daisy
  input logic expect_strobe_i,
  input expect_type_e expect_type_i,
  input compare_bus_t [NUM_COMPARATORS-1:0] compare_bus_i,

  // <-> Left IMC BANK
  input logic [IMC_NB_COLS_PER_BANK-1:0][MVM_IMC_OUT_DATA_W-1:0] lbank_data_i,
  // <-> Right IMC BANK
  input logic [IMC_NB_COLS_PER_BANK-1:0][MVM_IMC_OUT_DATA_W-1:0] rbank_data_i,

  // <-> Downstream daisy
  output logic expect_strobe_o,
  output expect_type_e expect_type_o,
  output compare_bus_t [NUM_COMPARATORS-1:0] compare_bus_o
);

  localparam int unsigned Stage = (PAIR_ID * 2) / NUM_COMPARATORS + (PAIR_ID % 2) * (NUM_COMPARATORS / 2);

  // Reference data for E_GOLDEN_ZEROES expectation
  localparam logic [MVM_IMC_OUT_DATA_W-1:0] LRefDataZeroes = {MVM_IMC_OUT_DATA_W{1'b0}};
  // Reference data for E_GOLDEN_ONES expectation
  localparam logic [MVM_IMC_OUT_DATA_W-1:0] LRefDataOnes = (MVM_IMC_OUT_DATA_W)'({DATA_W{1'b1}});
  // Reference data for E_GOLDEN_55 expectation
  localparam logic [MVM_IMC_OUT_DATA_W-1:0] LRefData55 = 'h55;
  // Reference data for E_GOLDEN_AA expectation
  localparam logic [MVM_IMC_OUT_DATA_W-1:0] LRefDataAA = 'haa;

  function automatic logic [MVM_IMC_OUT_DATA_W-1:0] f_getRefData(input expect_type_e i_et);
    logic [MVM_IMC_OUT_DATA_W-1:0] l_ref;
    unique case (i_et)
      default: l_ref = LRefDataZeroes;
      E_GOLDEN_ONES: l_ref = LRefDataOnes;
      E_GOLDEN_55: l_ref = LRefData55;
      E_GOLDEN_AA: l_ref = LRefDataAA;
    endcase
    f_getRefData = l_ref;
  endfunction

  // Internal daisy
  typedef struct packed {
    logic strobe;
    expect_type_e etype;
    compare_bus_t [NUM_COMPARATORS-1:0] compare_bus;
  } algn_t;

  // Input ties
  logic [NUM_COMPARATORS-1:0] s_in_tie_n;
  compare_bus_t [NUM_COMPARATORS-1:0] s_compare_bus_in_tie;

  // Data alignment
  algn_t s_algn_input, r_algn_lbank, s_comp_lbank, r_algn_rbank, s_comp_rbank, r_algn_output;
  logic [IMC_NB_COLS_PER_BANK-1:0][MVM_IMC_OUT_DATA_W-1:0] r_lbank_data;

  // Comparison logic
  logic [IMC_NB_COLS_PER_BANK-1:0] s_col_match_lbank, s_col_match_rbank;
  logic s_lbank_ok, s_rbank_ok;
  logic [IMC_BANK_COL_PW-1:0] s_lbank_fail_col, s_rbank_fail_col;

  // Output ties
  logic [NUM_COMPARATORS-1:0] s_out_tie_n;

  // Lint
  // Unconnected OK: We ignore r_algn_lbank.compare_bus[Stage], as it is inserted by the left-comparator
  //                 We ignore r_algn_rbank.compare_bus[Stage].rbank_ok, at it is inserted by the right-comparator
  compare_bus_t unconnected_ok_r_algn_lbank_at_stage;
  logic unconnected_ok_r_algn_rbank_rbank_ok_at_stage;

  // and-gate tie unused bits in the input compare bus to ensure they are never synthesized as FFs
  // PAIR_ID=0  = Stage 0 : 00 000 000
  // PAIR_ID=4  = Stage 1 : 00 000 001
  // PAIR_ID=8  = Stage 2 : 00 000 011
  // PAIR_ID=12 = Stage 3 : 00 000 111
  // PAIR_ID=1  = Stage 4 : 00 001 111
  // PAIR_ID=5  = Stage 5 : 00 011 111
  // PAIR_ID=9  = Stage 6 : 00 111 111
  // PAIR_ID=13 = Stage 7 : 01 111 111
  always_comb foreach (s_in_tie_n[i]) s_in_tie_n[i] = (i < Stage);
  always_comb
    foreach (s_compare_bus_in_tie[i])
      s_compare_bus_in_tie[i] = compare_bus_i[i] & {$bits(compare_bus_t) {s_in_tie_n[i]}};

  assign s_algn_input = '{
          strobe: expect_strobe_i,
          etype: expect_type_i,
          compare_bus: s_compare_bus_in_tie
      };

  // Align input to LBANK dataout
  cc_cnt_shift_reg #(
    .data_t(algn_t),
    .Stages(INPUT_DELAY)
  ) i_dly2lbank (
    .i_clear(1'b0),
    .i_stall(1'b0),
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_data(s_algn_input),
    .i_data_en(1'b1),
    .o_data(r_algn_lbank),
    .o_updated()
  );

  // Compare LBANK
    always_comb begin
      for(int i = 0; i < IMC_NB_COLS_PER_BANK; i++) begin
        if (~r_algn_lbank.strobe)
          s_col_match_lbank[i] = 1'b1;  // If there's no expect strobe, always match
        else if (r_algn_lbank.etype == E_NEIGHBOR)
          s_col_match_lbank[i] = 1'b1;  // If comparing neighbor, LBANK is always match
        else begin
          // If comparing golden, compare agaisnt L_REF_DATA
          s_col_match_lbank[i] = (lbank_data_i[i] == f_getRefData(r_algn_lbank.etype));
        end
      end
    end

  // Use a LZC to identify pass, and fail column if applicable
  lzc #(
    .WIDTH(IMC_NB_COLS_PER_BANK),
    .MODE(0)  // TZC mode detects first failure starting from column 0
  ) i_lzc_lbank (
    .in_i(~s_col_match_lbank),
    .cnt_o(s_lbank_fail_col),
    .empty_o(s_lbank_ok)
  );

  always_comb begin : s_comp_lbank_cproc
    s_comp_lbank.strobe = r_algn_lbank.strobe;
    s_comp_lbank.etype  = r_algn_lbank.etype;

    foreach (s_comp_lbank.compare_bus[i]) begin
      if (i == Stage) begin
        // Insert comparison results in our Stage
        s_comp_lbank.compare_bus[i] = '{
            lbank_ok: s_lbank_ok,
            rbank_ok: 1'b1,  // To be compared later
            fail_column: s_lbank_fail_col
        };
        unconnected_ok_r_algn_lbank_at_stage = r_algn_lbank.compare_bus[i];
      end else s_comp_lbank.compare_bus[i] = r_algn_lbank.compare_bus[i];
    end
  end : s_comp_lbank_cproc

  // Align LBANK to RBANK dataout
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_algn_rbank.strobe <= '0;
    else r_algn_rbank.strobe <= s_comp_lbank.strobe;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_algn_rbank.etype <= E_NEIGHBOR;
    else r_algn_rbank.etype <= s_comp_lbank.etype;

  for (
      genvar iter_comps = 0; iter_comps < NUM_COMPARATORS; iter_comps++
  ) begin : gen_algn_rbank_iter
    if (iter_comps > Stage) begin : gen_tied_algn_rbank
      // Unconnected OK: Compare bus higher than our current Stage is not used
      compare_bus_t unconnected_ok_s_comp_lbank_compare_bus;

      assign r_algn_rbank.compare_bus[iter_comps] = '0;
      assign unconnected_ok_s_comp_lbank_compare_bus = s_comp_lbank.compare_bus[iter_comps];
    end else begin : gen_algn_rbank
      always_ff @(posedge i_clk, negedge i_rst_n)
        if (!i_rst_n) r_algn_rbank.compare_bus[iter_comps] <= '0;
        else r_algn_rbank.compare_bus[iter_comps] <= s_comp_lbank.compare_bus[iter_comps];
    end
  end : gen_algn_rbank_iter

  // RST has been intentionally removed from these FF
  always_ff @(posedge i_clk) if (s_comp_lbank.strobe) r_lbank_data <= lbank_data_i;

  // Compare RBANK
    always_comb begin
      for (int i = 0; i < IMC_NB_COLS_PER_BANK; i++) begin
        if (~r_algn_rbank.strobe)
          s_col_match_rbank[i] = 1'b1;  // If there's no expect strobe, always match
        else if (r_algn_rbank.etype == E_NEIGHBOR)
          s_col_match_rbank[i] = (rbank_data_i[i] == r_lbank_data[i]);
        else begin
          // If comparing golden, compare agaisnt REF_DATA
          s_col_match_rbank[i] = (rbank_data_i[i] == f_getRefData(r_algn_rbank.etype));
        end
      end
    end

  lzc #(
    .WIDTH(IMC_NB_COLS_PER_BANK),
    .MODE(0)  // TZC mode detects first failure starting from column 0
  ) i_lzc_rbank (
    .in_i(~s_col_match_rbank),
    .cnt_o(s_rbank_fail_col),
    .empty_o(s_rbank_ok)
  );

  // verilog_format: off // tiago: verible format is hard to understand here
  always_comb begin : s_comp_rbank_cproc
    s_comp_rbank.strobe = r_algn_rbank.strobe;
    s_comp_rbank.etype = r_algn_rbank.etype;

    foreach(s_comp_rbank.compare_bus[i]) begin
        if(i==Stage) begin
          // Update comparison results in our Stage
          s_comp_rbank.compare_bus[i] = '{
          lbank_ok: r_algn_rbank.compare_bus[i].lbank_ok,
          rbank_ok: s_rbank_ok,
          fail_column: r_algn_rbank.compare_bus[i].lbank_ok ? s_rbank_fail_col : r_algn_rbank.compare_bus[i].fail_column
        };
        unconnected_ok_r_algn_rbank_rbank_ok_at_stage = r_algn_rbank.compare_bus[i].rbank_ok;
        end else s_comp_rbank.compare_bus[i] = r_algn_rbank.compare_bus[i];
    end
  end : s_comp_rbank_cproc
  // verilog_format: on

  // Align RBANK to output
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_algn_output.strobe <= '0;
    else r_algn_output.strobe <= s_comp_rbank.strobe;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_algn_output.etype <= E_NEIGHBOR;
    else r_algn_output.etype <= s_comp_rbank.etype;

  for (
      genvar iter_comps = 0; iter_comps < NUM_COMPARATORS; iter_comps++
  ) begin : gen_algn_output_iter
    if (iter_comps > Stage) begin : gen_tied_algn_output
      // Unconnected OK: Compare bus higher than our current Stage is not used
      compare_bus_t unconnected_ok_s_comp_rbank_compare_bus;

      assign r_algn_output.compare_bus[iter_comps]   = '0;
      assign unconnected_ok_s_comp_rbank_compare_bus = s_comp_rbank.compare_bus[iter_comps];
    end else begin : gen_algn_output
      always_ff @(posedge i_clk, negedge i_rst_n)
        if (!i_rst_n) r_algn_output.compare_bus[iter_comps] <= '0;
        else r_algn_output.compare_bus[iter_comps] <= s_comp_rbank.compare_bus[iter_comps];
    end
  end : gen_algn_output_iter

  assign expect_strobe_o = r_algn_output.strobe;
  assign expect_type_o   = r_algn_output.etype;
  assign compare_bus_o   = r_algn_output.compare_bus;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
// verilog_lint: waive-stop line-length
`endif  // IMC_BIST_COMP_SV
