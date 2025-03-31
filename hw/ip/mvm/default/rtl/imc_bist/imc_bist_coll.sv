// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC BIST collector
// Decodes comparator information bus into controller digestible format
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_COLL_SV
`define IMC_BIST_COLL_SV

// verilog_lint: waive-start line-length
module imc_bist_coll
  import imc_bist_pkg::NUM_COMPARATORS;
  import imc_bist_pkg::IMC_BIST_CYCLE_PW;
  import imc_bist_pkg::compare_bus_t;
  import mvm_pkg::MVM_IMC_BANK_PW;
  import mvm_pkg::MVM_NB_IMC_BANKS;
  import imc_bank_pkg::IMC_BANK_COL_PW;
(
  input wire i_clk,
  input wire i_rst_n,

  // <-> CTL
  input logic bist_mode_i,
  input logic start_pi,
  input logic resume_pi,
  input logic stop_pi,

  // <-> COLLs
  input logic compare_bus_strobe_i,
  input compare_bus_t [NUM_COMPARATORS-1:0] compare_bus_i,

  // <-> CTL
  output logic fault_det_o,
  output logic fault_valid_o,
  output logic [MVM_IMC_BANK_PW-1:0] fault_bank_o,
  output logic [IMC_BANK_COL_PW-1:0] fault_col_o,
  output logic [IMC_BIST_CYCLE_PW-1:0] fault_cycle_o,
  input logic fault_pop_i
);

  localparam int unsigned LComparatorPw = $clog2(NUM_COMPARATORS);

  typedef struct packed {
    logic ok;
    logic [IMC_BANK_COL_PW-1:0] fail_column;
  } bank_info_t;

  typedef struct packed {
    logic [IMC_BIST_CYCLE_PW-1:0] cycle;
    bank_info_t [MVM_NB_IMC_BANKS-1:0] bank_info;
  } work_item_t;

  // Unscramble the comparators into banks
  // 0: 0 2 = 0*4
  // 1: 4 6 = 1*4
  // 2: 8 10 = 2*4
  // 3: 12 14 = 3*4
  // 4: 1 3 = (4-(8/2))*4+1
  // 5: 5 7 = (5-(8/2))*4+1
  // 6: 9 11 = (6-(8/2))*4+1
  // 7: 13 15 = (7-(8/2))*4+1
  function automatic logic [MVM_IMC_BANK_PW-1:0] f_unscrambleLeftBank(
      input logic [LComparatorPw-1:0] i_comp_index);
    if (i_comp_index < (NUM_COMPARATORS / 2)) return (i_comp_index * 4);
    else return ((i_comp_index - (NUM_COMPARATORS / 2)) * 4 + 1);
  endfunction

  function automatic logic [MVM_IMC_BANK_PW-1:0] f_unscrambleRightBank(
      input logic [LComparatorPw-1:0] i_comp_index);
    return f_unscrambleLeftBank(i_comp_index) + 'd2;
  endfunction

  function automatic logic f_isOneHotZero(input logic [MVM_NB_IMC_BANKS-1:0] i_inp);
    for (int i = 0; i < MVM_NB_IMC_BANKS; i++)
      if (i_inp == ((MVM_NB_IMC_BANKS)'(1'b1) << i)) return 1'b1;
    return ~|i_inp;
  endfunction

  // Fault analysis mode, not implemented in bronze
  logic resume_pi_unc, fault_pop_i_unc;

  bank_info_t [MVM_NB_IMC_BANKS-1:0] s_bank;
  logic [MVM_NB_IMC_BANKS-1:0] s_bank_ok_vec;

  logic [IMC_BIST_CYCLE_PW-1:0] s_cycle_cnt, r_cycle_cnt;
  logic s_running, r_running;

  logic s_fault_valid, r_fault_valid;
  logic [MVM_IMC_BANK_PW-1:0] s_fail_bank, s_fault_bank, r_fault_bank;
  logic [IMC_BANK_COL_PW-1:0] s_fault_col, r_fault_col;
  logic [IMC_BIST_CYCLE_PW-1:0] s_fault_cycle, r_fault_cycle;

  logic s_banks_ok;

  // Unscramble banks
  // Bit-width mismatch between function call argument 'i' ('32' bits) and function input 'i_comp_index' ('3' bits)
  // tiago: i iterates NUM_COMPARATORS and never exceeds LComparatorPw
  always_comb
    foreach (compare_bus_i[i]) begin
      s_bank[f_unscrambleLeftBank(i)] = '{ok: compare_bus_i[i].lbank_ok,
                                          fail_column: compare_bus_i[i].fail_column};
      s_bank[f_unscrambleRightBank(i)] = '{ok: compare_bus_i[i].rbank_ok,
                                           fail_column: compare_bus_i[i].fail_column};
    end

  // Detect failures
  always_comb foreach (s_bank_ok_vec[i]) s_bank_ok_vec[i] = s_bank[i].ok;
  assign s_banks_ok  = (&s_bank_ok_vec) | ~compare_bus_strobe_i;

  // Stop counting if stop_pi is asserted or bist_mode_i is deasserted
  assign s_running   = r_running & (~(stop_pi | (~bist_mode_i)));
  assign s_cycle_cnt = r_cycle_cnt + r_running;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : r_cycle_cnt_sproc
    if (!i_rst_n) begin
      r_cycle_cnt <= '0;
      r_running   <= 1'b0;
    end else if (start_pi) begin
      // Start counting
      r_cycle_cnt <= '0;
      r_running   <= 1'b1;
    end else if (resume_pi) begin
      // Resume counting
      r_cycle_cnt <= r_cycle_cnt;
      r_running   <= 1'b1;
    end else begin
      r_cycle_cnt <= s_cycle_cnt;
      r_running   <= s_running;
    end
  end : r_cycle_cnt_sproc

  // Push detected failures into a queue
  logic fault_queue_push_en;
  work_item_t fault_queue_push_data;
  logic fault_queue_pop_en;
  work_item_t fault_queue_pop_data;
  logic fault_queue_full;
  logic fault_queue_empty;
  // Pop the fault queue into a 'work item'
  logic current_work_item_last;
  logic [MVM_NB_IMC_BANKS-1:0] fault_queue_bank_ok_mask;
  logic [MVM_NB_IMC_BANKS-1:0] fault_queue_bank_ok_masked;
  logic [MVM_NB_IMC_BANKS-1:0] fault_queue_bank_ok_vec;
  logic s_fail_banks_ok;
  // Output layer
  logic s_capture_new_fault;
  logic s_fault_det;

  // Push to queue if there is a fault detected
  assign fault_queue_push_en   = ~s_banks_ok & ~fault_queue_full;
  assign fault_queue_push_data = '{cycle: r_cycle_cnt, bank_info: s_bank};

  fifo_v3 #(
    .DATA_WIDTH($bits(work_item_t)),
    .DEPTH(7)  // Arbitrary
  ) i_fault_queue (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .flush_i(start_pi),
    .testmode_i(1'b0),
    .full_o(fault_queue_full),
    .empty_o(fault_queue_empty),
    .usage_o(),
    .data_i(fault_queue_push_data),
    .push_i(fault_queue_push_en),
    .data_o(fault_queue_pop_data),
    .pop_i(fault_queue_pop_en)
  );

  // Pop from queue if there is no work item or work item is finishing this cycle
  assign fault_queue_pop_en = (fault_pop_i & current_work_item_last) & ~fault_queue_empty;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (~i_rst_n) fault_queue_bank_ok_mask <= '0;
    else begin
      if(start_pi) fault_queue_bank_ok_mask <= '0;
      else if (fault_queue_pop_en) fault_queue_bank_ok_mask <= '0;
      else if (s_capture_new_fault)
        fault_queue_bank_ok_mask <= fault_queue_bank_ok_mask | ((MVM_NB_IMC_BANKS)'(1) << s_fail_bank);
    end

  // Decode the work item
  always_comb
    foreach (fault_queue_bank_ok_vec[i])
      fault_queue_bank_ok_vec[i] = fault_queue_pop_data.bank_info[i].ok | fault_queue_empty;
  assign fault_queue_bank_ok_masked = fault_queue_bank_ok_vec | fault_queue_bank_ok_mask;
  assign current_work_item_last = f_isOneHotZero(~fault_queue_bank_ok_masked);

  lzc #(
    .WIDTH(MVM_NB_IMC_BANKS),
    .MODE(0)  // TZC mode detects first failure starting from bank 0
  ) i_lzc_banks_ok (
    .in_i(~fault_queue_bank_ok_masked),
    .cnt_o(s_fail_bank),
    .empty_o(s_fail_banks_ok)
  );

  assign s_fault_det = ~fault_queue_empty & ~s_fail_banks_ok;
  assign s_capture_new_fault = (~r_fault_valid | fault_pop_i) & s_fault_det;
  assign s_fault_valid = r_fault_valid ? ~(fault_pop_i & ~s_fault_det) : s_fault_det;
  assign s_fault_bank = s_capture_new_fault ? s_fail_bank : r_fault_bank;
  assign s_fault_col         = s_capture_new_fault ? fault_queue_pop_data.bank_info[s_fail_bank].fail_column : r_fault_col;
  assign s_fault_cycle = s_capture_new_fault ? r_cycle_cnt : fault_queue_pop_data.cycle;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : r_fault_sproc
    if (~i_rst_n) begin
      r_fault_valid <= 1'b0;
      r_fault_bank  <= '0;
      r_fault_col   <= '0;
      r_fault_cycle <= '0;
    end else begin
      if (start_pi) begin
        // Synchronous clear
        r_fault_valid <= 1'b0;
        r_fault_bank  <= '0;
        r_fault_col   <= '0;
        r_fault_cycle <= '0;
      end else begin
        r_fault_valid <= s_fault_valid;
        r_fault_bank  <= s_fault_bank;
        r_fault_col   <= s_fault_col;
        r_fault_cycle <= s_fault_cycle;
      end
    end
  end : r_fault_sproc

  assign fault_det_o   = s_fault_det;
  assign fault_valid_o = r_fault_valid;
  assign fault_bank_o  = r_fault_bank;
  assign fault_col_o   = r_fault_col;
  assign fault_cycle_o = r_fault_cycle;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on

endmodule
// verilog_lint: waive-stop line-length
`endif  // IMC_BIST_COLL_SV
