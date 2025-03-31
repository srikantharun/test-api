// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This module is used to debounce the input button input 
//              to remove spurious glitches on the input signal. 
// Owner: Abhishek Maringanti <Abhishek.Maringanti@axelera.ai>

`ifndef SIGNAL_DEBOUNCE_SV
  `define SIGNAL_DEBOUNCE_SV

  module signal_debounce #(
  ) (
    input  logic clk_i,
    input  logic por_rst_n_sync_i,        // Synchronous Power-ON Reset signal. 
    input  logic inp_sig_ni,              // Active_low button input signal.
    
    input  logic [31:0] dbnc_timer_val_i, // CSR configurable timer value.
    output logic inp_sig_dbncd_no,        // debounced signal output (Active Low).

    input  logic test_mode_i              // DFT Scan Mode.

  );

  localparam DBNC_IDLE = 2'b00;
  localparam DBNC_ACTIVE = 2'b01;

  logic [1:0] curr_dbnc_state;
  logic [1:0] nxt_dbnc_state;
  
  logic inp_sig_sync;
  logic [31:0] timer_dbnc;

  // synchronize the incoming button input to the ref-clk domain
  // to avoid metastability issues.
  cdc_level #(
    .STAGE_NUM(2),
    .RESET_VALUE(1)
  )
  i_cdc_level_dbnc_inp_sig  (
    .s_level_i(inp_sig_ni),
    .d_clk_i(clk_i),
    .d_rst_ni(por_rst_n_sync_i),
    .d_level_o(inp_sig_sync),
    .d_pulse_o()
  );

  // Timer for debounce stable value. 
  // Set timer to a CSR value when button is pressed.
  // Decrement timer to 0 and ignore all button pulses/glitches during this period.
  // Trigger this timer for both button press and release if the button press is for a longer duration than the timer.
  always_ff  @(posedge clk_i or negedge por_rst_n_sync_i) begin
    if (~por_rst_n_sync_i)
      timer_dbnc <= 32'h00000000;
    else if (|timer_dbnc)
      timer_dbnc <= timer_dbnc -1;
    else if (((curr_dbnc_state == DBNC_IDLE) & (inp_sig_sync == 1'b0)) | ((curr_dbnc_state == DBNC_ACTIVE) & (inp_sig_sync == 1'b1)))
      timer_dbnc <= dbnc_timer_val_i;
  end

  // FSM to track the status of the button presses and timer. 
  always_ff @(posedge clk_i or negedge por_rst_n_sync_i) begin
    if (~por_rst_n_sync_i)
      curr_dbnc_state <= DBNC_IDLE;
    else
      curr_dbnc_state <= nxt_dbnc_state;
  end

  always_comb begin
    nxt_dbnc_state = DBNC_IDLE;
    case (curr_dbnc_state)
      DBNC_IDLE: begin
        if (~inp_sig_sync & (~(|timer_dbnc)))
          nxt_dbnc_state = DBNC_ACTIVE;
        else
          nxt_dbnc_state = DBNC_IDLE;
      end
      DBNC_ACTIVE: begin
        if ((~(|timer_dbnc)) & inp_sig_sync)
          nxt_dbnc_state = DBNC_IDLE;
        else
          nxt_dbnc_state = DBNC_ACTIVE;
      end
    endcase
  end

  // DBNC_ACTIVE State => button is pressed and waiting for button release and timer_dbnc = 0;
  assign inp_sig_dbncd_no = (curr_dbnc_state == DBNC_ACTIVE) ? 1'b0 : 1'b1;


  endmodule // signal_debounce


`endif // SIGNAL_DEBOUNCE_SV
  
