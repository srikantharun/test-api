// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Input beat #1: 64 words of 26-bits each, containing lowest-26-bits of each adder result
// Input beat #2: 64 words of 26-bits each, containing highest-26-bits of each adder result
// Output beat #1: 32 words of 52-bits each, containing all bits of each adder result
// Output beat #2: 32 words of 52-bits each, containing all bits of each adder result
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module mvm_int16_interleaver #(
  parameter int unsigned DATA_W = 26,
  parameter int unsigned PW_LEN = 64,

  localparam int unsigned PIPELINE_INPUT = 1
) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic i_enable,

  input  logic i_pw_data_valid,
  output logic o_pw_data_ready,
  input  logic [PW_LEN-1:0][DATA_W-1:0] i_pw_data,
  input  logic i_pw_last,

  output logic o_pw_data_valid,
  input  logic i_pw_data_ready,
  output logic [PW_LEN-1:0][DATA_W-1:0] o_pw_data,
  output logic o_pw_last
);

  typedef enum logic [1:0] {
    E_NO_DATA_STORED = 2'b00,
    E_LOW_BYTES_STORED = 2'b01,
    E_HALF_BEATS_STORED = 2'b10
  } state_t;

  state_t s_state, r_state;
  logic [1:0] write_enable;
  logic [1:0] write_address;

  logic [1:0][PW_LEN/2-1:0][DATA_W-1:0] s_input_half;
  logic [1:0][PW_LEN/2-1:0][DATA_W-1:0] s_store, r_store;
  logic [1:0][PW_LEN/2-1:0][DATA_W-1:0] s_deinterleaved_output;
  logic [PW_LEN-1:0][DATA_W-1:0] s_interleaved_output;
  logic s_output_valid;
  logic s_last, r_last;

  logic s_enable_int;

  ///////////////////////////////////////////////
  // 0. Input pipeline
  ///////////////////////////////////////////////
  logic r_pw_data_valid;
  logic s_pw_data_ready;
  logic [PW_LEN-1:0][DATA_W-1:0] r_pw_data;
  logic r_pw_last;

  if(PIPELINE_INPUT) begin : g_pipe_input
    cc_stream_spill_reg #(
      .DataWidth(PW_LEN*DATA_W+1),
      .CutFirst(1'b1)
    ) u_inp_pipe (
      .i_clk,
      .i_rst_n,

      .i_flush(1'b0),

      .i_data({i_pw_data, i_pw_last}),
      .i_valid(i_pw_data_valid),
      .o_ready(o_pw_data_ready),

      .o_data({r_pw_data, r_pw_last}),
      .o_valid(r_pw_data_valid),
      .i_ready(s_pw_data_ready)
    );
  end else begin : g_no_pipe_input
    assign r_pw_data_valid = i_pw_data_valid;
    assign o_pw_data_ready = s_pw_data_ready;
    assign r_pw_data = i_pw_data;
    assign r_pw_last = i_pw_last;
  end

  ///////////////////////////////////////////////
  // 1. State control
  ///////////////////////////////////////////////
  always_comb case(r_state)
    E_NO_DATA_STORED:
      s_state = (r_pw_data_valid) ? E_LOW_BYTES_STORED : E_NO_DATA_STORED;
    E_LOW_BYTES_STORED:
      s_state = (r_pw_data_valid & i_pw_data_ready) ? E_HALF_BEATS_STORED : E_LOW_BYTES_STORED;
    E_HALF_BEATS_STORED:
      s_state = ( r_pw_data_valid & i_pw_data_ready) ? E_LOW_BYTES_STORED :
                (~r_pw_data_valid & i_pw_data_ready) ? E_NO_DATA_STORED : E_HALF_BEATS_STORED;
    default:
      s_state = E_NO_DATA_STORED;
  endcase

  // Enable the block if we have enough data to send, even if there are no incoming beats
  assign s_enable_int = i_enable || (r_state == E_HALF_BEATS_STORED);

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)      r_state <= E_NO_DATA_STORED;
    else if(s_enable_int) r_state <= s_state;

  ///////////////////////////////////////////////
  // 2. Write/read control
  ///////////////////////////////////////////////
  always_comb case(r_state)
    E_NO_DATA_STORED,
    E_HALF_BEATS_STORED: begin
      // The left-side input half is written in the left-storage
      // The right-side input half is written in the right-storage
      write_enable  = {2{r_pw_data_valid}} & 2'b11;
      write_address = 2'b10;
    end
    E_LOW_BYTES_STORED: begin
      // The left-side input half is written in the right-storage
      // The right-side input half is not stored (streamed to output)
      write_enable  = {2{r_pw_data_valid}} & {2{i_pw_data_ready}} & 2'b10;
      write_address = 2'b00;
    end
    default: begin
      write_enable  = 2'b00;
      write_address = 2'b00;
    end
  endcase

  ///////////////////////////////////////////////
  // 3. Storage
  ///////////////////////////////////////////////
  assign s_input_half = r_pw_data;

  always_comb begin : s_store_cproc
    s_store = r_store;
    foreach(write_enable[i])
      if(write_enable[i]) s_store[write_address[i]] = s_input_half[i];
  end : s_store_cproc

  for(genvar g = 0; g < 2; g++) begin : g_store_sproc
    always_ff @(posedge i_clk, negedge i_rst_n)
      if(~i_rst_n)           r_store[g] <= '0;
      else if(|write_enable) r_store[g] <= s_store[g];
  end

  ///////////////////////////////////////////////
  // 4. Output beat construction
  ///////////////////////////////////////////////
  always_comb case(r_state)
    E_NO_DATA_STORED:
      s_deinterleaved_output = '0;
    E_LOW_BYTES_STORED:
      s_deinterleaved_output = {s_input_half[0], r_store[0]};
    E_HALF_BEATS_STORED:
      s_deinterleaved_output = {r_store[0], r_store[1]};
    default:
      s_deinterleaved_output = '0;
  endcase

  // s_interleaved_output[0] = s_deinterleaved_output[0][0]
  // s_interleaved_output[1] = s_deinterleaved_output[1][0]
  // s_interleaved_output[2] = s_deinterleaved_output[0][1]
  // ...
  // s_interleaved_output[61] = s_deinterleaved_output[1][30]
  // s_interleaved_output[62] = s_deinterleaved_output[0][31]
  // s_interleaved_output[63] = s_deinterleaved_output[1][31]
  always_comb foreach(s_interleaved_output[i]) s_interleaved_output[i] = s_deinterleaved_output[i%2][i/2];

  ///////////////////////////////////////////////
  // 5. Valid/Last tracking
  ///////////////////////////////////////////////
  // This cycle's valid
  always_comb case(r_state)
    E_NO_DATA_STORED: // Not enough data to construct a full beat
      s_output_valid = 1'b0;
    E_LOW_BYTES_STORED: // Only enough data if receiving an input beat
      s_output_valid = r_pw_data_valid;
    E_HALF_BEATS_STORED: // Always enough data to construct a full beat
      s_output_valid = 1'b1;
    default:
      s_output_valid = 1'b0;
  endcase

  // Next cycle's last
  always_comb case(r_state)
    E_NO_DATA_STORED:
      s_last = 1'b0;
    E_LOW_BYTES_STORED:
      s_last = r_pw_data_valid & i_pw_data_ready & r_pw_last;
    E_HALF_BEATS_STORED:
      s_last = (~i_pw_data_ready) & r_last;
    default:
      s_last = 1'b0;
  endcase

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)          r_last <= '0;
    else if(s_enable_int) r_last <= s_last;

  ///////////////////////////////////////////////
  // 6. Output mux
  ///////////////////////////////////////////////
  always_comb begin : output_cproc
    if(s_enable_int) begin
      s_pw_data_ready = (r_state == E_NO_DATA_STORED) || i_pw_data_ready;
      o_pw_data_valid = s_output_valid;
      o_pw_data = s_interleaved_output;
      o_pw_last = r_last;
    end else begin
      s_pw_data_ready = i_pw_data_ready;
      o_pw_data_valid = r_pw_data_valid;
      o_pw_data = r_pw_data;
      o_pw_last = r_pw_last;
    end
  end : output_cproc


endmodule : mvm_int16_interleaver
