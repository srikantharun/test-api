// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// The deinterleaver is placed before par2bser in order to split all the low-bytes to ifd0
//   and all the high-bytes to ifd2.
// The module is only active when INT16 inputs are enabled, it is passthrough otherwise.
// When enabled, the module only reads from ifd0. Ifd2 is ignored.
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module mvm_int16_deinterleaver #(
  parameter int unsigned DATA_W = 8,
  parameter int unsigned PW_LEN = 64
) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic i_enable,

  // Input IFD0 - parallel interleaved highs and lows
  input  logic i_ifd0_tvalid,
  output logic o_ifd0_tready,
  input  logic [PW_LEN-1:0] [DATA_W-1:0] i_ifd0_pw_data,

  // Input IFD2 - for passthrough if disabled
  input  logic i_ifd2_tvalid,
  output logic o_ifd2_tready,
  input  logic [PW_LEN-1:0] [DATA_W-1:0] i_ifd2_pw_data,

  // Output IFD0 - low bytes
  output logic o_ifd0_tvalid,
  input  logic i_ifd0_tready,
  output logic [PW_LEN-1:0] [DATA_W-1:0] o_ifd0_pw_data,

  // Output IFD2 - high bytes
  output logic o_ifd2_tvalid,
  input  logic i_ifd2_tready,
  output logic [PW_LEN-1:0] [DATA_W-1:0] o_ifd2_pw_data
);

  logic write_enable;
  logic read_enable;

  logic [1:0] [PW_LEN/2-1:0] [DATA_W-1:0] s_input_deinterleaved;
  logic                                   r_stored_valid        , s_stored_valid;
  logic [1:0] [PW_LEN/2-1:0] [DATA_W-1:0] r_stored_deinterleaved, s_stored_deinterleaved;
  logic [1:0] [PW_LEN  -1:0] [DATA_W-1:0] s_output_deinterleaved;

  logic       r_inp_beat_count, s_inp_beat_count;
  logic [1:0] r_ifd_beat_count, s_ifd_beat_count;

  logic s_ifd0_tvalid, s_ifd2_tvalid;

  ///////////////////////////////////////////////
  // 1. Deinterleave input data
  ///////////////////////////////////////////////

  always_comb begin : deinterleave_cproc
    // s_input_deinterleaved[0][0] <- i_ifd0_pw_data[0]
    // s_input_deinterleaved[0][1] <- i_ifd0_pw_data[2]
    // s_input_deinterleaved[0][2] <- i_ifd0_pw_data[4]
    // ...
    // s_input_deinterleaved[1][0] <- i_ifd0_pw_data[1]
    // s_input_deinterleaved[1][1] <- i_ifd0_pw_data[3]
    // s_input_deinterleaved[1][2] <- i_ifd0_pw_data[5]
    // ...
    foreach(s_input_deinterleaved[i,j])
      s_input_deinterleaved[i][j] = i_ifd0_pw_data[i+(j*2)];
  end : deinterleave_cproc

  ///////////////////////////////////////////////
  // 2. Wait for 2 beats, store data of the first beat
  ///////////////////////////////////////////////

  // Write if
  // - incoming data valid
  // - and not full
  // Note: there is never a need to simulateneously read and write
  assign write_enable = i_enable & i_ifd0_tvalid & ~r_stored_valid;
  // Read if
  // - enough data to send (incoming data valid and full)
  // - and, both par2bsers advanced
  assign read_enable  = i_enable & r_stored_valid & (s_ifd_beat_count == {2{r_inp_beat_count}});

  always_comb begin : storage_cproc
    if(write_enable) begin
      s_stored_valid         = 1'b1;
      s_stored_deinterleaved = s_input_deinterleaved;
      s_inp_beat_count       = ~r_inp_beat_count;
    end else if(read_enable) begin
      s_stored_valid         = 1'b0;
      s_stored_deinterleaved = r_stored_deinterleaved;
      s_inp_beat_count       = r_inp_beat_count;
    end else begin
      s_stored_valid         = r_stored_valid;
      s_stored_deinterleaved = r_stored_deinterleaved;
      s_inp_beat_count       = r_inp_beat_count;
    end
  end : storage_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)      r_stored_valid <= 1'b0;
    else if(i_enable) r_stored_valid <= s_stored_valid;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)      r_inp_beat_count <= 1'b0;
    else if(i_enable) r_inp_beat_count <= s_inp_beat_count;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)            r_stored_deinterleaved <= '0;
    else if(s_stored_valid) r_stored_deinterleaved <= s_stored_deinterleaved;

  ///////////////////////////////////////////////
  // 3. Calculate outputs
  ///////////////////////////////////////////////
  always_comb begin
    s_ifd2_tvalid       = (r_ifd_beat_count[1] ^ r_inp_beat_count) & i_ifd0_tvalid;
    s_ifd_beat_count[1] = (s_ifd2_tvalid & i_ifd2_tready) ? ~r_ifd_beat_count[1] : r_ifd_beat_count[1];

    s_ifd0_tvalid       = (r_ifd_beat_count[0] ^ r_inp_beat_count) & i_ifd0_tvalid;
    s_ifd_beat_count[0] = (s_ifd0_tvalid & i_ifd0_tready) ? ~r_ifd_beat_count[0] : r_ifd_beat_count[0];
  end

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)      r_ifd_beat_count <= '0;
    else if(i_enable) r_ifd_beat_count <= s_ifd_beat_count;

  always_comb foreach(s_output_deinterleaved[i]) s_output_deinterleaved[i] = i_enable ? {s_input_deinterleaved[i], r_stored_deinterleaved[i]} : '0;

  ///////////////////////////////////////////////
  // 4. Drive outputs, bypass if not i_enable
  ///////////////////////////////////////////////

  always_comb begin : output_cproc
    if(i_enable) begin
      // Input IFD0 - parallel interleaved highs and lows
      o_ifd0_tready  = (~r_stored_valid) | (s_ifd_beat_count == {2{r_inp_beat_count}});
      // Input IFD2 - needed to progress command stream
      o_ifd2_tready  = (~r_stored_valid) | (s_ifd_beat_count == {2{r_inp_beat_count}});
      // Output IFD0 - low bytes
      o_ifd0_tvalid  = s_ifd0_tvalid;
      o_ifd0_pw_data = s_output_deinterleaved[0];
      // Output IFD2 - high bytes
      o_ifd2_tvalid  = s_ifd2_tvalid;
      o_ifd2_pw_data = s_output_deinterleaved[1];
    end else begin
      o_ifd0_tready  = i_ifd0_tready;
      o_ifd2_tready  = i_ifd2_tready;
      o_ifd0_tvalid  = i_ifd0_tvalid;
      o_ifd0_pw_data = i_ifd0_pw_data;
      o_ifd2_tvalid  = i_ifd2_tvalid;
      o_ifd2_pw_data = i_ifd2_pw_data;
    end
  end : output_cproc

`ifndef SYNTHESIS
  if (PW_LEN%2) $fatal("PW_LEN must be a multiple of 2");
`endif

endmodule : mvm_int16_deinterleaver
