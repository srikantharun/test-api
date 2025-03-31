// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// The mvm_imc_bank_acc_combiner instantiates the mvm accumulators and all logic required
//   for merging results wrt different precision modes.
// INT8wINT8i: accumulator in 8-beat bursts, splitter bypassed, column merger bypassed
// INT8wINT16i: accumulator in 16-beat bursts, splitter enabled, column merger bypassed
// INT16wINT8i: accumulator in 8-beat bursts, splitter bypassed, column merger enabled
// INT16wINT16i: accumulator in 16-beat burts, splitter bypassed, column merger enabled
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module mvm_imc_bank_acc_combiner #(
  localparam int unsigned N_CHANNELS = 2,

  parameter int unsigned IMC_DATA_WD = 19,
  parameter int unsigned ACC_DATA_WD = 34,
  parameter int unsigned COMB_DATA_WD = 26
) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic i_weight_precision,
  input  logic i_input_precision,

  input  logic [3:0] ctrl_acc_shift_pos_i,
  input  logic       ctrl_acc_group_enable_i,
  input  logic       ctrl_acc_output_enable_i,
  input  logic       ctrl_acc_clear_i,
  input  logic       ctrl_acc_signed_weights,
  input  logic       ctrl_acc_signed_inputs,

  input  logic [N_CHANNELS-1:0] [IMC_DATA_WD -1:0] i_imc_data,
  output logic [N_CHANNELS-1:0] [COMB_DATA_WD-1:0] o_comb_data
);

  localparam int unsigned MERGE_DATA_WD = ACC_DATA_WD+8;
  localparam int unsigned MERGE_PADDING_WD = COMB_DATA_WD*N_CHANNELS - MERGE_DATA_WD;

  localparam int unsigned SPLIT_STORE_WD = ACC_DATA_WD-COMB_DATA_WD;

  typedef enum logic [1:0] {
    E_PASSTHROUGH  = 2'b00, // INT8 inputs, INT8 weights. Each IMC + ACC column combo produces a valid result of max 26b every 8 cycles.
                            //   Result can directly be mapped to 26b distributed mux wires by dropping unused bits 27-33 of each.
    E_SPLITTER     = 2'b01, // INT16 inputs, INT8 weights. Each IMC + ACC column combo produces a valid results of max 34b every 16 cycles.
                            //   Results need to be send out over 2 cycles since 26b mux cannot accept all 34b at once. Output is sequentialised.
    E_COLUMN_MERGE = 2'b10  // INT8/INT16 inputs, INT16 weights.
                            //   The output of two neighboring IMC + ACC column combos need to be added with the msb one shifted by 8 bit.
                            //   This produces only half of the 'normal' number of valid results per cycle at a max precision of 41b.
                            //   Those 41b can be split over 2x26b of the distributed muxes. No sequentialising required.
  } acc_combine_method_e;

  // DP ctrl
  acc_combine_method_e s_combine_method;
  logic s_split_enable;
  logic s_merge_enable;
  // Accumulator outputs
  logic [N_CHANNELS-1:0] s_acc_valid;
  logic [N_CHANNELS-1:0] [ACC_DATA_WD -1:0] s_acc_data;
  // Splitter - upper beat storage
  logic s_split_store_valid, r_split_store_valid;
  logic [N_CHANNELS-1:0] [SPLIT_STORE_WD-1:0] s_split_store, r_split_store;
  // Splitter output
  logic [N_CHANNELS-1:0] [COMB_DATA_WD-1:0] s_split_data;
  // Column merge
  logic [MERGE_DATA_WD-1:0] s_merged_acc;

  always_comb
         if(~i_weight_precision & ~i_input_precision) s_combine_method = E_PASSTHROUGH;
    else if(~i_weight_precision &  i_input_precision) s_combine_method = E_SPLITTER;
    else if( i_weight_precision                     ) s_combine_method = E_COLUMN_MERGE;
    else                                              s_combine_method = E_PASSTHROUGH;

  assign s_split_enable = (s_combine_method == E_SPLITTER);
  assign s_merge_enable = (s_combine_method == E_COLUMN_MERGE);

  ///////////////////////////////////////////////
  // 1. Input accumulation
  ///////////////////////////////////////////////

  for (genvar g = 0; g < N_CHANNELS; g++) begin : gen_acc_pair
    mvm_acc #(
      .INP_WIDTH(IMC_DATA_WD),
      .ACC_WIDTH(ACC_DATA_WD)
    ) u_mvm_acc (
      .i_clk,
      .i_rst_n,
      .ctrl_acc_shift_pos_i,
      .ctrl_acc_group_enable_i,
      .ctrl_acc_output_enable_i,
      .ctrl_acc_clear_i,
      .ctrl_acc_signed_weights,
      .ctrl_acc_signed_inputs,
      .ctrl_acc_input_precision(i_input_precision),
      .imc_to_accum_i(i_imc_data[g]),
      .accum_valid_o(s_acc_valid[g]),
      .accum_to_buf_o(s_acc_data[g])
    );
  end : gen_acc_pair

  ///////////////////////////////////////////////
  // 2. (Path A) Splitter (int8wint16i)
  // With bypass for (int8wint8i)
  ///////////////////////////////////////////////

  always_comb begin : s_split_store_cproc
    if(~r_split_store_valid & (|s_acc_valid) & s_split_enable) begin
      // Write split store
      s_split_store_valid = 1'b1;
      foreach(s_split_store[i]) s_split_store[i] = s_acc_data[i][ACC_DATA_WD-1:COMB_DATA_WD];
    end else if(r_split_store_valid & s_split_enable) begin
      // Read split store
      s_split_store_valid = 1'b0;
      s_split_store = r_split_store;
    end else begin
      s_split_store_valid = r_split_store_valid;
      s_split_store = r_split_store;
    end
  end : s_split_store_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)            r_split_store_valid <= 1'b0;
    else if(s_split_enable) r_split_store_valid <= s_split_store_valid;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if(~i_rst_n)                 r_split_store <= '0;
    else if(s_split_store_valid) r_split_store <= s_split_store;

  always_comb begin : s_split_mux
    if(s_split_enable) begin
      // 2nd beat: Send pending upper bits, sign extended
      if(r_split_store_valid) foreach(s_split_data[i]) s_split_data[i] = {{COMB_DATA_WD{r_split_store[i][SPLIT_STORE_WD-1]}}, r_split_store[i]};
      // 1st beat: Send immediate lower bits
      else                    foreach(s_split_data[i]) s_split_data[i] = s_acc_data[i][COMB_DATA_WD-1:0];
    end else begin
      // Split disabled assumes int8wint8i path, just discard bits 27-34
      foreach(s_split_data[i]) s_split_data[i] = s_acc_data[i][COMB_DATA_WD-1:0];
    end
  end : s_split_mux

  ///////////////////////////////////////////////
  // 2. (Path B) Column merge (for int16w with any input precision)
  ///////////////////////////////////////////////
  // The upper channel is left-shifted 8 bits
  // And summed with the sign-extended lower channel
  // Tied to 0 if merge disabled
  // TODO: possibly need to sequentialize this 42-bit adder into 2 clock cycles
  assign s_merged_acc = {MERGE_DATA_WD{s_merge_enable}} & {s_acc_data[1], 8'd0} + { {8{s_acc_data[0][ACC_DATA_WD-1]}}, s_acc_data[0] };

  ///////////////////////////////////////////////
  // 3. Output mux
  ///////////////////////////////////////////////
  always_comb begin
    if(s_merge_enable) begin
      o_comb_data[1] = { {MERGE_PADDING_WD{s_merged_acc[MERGE_DATA_WD-1]}}, s_merged_acc[MERGE_DATA_WD-1:COMB_DATA_WD] };
      o_comb_data[0] = s_merged_acc[COMB_DATA_WD-1:0];
    end else begin
      o_comb_data = s_split_data;
    end
  end

endmodule : mvm_imc_bank_acc_combiner
