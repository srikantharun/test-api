// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner:       Stefan Mach <stefan.mach@axelera.ai>
//              Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// DWPU data path channel, taking commands from the DPcmd stream, and processing data from the data
/// stream to produce a new output stream.
///
module dwpu_dp_channel #(
  /// Number of scratchpad registers
  parameter int unsigned NumSpRegs = dwpu_pkg::NUM_SP_REGS,
  /// Number of weight buffer registers
  parameter int unsigned NumWbRegs = dwpu_pkg::NUM_WB_REGS,
  /// Number of compute tree operands
  parameter int unsigned NumOperands = dwpu_pkg::NUM_OPERANDS,
  /// Number of pipeline stages
  parameter int unsigned NumPipeStages = dwpu_pkg::NUM_PIPELINE_STAGES,
  /// Datapath command type
  parameter type dwpu_dp_command_t = dwpu_pkg::dwpu_dp_command_t,
  /// Data type for the input data
  parameter type data_inp_t = dwpu_pkg::input_t,
  /// Data type for the computed output data
  parameter type data_oup_t = dwpu_pkg::output_t
)(
  /// Clock, positive edge triggered
  input wire i_clk,
  // doc async
  /// Asyncronous reset, active low
  input wire i_rst_n,
  // doc sync i_clk
  /// Load signal for the data pipeline registers, handshaking handled centrally for all channels.
  input logic [NumPipeStages-1:0] i_pipe_load,
  /// Datapath command to compute
  input dwpu_dp_command_t i_command, // ASO-UNUSED_INPUT : Some fields of the command are not needed. Reserved and last push is handled earlier.
  /// Datapath command channel performs an transaction
  input logic i_transaction,
  /// Input data
  input data_inp_t i_data,
  /// Computed result output
  output data_oup_t o_data,
  // doc quasi_static
  /// Static configuration that image data is signed.
  input logic i_signed_img,
  /// Static configuration that weight data is signed.
  input logic i_signed_wgt
);

  /////////////////////////////////
  // Assert the parameterization //
  /////////////////////////////////

  if (NumSpRegs < 8)   $fatal(1, "Parameter: 'NumSpRegs' has to be at least 8; is: %d", NumSpRegs);
  if (NumWbRegs < 8)   $fatal(1, "Parameter: 'NumWbRegs' has to be at least 8; is: %d", NumWbRegs);
  if (NumOperands < 3) $fatal(1, "Parameter: 'NumOperands' has to be at least 3; is: %d", NumWbRegs);

  if (NumPipeStages < 2) $fatal(1, "Parameter: 'NumPipeStages' has to be at least 2; is: %d", NumPipeStages);

  /////////////////////////////////////
  // Derived parameters and typedefs //
  /////////////////////////////////////
  localparam int unsigned ISelWidth = cc_math_pkg::index_width(NumSpRegs);
  localparam int unsigned WSelWidth = cc_math_pkg::index_width(NumWbRegs);

  typedef logic [ISelWidth-1:0] i_sel_t;
  typedef logic [WSelWidth-1:0] w_sel_t;

  // Switchable signed/unsigned datapath requires MAC data to be 1 bit wider and signed
  typedef logic signed [$bits(data_inp_t):0] data_mac_t;
  typedef logic signed [$bits(data_oup_t):0] data_mac_result_t;


  /////////////////////////////////
  // The shifting state pointers //
  /////////////////////////////////

  // Shift offset for the scratchpad registers
  // Load when channel is loaded, handshake will propagate always!
  // The sp regs 0 and 1 are special
  i_sel_t sp_shift_pointer_q, sp_shift_pointer_d;
  assign sp_shift_pointer_d = (sp_shift_pointer_q == i_sel_t'(0)) ?
      i_sel_t'(NumSpRegs-32'd3) : i_sel_t'(sp_shift_pointer_q - 1);

  logic sp_shift_pointer_load;
  assign sp_shift_pointer_load = i_command.op_desc.shift_sp & i_transaction;

  // Shift offset for the weigth buffer register
  w_sel_t wb_shift_pointer_q, wb_shift_pointer_d;
  assign wb_shift_pointer_d = (wb_shift_pointer_q == w_sel_t'(0)) ?
      w_sel_t'(NumWbRegs-32'd1) : w_sel_t'(wb_shift_pointer_q - 1);

  logic wb_shift_pointer_load;
  assign wb_shift_pointer_load = i_command.op_desc.shift_wb & i_transaction;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                   sp_shift_pointer_q <= i_sel_t'(0);
    else if (sp_shift_pointer_load) sp_shift_pointer_q <= sp_shift_pointer_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                   wb_shift_pointer_q <= w_sel_t'(0);
    else if (wb_shift_pointer_load) wb_shift_pointer_q <= wb_shift_pointer_d;
  end

  ///////////////////
  // Weight Buffer //
  ///////////////////

  data_inp_t [NumWbRegs-1:0] wb_q;
  // Onehot decoded shift pointer and ff enable signal
  logic [NumWbRegs-1:0] wb_decode;
  logic [NumWbRegs-1:0] wb_enable;

  // Insert value at wb0, that designation depends on the state of sb_shift_offset
  assign wb_decode = (NumWbRegs)'(1) << wb_shift_pointer_d;

  // Generate weight buffer regs
  for (genvar i = 0; unsigned'(i) < NumWbRegs; ++i) begin : gen_wb_regs
    // Set the corresponding enable bit
    assign wb_enable[i] = wb_decode[i] & i_command.op_desc.shift_wb & i_transaction;
    // WB regs fed directly from data input
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)          wb_q[i] <= '0;
      else if (wb_enable[i]) wb_q[i] <= i_data;
    end
  end

  ////////////////
  // Scratchpad //
  ////////////////

  data_inp_t [NumSpRegs-1:0] sp_q;
  // Onehot decoded shift pointer and ff enable signal
  logic [NumSpRegs-1:0] sp_decode;
  logic [NumSpRegs-1:0] sp_enable;

  // Insert value at sp2, that designation depends on the state of sb_shift_offset
  assign sp_decode = (NumSpRegs)'(1) << i_sel_t'(sp_shift_pointer_d + i_sel_t'(2));

  // Generate scratchpad regs
  for (genvar i = 0; unsigned'(i) < NumSpRegs; ++i) begin : gen_sp_regs
    // Set the corresponding enable bit
    assign sp_enable[i] = sp_decode[i] & i_command.op_desc.shift_sp & i_transaction;

    if (i == 0) begin : gen_sp_0
      // sp0 is always the absorbing element of the operation!
      always_comb begin : assign_sp_0
        unique case (i_command.op_desc.opcode)
          dwpu_pkg::MAX: sp_q[i] = data_inp_t'(i_signed_img << ($bits(data_inp_t) - 1));
          dwpu_pkg::MIN: sp_q[i] = data_inp_t'(~(i_signed_img << ($bits(data_inp_t) - 1)));
          default:       sp_q[i] = data_inp_t'(0);
        endcase
      end
    end else if (i == 1) begin : gen_sp_1
      // sp1 is always the current input data
      assign sp_q[i] = i_data;
    end else begin : gen_sp_reg
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n)          sp_q[i] <= '0;
        else if (sp_enable[i]) sp_q[i] <= i_data;
      end
    end
  end

  ///////////////////////////
  // Image Value selection //
  ///////////////////////////

  data_mac_t [NumOperands-1:0] image_values_q;

  for (genvar i = 0; unsigned'(i) < NumOperands; ++i) begin : gen_image_value_mux
    // Adapted select from the current shift pointer offset
    // Actual select is special depending if it is 0 or 1
    i_sel_t sp_select;

    // Addition is used multiple times, optimized for datapath extraction
    logic [ISelWidth:0] sum_i_sel_sp_shift_pointer;
    assign sum_i_sel_sp_shift_pointer = i_command.i_sel[i] + sp_shift_pointer_q;

    // Think about the modulo, probably has to be NumSpRegs-2
    always_comb begin
      // No modulo needed if we stay inside the range
      sp_select = i_sel_t'(sum_i_sel_sp_shift_pointer);
      if (i_command.i_sel[i] inside {i_sel_t'(0), i_sel_t'(1)}) begin
        // No shift pointer as these two regs are always accessed
        sp_select = i_command.i_sel[i];
      end else if (sum_i_sel_sp_shift_pointer >= NumSpRegs) begin
        // Use the modulo if the pointer would point outside the range
        sp_select = i_sel_t'(sum_i_sel_sp_shift_pointer - (NumSpRegs - 2));
      end
    end

    // I regs fed from any scratchpad reg --> mux and sign extension
    data_inp_t   scrathpad_data;
    data_mac_t image_value_d;
    assign scrathpad_data = sp_q[sp_select];
    assign image_value_d = signed'({i_signed_img & scrathpad_data[$bits(data_inp_t)-1], scrathpad_data});

    // DFFL: D-Flip-Flop, load enable
    always_ff @(posedge i_clk) begin
      if (i_pipe_load[0]) image_values_q[i] <= image_value_d;
    end
  end


  ////////////////////////////
  // Weight Value selection //
  ////////////////////////////

  data_mac_t [NumOperands-1:0] weight_values_q;

  for (genvar i = 0; unsigned'(i) < NumOperands; ++i) begin : gen_weight_value_mux
    // Adapted select from the current shift offset pointer.
    w_sel_t wb_select;

    // Addition is used multiple times, optimzed for datapath extraction
    logic [WSelWidth:0] sum_w_sel_wb_shift_pointer;
    assign sum_w_sel_wb_shift_pointer = i_command.w_sel[i] + wb_shift_pointer_q;

    always_comb begin : proc_assign_wb_select
      if (sum_w_sel_wb_shift_pointer >= NumWbRegs) begin
        // Use the modulo if we go outside the pointer range
        wb_select = w_sel_t'(sum_w_sel_wb_shift_pointer - NumWbRegs);
      end else begin
        wb_select = w_sel_t'(sum_w_sel_wb_shift_pointer);
      end
    end

    // W regs fed from any weight buffer reg --> mux and sign extension
    data_inp_t   weightbuffer_data;
    data_mac_t weight_value_d;
    assign weightbuffer_data = wb_q[wb_select];
    assign weight_value_d    = (i_command.op_desc.opcode == dwpu_pkg::SUM) ?
        data_mac_t'(1'b1) : signed'({i_signed_wgt & weightbuffer_data[$bits(data_inp_t)-1], weightbuffer_data});

    // DFFL: D-Flip-Flop, load enable
    always_ff @(posedge i_clk) begin
      if (i_pipe_load[0]) weight_values_q[i] <= weight_value_d;
    end
  end

  // Have the first pipeline stage after the image and weight selection
  // The opcode is needed after the first stage, so save it.
  dwpu_pkg::opcode_e opcode_q;
  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)            opcode_q <= dwpu_pkg::SOP;
    else if (i_pipe_load[0]) opcode_q <= i_command.op_desc.opcode;
  end

  //////////////
  // MAC Tree //
  //////////////

  data_mac_result_t mac_result;

  if (NumOperands == 9) begin : gen_manual_sop_9ops
    // Do an explicit SOP expression for 9 operands - this will use redundant number formats and
    // only one single carry chain. See Synopsys coding guidelines for datapath synthesis for more
    // information about datapath extraction
    always_comb mac_result = (image_values_q[0] * weight_values_q[0])
                           + (image_values_q[1] * weight_values_q[1])
                           + (image_values_q[2] * weight_values_q[2])
                           + (image_values_q[3] * weight_values_q[3])
                           + (image_values_q[4] * weight_values_q[4])
                           + (image_values_q[5] * weight_values_q[5])
                           + (image_values_q[6] * weight_values_q[6])
                           + (image_values_q[7] * weight_values_q[7])
                           + (image_values_q[8] * weight_values_q[8]);

  end else begin : gen_simple_mac_chain
    // Use generative approach to build a simple MAC chain for other sizes
    data_mac_result_t [NumOperands-1:0] tmp_mac_results;
    // Simple chain of MACs
    assign tmp_mac_results[0] = image_values_q[0] * weight_values_q[0];
    for (genvar i = 1; unsigned'(i) < NumOperands; ++i) begin : gen_mac_chain
      assign tmp_mac_results[i] = (image_values_q[i] * weight_values_q[i]) + tmp_mac_results[i-1];
    end
    assign mac_result = tmp_mac_results[NumOperands-1];
  end


  //////////////////
  // Min/Max Tree //
  //////////////////

  data_mac_result_t cmp_result;
  logic  min_op;
  assign min_op = (opcode_q == dwpu_pkg::MIN);

  if (NumOperands == 9) begin : gen_manual_cmp_9ops
    // Do an explicit tree topology for 9 operands
    data_mac_t       t_0;
    data_mac_t [3:0] t_1;
    data_mac_t [1:0] t_2;
    assign t_0 = (image_values_q[0] > image_values_q[1]) ?
           (min_op ? image_values_q[1] : image_values_q[0])
         : (min_op ? image_values_q[0] : image_values_q[1]);
    assign t_1[0] = (t_0 > image_values_q[2]) ?
           (min_op ? image_values_q[2] : t_0)
         : (min_op ? t_0 : image_values_q[2]);
    assign t_1[1] = (image_values_q[3] > image_values_q[4]) ?
           (min_op ? image_values_q[4] : image_values_q[3])
         : (min_op ? image_values_q[3] : image_values_q[4]);
    assign t_1[2] = (image_values_q[5] > image_values_q[6]) ?
           (min_op ? image_values_q[6] : image_values_q[5])
         : (min_op ? image_values_q[5] : image_values_q[6]);
    assign t_1[3] = (image_values_q[7] > image_values_q[8]) ?
           (min_op ? image_values_q[8] : image_values_q[7])
         : (min_op ? image_values_q[7] : image_values_q[8]);
    assign t_2[0] = (t_1[0] > t_1[1]) ?
           (min_op ? t_1[1] : t_1[0])
         : (min_op ? t_1[0] : t_1[1]);
    assign t_2[1] = (t_1[2] > t_1[3]) ?
           (min_op ? t_1[3] : t_1[2])
         : (min_op ? t_1[2] : t_1[3]);
    assign cmp_result = (t_2[0] > t_2[1]) ? (min_op ? t_2[1] : t_2[0]) : (min_op ? t_2[0] : t_2[1]);

  end else begin : gen_simple_cmp_chain
    // Use generative approach to build a simple cmp chain for other sizes
    data_mac_t [NumOperands-1:0] tr;
    // Simple chain of comparators & muxes
    assign tr[0] = image_values_q[0];
    for (genvar i = 1; i < NumOperands; ++i) begin : gen_link
      assign tr[i] = (image_values_q[i] > tr[i-1]) ? (min_op ? tr[i-1] : image_values_q[i]) : (min_op ? image_values_q[i] : tr[i-1]);
    end
    assign cmp_result = tr[NumOperands-1];
  end

  ///////////////////////////////
  // Output pipeline registers //
  // Relies on retiming        //
  ///////////////////////////////

  // One off the pipeline stages is before the arithmetic operations
  data_oup_t [NumPipeStages-1:1] pipe_data_q, pipe_data_d;

  for (genvar i = 1; unsigned'(i) < NumPipeStages; i++) begin : gen_pipeline
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)            pipe_data_q[i] <= '0;
      else if (i_pipe_load[i]) pipe_data_q[i] <= pipe_data_d[i];
    end

    // Connect the pipeline registers
    if (i == 1) begin : gen_inp
      assign pipe_data_d[i] = (opcode_q inside {dwpu_pkg::SOP, dwpu_pkg::SUM}) ?
          data_oup_t'(mac_result) : data_oup_t'(cmp_result);
    end else begin : gen_con
      assign pipe_data_d[i] = pipe_data_q[i-1];
    end
  end

  assign o_data = pipe_data_q[NumPipeStages-1];

endmodule
