// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>

/// Constant provider as part of the ID/ISS pipe. Essentially a read-only memory, providing
/// independent read ports - synchronizing them must be done in the surrounding circuitry. MUXes
/// are located after the pipe to reduce the number of registers.
module dpu_dp_const
  import dpu_pkg::*;
#(
  parameter int unsigned NumPorts = 3
) (
  input wire i_clk,   // Clock
  input wire i_rst_n, // Reset active low

  // Read request ports
  input  const_sel_e [NumPorts-1:0] i_const_sel,      // Register read address
  input  logic       [NumPorts-1:0] i_const_sel_vld,
  output logic       [NumPorts-1:0] o_const_sel_rdy,

  // Read data ports
  output pw_dpu_fp_t [NumPorts-1:0] o_const_data,      // Output data
  output logic       [NumPorts-1:0] o_const_data_vld,
  input  logic       [NumPorts-1:0] i_const_data_rdy
);

  // Read Request Pipe
  // ==================
  const_sel_e [NumPorts-1:0] const_sel;

  // ID/ISS pipe the requests themselves to save on FF area -> MUX timing impacts ISS stage!
  // TODO(@stefan.mach): this was a spill reg, make sure stream_reg is enough!
  cc_stream_reg #(
    .data_t(const_sel_e)
  ) u_stream_reg[NumPorts-1:0] (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_valid(i_const_sel_vld),
    .o_ready(o_const_sel_rdy),
    .i_data (i_const_sel),
    .o_valid(o_const_data_vld),
    .i_ready(i_const_data_rdy),
    .o_data (const_sel)
  );

  // Read Data
  // ==========
  for (genvar i = 0; unsigned'(i) < NumPorts; ++i) begin : gen_const_mux
    always_comb begin : const_mux
      // Default assignment
      o_const_data[i] = PW_DPU_FP_ZERO;
      // Simple mux
      unique case (const_sel[i])
        CONST_ZERO:    o_const_data[i] = PW_DPU_FP_ZERO;
        CONST_ONE:     o_const_data[i] = PW_DPU_FP_ONE;
        CONST_NEGZERO: o_const_data[i] = PW_DPU_FP_NEGZERO;
        CONST_NEGONE:  o_const_data[i] = PW_DPU_FP_NEGONE;
        CONST_INF:     o_const_data[i] = PW_DPU_FP_INF;
        CONST_NEGINF:  o_const_data[i] = PW_DPU_FP_NEGINF;
        CONST_PI:      o_const_data[i] = PW_DPU_FP_PI;
        CONST_2PI:     o_const_data[i] = PW_DPU_FP_2PI;
        default:       ;
      endcase
    end
  end

endmodule
