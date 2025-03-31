// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Translation layer between CVA6V's tc_sram and our tc_sram - ASIC only
//
// Additional parameters:
// - impl_in_t:   Implementation-related inputs, such as pseudo-static macro configuration inputs.
// - impl_out_t:  Implementation-related outputs. This model only supports driving static values.
//
// Additional ports:
// - `impl_i`:  Implementation-related inputs
// - `impl_o`:  Implementation-related outputs

module cva6v_tc_sram_impl #(
  parameter int unsigned NumWords     = 32'd1024, // Number of Words in data array
  parameter int unsigned DataWidth    = 32'd128,  // Data signal width
  parameter int unsigned ByteWidth    = 32'd8,    // Width of a data byte
  parameter int unsigned NumPorts     = 32'd2,    // Number of read and write ports
  parameter int unsigned Latency      = 32'd1,    // Latency when the read data is available
  parameter              SimInit      = "none",   // Simulation initialization
  parameter bit          PrintSimCfg  = 1'b0,     // Print configuration
  parameter              ImplKey      = "none",   // Reference to specific implementation
  parameter type         impl_in_t    = logic,    // Type for implementation inputs
  parameter type         impl_out_t   = logic,    // Type for implementation outputs
  parameter impl_out_t   ImplOutSim   = 'X,       // Implementation output in simulation
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  localparam int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  localparam int unsigned TrueByteWidth = ((DataWidth / ByteWidth) * ByteWidth == DataWidth) ? ByteWidth : 32'd1,
  localparam int unsigned BeWidth   = DataWidth / TrueByteWidth,
  localparam type         addr_t    = logic [AddrWidth-1:0],
  localparam type         data_t    = logic [DataWidth-1:0],
  localparam type         be_t      = logic [BeWidth-1:0]
) (
  input  logic                 clk_i,      // Clock
  input  logic                 rst_ni,     // Asynchronous reset active low
  // implementation-related IO
  input  impl_in_t             impl_i,
  output impl_out_t            impl_o,
  // input ports
  input  logic  [NumPorts-1:0] req_i,      // request
  input  logic  [NumPorts-1:0] we_i,       // write enable
  input  addr_t [NumPorts-1:0] addr_i,     // request address
  input  data_t [NumPorts-1:0] wdata_i,    // write data
  input  be_t   [NumPorts-1:0] be_i,       // write byte enable
  // output ports
  output data_t [NumPorts-1:0] rdata_o     // read data
);

  localparam LocalImplKey = (vendor_cva6v_pkg::USE_LVT_MEMS && !(NumWords == 32 && DataWidth == 128)) ? "HS_LVT" : "HS_RVT";

  if(NumPorts == 2) begin : gen_vrf_mem
    // VRF - 1rp_1wp
    // Note: Input CG & silencing logic is disabled, power improvement is insignificant
    axe_tcl_ram_1rp_1wp #(
      .NumWords              (NumWords),
      .DataWidth             (DataWidth),
      .ByteWidth             (TrueByteWidth),
      .ReadLatency           (Latency),
      .ImplKey               (LocalImplKey),
      .impl_inp_t            (impl_in_t),
      .impl_oup_t            (impl_out_t),
      .FunctionalClkGate     (1'b0),
      .FunctionalInputSilence(1'b0)
    ) u_tc_sram (
      .i_wr_clk  (clk_i),
      .i_wr_rst_n(rst_ni),
      .i_wr_req  (req_i[1]),
      .i_wr_addr (addr_i[1]),
      .i_wr_data (wdata_i[1]),
      .i_wr_mask (be_i[1]),

      .i_rd_clk  (clk_i),
      .i_rd_rst_n(rst_ni),
      .i_rd_req  (req_i[0]),
      .i_rd_addr (addr_i[0]),
      .o_rd_data (rdata_o[0]),

      .i_impl    (impl_i),
      .o_impl    (impl_o)
    );
  end else if (NumPorts == 1) begin : gen_cva6_mem
    // CVA6 d/i cache/tag
    // Note: Input CG & silencing logic is disabled, power improvement is insignificant
    axe_tcl_ram_1rwp #(
      .NumWords              (NumWords),
      .DataWidth             (DataWidth),
      .ByteWidth             (TrueByteWidth),
      .ReadLatency           (Latency),
      .ImplKey               (LocalImplKey),
      .impl_inp_t            (impl_in_t),
      .impl_oup_t            (impl_out_t),
      .FunctionalClkGate     (1'b0),
      .FunctionalInputSilence(1'b0)
    ) u_tc_sram (
      .i_clk      (clk_i),
      .i_rst_n    (rst_ni),
      .i_req      (req_i),
      .i_addr     (addr_i),
      .i_wr_enable(we_i),
      .i_wr_data  (wdata_i),
      .i_wr_mask  (be_i),
      .o_rd_data  (rdata_o),
      .i_impl     (impl_i),
      .o_impl     (impl_o)
    );
  end

`ifndef SYNTHESIS
  if (!(NumPorts inside {1,2})) $fatal(1, "Parameter: 'NumPorts' must be 1 or 2");
`endif

endmodule
