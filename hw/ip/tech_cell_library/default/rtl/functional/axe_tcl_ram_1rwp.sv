// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Single Port (1 * RW) Memory
///
module axe_tcl_ram_1rwp #(
  /// Number of Words of the Data Array `addr_t = logic [$clog2(NumWords)-1:0]`
  parameter int unsigned NumWords    = 16,
  /// The Data Width of each Individual Word in Bits
  parameter int unsigned DataWidth   = 16,
  /// The Byte Width (in Bits) which will patition write data. MUST be a divisor of DataWidth!
  parameter int unsigned ByteWidth   = 1,
  /// The Latency for READ requests to the Memory in Cycles
  parameter int unsigned ReadLatency = 1,

  /// Adds a clock gate which enables the clock on request
  parameter bit FunctionalClkGate = 1'b1,
  /// Adds functional input silencing depending on request
  parameter bit FunctionalInputSilence = 1'b1,

  /// A technology specific key to choose between similar shaped memories
  parameter              ImplKey    = "default",
  /// parameterized type for implementation specific inputs
  parameter type         impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// parameterized type for implementation specific outputs
  parameter type         impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,

  /// Derived parameter: Address type
  localparam type addr_t   = logic[$clog2(NumWords)-1:0],
  /// Derived Parameter: Payload Data Type
  localparam type data_t   = logic[DataWidth-1:0],
  /// Derived Paramter: Byte Enable vector
  localparam type enable_t = logic[(DataWidth/ByteWidth)-1:0]
)(
  /// Clock, positive edge triggered
  input  wire       i_clk,
  /// Asynchronous reset, active low
  input  wire       i_rst_n,

  /// Request either read or write to the array, active high
  input  logic      i_req,
  /// The Word address of the request
  input  addr_t     i_addr,
  /// The request represents a write
  /// `0`: Read  request
  /// `1`: Write request
  input  logic      i_wr_enable,

  /// The write data payload
  input  data_t     i_wr_data,
  /// The write enable mask for the individual bytes
  input  enable_t   i_wr_mask,

  /// The read data payload. updates `Latency` cycles after the respective request.
  output data_t     o_rd_data,

  /// Implementation specific sideband inputs
  input  impl_inp_t i_impl,
  /// Implementation specific sideband outputs
  output impl_oup_t o_impl
);

  //////////////////////////
  // Parameter Validation //
  //////////////////////////
  if (NumWords <= 1)  $fatal(1, "Parameter: 'NumWords' has to be > 1;");
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' has to be > 0;");
  if (ByteWidth == 0) $fatal(1, "Parameter: 'ByteWidth' has to be > 0;");

  if (DataWidth % ByteWidth != 0) $fatal(1, "'DataWidth' has to be multiple of 'ByteWidth';");

  /////////////////////////////
  // Print the configuration //
  /////////////////////////////
`ifdef AXE_TCL_PRINT_CONFIG
  $info(
    "\n",
    "#################################################################################\n",
    "# 'axe_tcl_ram_1rwp' instantiated with the configuration:\n",
    "#   Number of words:   %d\n", NumWords,
    "#   Address width:     %d\n", $clog2(NumWords),
    "#   Data width:        %d\n", DataWidth,
    "#   Byte width:        %d\n", ByteWidth,
    "#   Byte enable width: %d\n", (DataWidth/ByteWidth),
    "#   Latency Cycles:    %d\n", ReadLatency,
    "#   ImplKey:          '%s'\n",  ImplKey,
    "#################################################################################"
  );
`endif

  ///////////////////////////////////////////////////////
  // Functional model just stubbs all sideband outputs //
  ///////////////////////////////////////////////////////
  always_comb o_impl = '0;

  /////////////////
  // The Memory! //
  /////////////////
  data_t memory_q[NumWords];

  /////////////////////
  // Write Moddeling //
  /////////////////////
  always_ff @(posedge i_clk) begin
    if (i_req && i_wr_enable) foreach (i_wr_mask[byte_index]) begin
      if (i_wr_mask[byte_index])
        memory_q[i_addr][byte_index*ByteWidth +: ByteWidth] <= i_wr_data[byte_index*ByteWidth +: ByteWidth];
    end
  end

  ////////////////////
  // Read Moddeling //
  ////////////////////
  // Note the index into the array at index zerom meand in the same cycle
  logic  read_request;
  addr_t read_address_q;
  data_t read_data_q[ReadLatency+1];
  logic  read_updated_q[ReadLatency+1];

  always_comb read_request      = i_req & ~i_wr_enable;
  always_comb read_data_q[0]    = read_request ? memory_q[i_addr] : memory_q[read_address_q];
  always_comb read_updated_q[0] = read_request;

  // Keep track of the last read address
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)         read_address_q <= addr_t'(0);
    else if(read_request) read_address_q <= i_addr;
  end

  for (genvar stage = 0; unsigned'(stage) < ReadLatency; stage++) begin : gen_read_stage
    // DFFR: D-Flip-Flop, asynchronous low reset
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) read_updated_q[stage+1] <= 1'b0;
      else          read_updated_q[stage+1] <= read_updated_q[stage];
    end

    // DFFL: D-Flip-Flop, load enable
    always_ff @(posedge i_clk) begin
      if (read_updated_q[stage]) read_data_q[stage+1] <= read_data_q[stage];
    end
  end

  always_comb o_rd_data = read_data_q[ReadLatency];

endmodule
