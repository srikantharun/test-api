// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Single Port (1 * RW) Memory
///
/// Concrete macros for Europas sf5a implementation.
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

  logic rst_nc;
  always_comb rst_nc = i_rst_n; // ASO-UNUSED_VARIABLE: reset is not used
  logic impl_nc;
  always_comb impl_nc = (|i_impl.mcs) | i_impl.mcsw | (|i_impl.adme); // ASO-UNUSED_VARIABLE: mcs, mcsw, and adme are not used from impl anymore

  ////////////////////////////////////////////////////////
  // Power Optimization                                 //
  // https://git.axelera.ai/ai-pd-team/flow/-/issues/52 //
  ////////////////////////////////////////////////////////

  // The wires that will connect to the memories
  wire     clk;
  logic    chip_select_n;    // Macros are active low enabled
  addr_t   address;
  logic    wr_enable_n;      // Macros have active low write enable
  data_t   wr_data;
  enable_t wr_byte_enable_n; // Byte enable are active low

  if (FunctionalClkGate) begin : gen_clk_gate
    axe_tcl_clk_gating u_clk_gate_pwr (
      .i_clk,
      .i_en     (i_req),
      .i_test_en(i_impl.se),
      .o_clk    (clk)
    );
  end else begin : gen_direct_clk
    assign clk = i_clk;
  end

  always_comb chip_select_n = ~i_req;

  if (FunctionalInputSilence) begin : gen_input_silence
    always_comb address          =  i_req ?  i_addr      : addr_t'(0);
    always_comb wr_enable_n      =  i_req ? ~i_wr_enable : 1'b0;
    always_comb wr_data          =  i_req ?  i_wr_data   : data_t'(0);
    always_comb wr_byte_enable_n =  i_req ? ~i_wr_mask   : enable_t'(0);
  end else begin : gen_direct_input
    always_comb address          =  i_addr;
    always_comb wr_enable_n      = ~i_wr_enable;
    always_comb wr_data          =  i_wr_data;
    always_comb wr_byte_enable_n = ~i_wr_mask;
  end

  ///////////////////////////////////////////////////////////
  // All memories have bit enables instead of byte enables //
  // Convert them here                                     //
  ///////////////////////////////////////////////////////////

  data_t wr_bit_enable_n;
  always_comb begin
    for (int unsigned byte_index = 0; byte_index < (DataWidth/ByteWidth); byte_index++) begin
      wr_bit_enable_n[byte_index*ByteWidth +: ByteWidth] = {ByteWidth{wr_byte_enable_n[byte_index]}};
    end
  end

  /////////////////
  // The Memory! //
  /////////////////

  case ({
      NumWords,
      DataWidth,
      // ByteWidth, We are resolving the bytewidth beforehand so no check for it
      ReadLatency,
      ImplKey
  })
/*
    ////////////////////////////
    // SPM memory macro -- 2k //
    ////////////////////////////
    {
      32'd2048, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_2048x64m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
*/
    //////////////////
    // SPM 2K extra //
    //////////////////
    {
      32'd2048, // NumWords
      32'd72,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_2048x72m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////
    // Spm Memory -- 4K //
    //////////////////////
    {
      32'd4096, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_4096x64m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////
    // SPM 4k extra //
    //////////////////
    {
      32'd4096, // NumWords
      32'd72,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_4096x72m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////
    // SPM memory -- 8K //
    //////////////////////
    {
      32'd8192, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_8192x64m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////
    // SPM Memory -- 8K extra //
    ////////////////////////////
    {
      32'd8192, // NumWords
      32'd72,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_8192x72m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    /////////////////////
    // L2 memory macro //
    /////////////////////
    {
      32'd4096, // NumWords
      32'd128,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_4096x128m4b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    /////////////////////
    // L1 memory macro //
    /////////////////////
    {
      32'd2048, // NumWords
      32'd128,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_2048x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////////
    // L1 memory macro (other option) //
    ////////////////////////////////////
    {
      32'd4096, // NumWords
      32'd128,  // DataWidth
      32'd1,    // ReadLatency
      "HS_LVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_lvt_4096x128m4b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////
    // AIC IFD / ODR desc mem //
    ////////////////////////////
    {
      32'd128, // NumWords
      32'd64,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x64m2b1c1r2_wrapper u_macro (
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////
    // AX65 BTB RAM Macro //
    ////////////////////////
    {
      32'd1024, // NumWords
      32'd103,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x103m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////
    // AX65 BHT RAM Macro //
    ////////////////////////
    {
      32'd1024, // NumWords
      32'd32,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x32m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////
    // AX65 ICACHE TAG RAM Macro //
    ///////////////////////////////
    {
      32'd128, // NumWords
      32'd37,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x37m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////
    // AX65 ICACHE DATA RAM Macro //
    ////////////////////////////////
    {
      32'd1024, // NumWords
      32'd72,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x72m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////////////////
    // AX65 DCACHE TAG RAM and DTAG RAM Macro //
    ////////////////////////////////////////////
    {
      32'd64,  // NumWords
      32'd38,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x38m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////
    // AX65 DCACHE DATA RAM Macro //
    ////////////////////////////////
    {
      32'd512, // NumWords
      32'd72,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_512x72m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////////////////////////
    // AX65 L2ITLB TAG RAM and L2DTLB TAG RAM Macro //
    //////////////////////////////////////////////////
    {
      32'd256, // NumWords
      32'd54,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x54m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////
    // AX65 L2ITLB DATA RAM  //
    // L2DTLB DATA RAM Macro //
    ///////////////////////////
    {
      32'd256, // NumWords
      32'd44,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x44m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                // Clock
          .CSN   (chip_select_n),      // Chip enable, active low
          .WEN   (wr_enable_n),        // Write enable, active low
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .A     (address),            // Address input bus
          .DI    (wr_data),            // Data input bus
          .DOUT  (o_rd_data),          // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),         // Retention mode enable input pin
          .PDE   (i_impl.pde),         // Power down enable, active high
          .PRN   (o_impl.prn),         // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
          ///////////////////////////////
          // Row Redundancy Pins       //
          ///////////////////////////////
          .RREN1 ('0),                 // Row redundancy enable, active low
          .RREN2 ('0),                 // Row redundancy enable, active low
          .FRA1  ('0),                 // Faulty row address
          .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////
    // AX65 L2C TAG RAM //
    //////////////////////
    {
      32'd256, // NumWords
      32'd38,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x38m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////
    // AX65 L2C DATA RAM //
    ///////////////////////
    {
      32'd2048, // NumWords
      32'd144,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_2048x144m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    /////////////////////////////
    // AX65 256x11 ? RAM Macro //
    /////////////////////////////
    {
      32'd256, // NumWords
      32'd11,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x11m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    /////////////////////////////
    // AX65 256x13 ? RAM Macro //
    /////////////////////////////
    {
      32'd256, // NumWords
      32'd13,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x13m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    /////////////////////////////
    // AX65 512x12 ? RAM Macro //
    /////////////////////////////
    {
      32'd512, // NumWords
      32'd12,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_512x12m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                // Clock
          .CSN   (chip_select_n),      // Chip enable, active low
          .WEN   (wr_enable_n),        // Write enable, active low
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .A     (address),            // Address input bus
          .DI    (wr_data),            // Data input bus
          .DOUT  (o_rd_data),          // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),         // Retention mode enable input pin
          .PDE   (i_impl.pde),         // Power down enable, active high
          .PRN   (o_impl.prn),         // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////
    // DPU cSTORE //
    ////////////////
    {
      32'd64,   // NumWords
      32'd1152, // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      localparam int unsigned NumDataBanks  = 8;
      localparam int unsigned BankDataWidth = DataWidth / NumDataBanks;
`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Data banked %0dx%0d due to mem compiler limitations\n", NumDataBanks, BankDataWidth,
        "#################################################################################\n",
      );
`endif

      // Propagate the power down chain
      logic power_down_chain[NumDataBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumDataBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumDataBanks; ++bank_index) begin : gen_data_banks
        ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x144m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                                                        // Clock
          .CSN   (chip_select_n),                                              // Chip enable, active low
          .WEN   (wr_enable_n),                                                // Write enable, active low
          .BWEN  (wr_bit_enable_n[bank_index*BankDataWidth +: BankDataWidth]), // Write mask enable input bus
          .A     (address),                                                    // Address input bus
          .DI    (wr_data[bank_index*BankDataWidth   +: BankDataWidth]),       // Data input bus
          .DOUT  (o_rd_data[bank_index*BankDataWidth +: BankDataWidth]),       // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),                     // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
          ///////////////////////////////
          // Row Redundancy Pins       //
          ///////////////////////////////
          .RREN1 ('0),                 // Row redundancy enable, active low
          .RREN2 ('0),                 // Row redundancy enable, active low
          .FRA1  ('0),                 // Faulty row address
          .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
        );
      end
    end
    //////////////////
    // DPU prog_mem //
    //////////////////
    {
      32'd512, // NumWords
      32'd64,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_512x64m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                // Clock
          .CSN   (chip_select_n),      // Chip enable, active low
          .WEN   (wr_enable_n),        // Write enable, active low
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .A     (address),            // Address input bus
          .DI    (wr_data),            // Data input bus
          .DOUT  (o_rd_data),          // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),         // Retention mode enable input pin
          .PDE   (i_impl.pde),         // Power down enable, active high
          .PRN   (o_impl.prn),         // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
          ///////////////////////////////
          // Row Redundancy Pins       //
          ///////////////////////////////
          .RREN1 ('0),                 // Row redundancy enable, active low
          .RREN2 ('0),                 // Row redundancy enable, active low
          .FRA1  ('0),                 // Faulty row address
          .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////
    // DWPU programm memory //
    //////////////////////////
    {
      32'd1024, // NumWords
      32'd128,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////
    // CVA6V CVA6 Dcache and Icache data //
    ///////////////////////////////////////
    {
      32'd128, // NumWords
      32'd266, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      localparam int unsigned NumDataBanks  = 2;
      localparam int unsigned BankDataWidth = DataWidth / NumDataBanks;
`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Data banked %0dx%0d due to mem compiler limitations\n", NumDataBanks, BankDataWidth,
        "#################################################################################\n",
      );
`endif

      // Propagate the power down chain
      logic power_down_chain[NumDataBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumDataBanks];

      // The macro is one bit wider than we actually need...
      logic rd_data_open[NumDataBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumDataBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x134m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                                                                              // Clock
          .CSN   (chip_select_n),                                                                    // Chip enable, active low
          .WEN   (wr_enable_n),                                                                      // Write enable, active low
          .BWEN  ({1'b1, wr_bit_enable_n[bank_index*BankDataWidth +: BankDataWidth]}),               // Write mask enable input bus
          .A     (address),                                                                          // Address input bus
          .DI    ({1'b0, wr_data[bank_index*BankDataWidth +: BankDataWidth]}),                       // Data input bus
          .DOUT  ({rd_data_open[bank_index], o_rd_data[bank_index*BankDataWidth +: BankDataWidth]}), // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),                      // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),    // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]),  // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
          ///////////////////////////////
          // Row Redundancy Pins       //
          ///////////////////////////////
          .RREN1 ('0),                 // Row redundancy enable, active low
          .RREN2 ('0),                 // Row redundancy enable, active low
          .FRA1  ('0),                 // Faulty row address
          .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
        );
      end
    end
    ///////////////////////////
    // CVA6V CVA6 Dcache tag //
    ///////////////////////////
    {
      32'd128, // NumWords
      32'd37,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x37m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////
    // CVA6V CVA6 Icache tag //
    ///////////////////////////
    {
      32'd128, // NumWords
      32'd36,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x36m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////////////////////////
    // CVA6V CVA6 Dcache and Icache data (LVT backup) //
    ////////////////////////////////////////////////////
    {
      32'd128, // NumWords
      32'd266, // DataWidth
      32'd1,   // ReadLatency
      "HS_LVT" // ImplKey
    }: begin : gen_macro
      localparam int unsigned NumDataBanks  = 2;
      localparam int unsigned BankDataWidth = DataWidth / NumDataBanks;
`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Data banked %0dx%0d due to mem compiler limitations\n", NumDataBanks, BankDataWidth,
        "#################################################################################\n",
      );
`endif

      // Propagate the power down chain
      logic power_down_chain[NumDataBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumDataBanks];

      // The macro is one bit wider than we actually need...
      logic rd_data_open[NumDataBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumDataBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf1rwp_hsr_lvt_128x134m2b1c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          .CK    (clk),                                                                              // Clock
          .CSN   (chip_select_n),                                                                    // Chip enable, active low
          .WEN   (wr_enable_n),                                                                      // Write enable, active low
          .BWEN  ({1'b1, wr_bit_enable_n[bank_index*BankDataWidth +: BankDataWidth]}),               // Write mask enable input bus
          .A     (address),                                                                          // Address input bus
          .DI    ({1'b0, wr_data[bank_index*BankDataWidth +: BankDataWidth]}),                       // Data input bus
          .DOUT  ({rd_data_open[bank_index], o_rd_data[bank_index*BankDataWidth +: BankDataWidth]}), // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
          .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
          ///////////////////////////////
          // Power Gatins pins         //
          ///////////////////////////////
          .RET   (i_impl.ret),                      // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),    // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]),  // Power up ready negative
          ///////////////////////////////
          // Scan Pins                 //
          ///////////////////////////////
          .DFTRAM('0),                 // Test control enable, active high
          .SE    (i_impl.se),          // Scan enable, active high
          .SI_D_L('0),                 // Scan Input for the lower half DI
          .SO_D_L(),                   // Scan Output for the lower half DI
          .SI_D_R('0),                 // Scan Input for the upper half DI
          .SO_D_R(),                   // Scan Output for the upper half DI
          ///////////////////////////////
          // Column Redundancy Pins    //
          ///////////////////////////////
          .CRE1  ('0),                 // Column redundancy enable, active high, right side
          .CRE2  ('0),                 // Column redundancy enable, active hig, left side
          .FCA1  ('0),                 // Faulty column address, right side
          .FCA2  ('0),                 // Faulty column address, left side
          ///////////////////////////////
          // Row Redundancy Pins       //
          ///////////////////////////////
          .RREN1 ('0),                 // Row redundancy enable, active low
          .RREN2 ('0),                 // Row redundancy enable, active low
          .FRA1  ('0),                 // Faulty row address
          .FRA2  ('0),                 // Faulty row address
          ///////////////////////////////
          // Vmin Feature Control Pins //
          ///////////////////////////////
          .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
        );
      end
    end
    ////////////////////////////////////////
    // CVA6V CVA6 Dcache tag (LVT backup) //
    ////////////////////////////////////////
    {
      32'd128, // NumWords
      32'd37,  // DataWidth
      32'd1,   // ReadLatency
      "HS_LVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_lvt_128x37m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////////////////
    // CVA6V CVA6 Icache tag (LVT backup) //
    ////////////////////////////////////////
    {
      32'd128, // NumWords
      32'd36,  // DataWidth
      32'd1,   // ReadLatency
      "HS_LVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_lvt_128x36m4b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd2880, // NumWords
      32'd128,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_2880x128m4b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd2003, // NumWords
      32'd32,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_2016x32m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd1955, // NumWords
      32'd128,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_1984x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd1929, // NumWords
      32'd32,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_1952x32m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd993, // NumWords
      32'd120, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_1024x120m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd633, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_640x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd544, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_544x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd512, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_512x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd292, // NumWords
      32'd122, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_296x122m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd290, // NumWords
      32'd8,   // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_296x8m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd272, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_272x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd256, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_256x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd256, // NumWords
      32'd124, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_256x124m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd256, // NumWords
      32'd120, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_256x120m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd243, // NumWords
      32'd102, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_248x102m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd200, // NumWords
      32'd16,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_200x14m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data[13:0]),      // Data input bus
        .DOUT  (o_rd_data[13:0]),    // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
      always_comb o_rd_data[DataWidth-1:14] = '0;
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd192, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_192x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd144, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_144x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd128, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_128x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd128, // NumWords
      32'd112, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_128x112m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd128, // NumWords
      32'd104, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_128x104m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd128, // NumWords
      32'd32,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_128x32m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd61,  // NumWords
      32'd64,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_64x64m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd32,  // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_32x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd32,  // NumWords
      32'd74,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_32x74m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////
    // Single port RAMS //
    //////////////////////
    {
      32'd31,  // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_32x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd19,  // NumWords
      32'd92,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_24x92m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd16,  // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_16x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd2048, // NumWords
      32'd32,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_2048x32m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd2048, // NumWords
      32'd32,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rw_hsr_rvt_2048x32m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    // timestamp_logger in aic_infra             //
    ///////////////////////////////////////////////
    {
      32'd1024, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x64m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd1024, // NumWords
      32'd16,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_1024x16m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable
    ///////////////////////////////////////////////
    {
      32'd480, // NumWords
      32'd94,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_480x94m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    // Decoder Single port RAMS with word enable
    {
      32'd480, // NumWords
      32'd88,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_480x88m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd384, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_384x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd384, // NumWords
      32'd160, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_384x160m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd384, // NumWords
      32'd144, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_384x144m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd256,     // NumWords
      32'd60,      // DataWidth
      32'd1,       // ReadLatency
      "HS_RVT_DCD" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x60m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd240, // NumWords
      32'd88,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_240x88m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd128, // NumWords
      32'd8,   // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_128x8m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd64,  // NumWords
      32'd98,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x98m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd64,  // NumWords
      32'd88,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x88m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////////////////////////////
    // Decoder Single port RAMS with word enable //
    ///////////////////////////////////////////////
    {
      32'd64,  // NumWords
      32'd58,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x58m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////
    // DMA CHNL DATA //
    ///////////////////
    {
      32'd64,  // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_64x128m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ///////////////////////
    // eMMC Single Ports //
    ///////////////////////
    {
      32'd256, // NumWords
      32'd64,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_256x64m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1 ('0),                  // Faulty row address
        .FRA2 ('0),                  // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd1072,
      32'd128,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_1088x128m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    //////////////////////////////
    // Decoder Single port RAMS //
    //////////////////////////////
    {
      32'd400,
      32'd14,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rp_hsr_rvt_400x14m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),   // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),  // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)   // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////
    // NOC Memory -- 64b RAM  //
    ////////////////////////////
    {
      32'd512, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rp_hsr_rvt_512x64m4b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),         // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),        // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)         // Margin adjustment for access disturbance margin enhancement
      );
    end


    ////////////////////////////
    // NOC Memory -- 160b RAM //
    ////////////////////////////
    {
      32'd208, // NumWords
      32'd160, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf1rwp_hsr_rvt_208x160m2b1c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),         // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),        // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)         // Margin adjustment for access disturbance margin enhancement
      );
    end

    ////////////////////////////
    // SOC MGMT KSE-3 IRAM    //
    ////////////////////////////
    {
      32'd8192,// NumWords
      32'd36,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_8192x36m8b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),         // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),        // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)         // Margin adjustment for access disturbance margin enhancement
      );
    end
    ////////////////////////////
    // SOC MGMT KSE-3 DRAM    //
    ////////////////////////////
    {
      32'd4096,// NumWords
      32'd40,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_ra1rwp_hsr_rvt_4096x40m4b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK    (clk),                // Clock
        .CSN   (chip_select_n),      // Chip enable, active low
        .WEN   (wr_enable_n),        // Write enable, active low
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .A     (address),            // Address input bus
        .DI    (wr_data),            // Data input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS   (axe_tcl_pkg::MCS),         // Margin control selection
        .MCSW  (axe_tcl_pkg::MCSW),        // Margin control selection write
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .RET   (i_impl.ret),         // Retention mode enable input pin
        .PDE   (i_impl.pde),         // Power down enable, active high
        .PRN   (o_impl.prn),         // Power up ready negative
        ///////////////////////////////
        // Scan Pins                 //
        ///////////////////////////////
        .DFTRAM('0),                 // Test control enable, active high
        .SE    (i_impl.se),          // Scan enable, active high
        .SI_D_L('0),                 // Scan Input for the lower half DI
        .SO_D_L(),                   // Scan Output for the lower half DI
        .SI_D_R('0),                 // Scan Input for the upper half DI
        .SO_D_R(),                   // Scan Output for the upper half DI
        ///////////////////////////////
        // Column Redundancy Pins    //
        ///////////////////////////////
        .CRE1  ('0),                 // Column redundancy enable, active high, right side
        .CRE2  ('0),                 // Column redundancy enable, active hig, left side
        .FCA1  ('0),                 // Faulty column address, right side
        .FCA2  ('0),                 // Faulty column address, left side
        ///////////////////////////////
        // Row Redundancy Pins       //
        ///////////////////////////////
        .RREN1 ('0),                 // Row redundancy enable, active low
        .RREN2 ('0),                 // Row redundancy enable, active low
        .FRA1  ('0),                 // Faulty row address
        .FRA2  ('0),                 // Faulty row address
        ///////////////////////////////
        // Vmin Feature Control Pins //
        ///////////////////////////////
        .ADME  (axe_tcl_pkg::ADME)         // Margin adjustment for access disturbance margin enhancement
      );
    end
    default: begin : gen_macro
      $info(
        "\n",
        "#################################################################################\n",
        "# 'axe_tcl_ram_1rwp' Not supported configuration:\n",
        "#   Number of words:   %d\n", NumWords,
        "#   Address width:     %d\n", $clog2(NumWords),
        "#   Data width:        %d\n", DataWidth,
        "#   Byte width:        %d\n", ByteWidth,
        "#   Byte enable width: %d\n", (DataWidth/ByteWidth),
        "#   Latency Cycles:    %d\n", ReadLatency,
        "#   ImplKey:          '%s'\n",  ImplKey,
        "#################################################################################"
      );
      $fatal(1, "Not supported configuration!");
    end
  endcase
endmodule
