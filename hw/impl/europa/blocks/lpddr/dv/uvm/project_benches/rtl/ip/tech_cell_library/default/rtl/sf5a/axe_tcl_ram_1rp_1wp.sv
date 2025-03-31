// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Two Port (1R + 1W) Memory
///
module axe_tcl_ram_1rp_1wp #(
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

  /// A technology specific key to choose between similar shaped memories TODO: Should this be an enum?
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
  /// Clock for Writes, positive edge triggered
  input  wire       i_wr_clk,
  /// Asynchronous reset for writes, active low
  input  wire       i_wr_rst_n,
  /// Request to write to the array, active high
  input  logic      i_wr_req,
  /// The Word address of the write request
  input  addr_t     i_wr_addr,
  /// The write data payload
  input  data_t     i_wr_data,
  /// The write enable mask for the individual bytes
  input  enable_t   i_wr_mask,

  /// Clock for Reads, positive edge triggered
  input  wire       i_rd_clk,
  /// Asynchronous reset for reads, active low
  input  wire       i_rd_rst_n,
  /// Request to write to the array, active high
  input  logic      i_rd_req,
  /// The word address of the read request
  input  addr_t     i_rd_addr,
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
    "# 'axe_tcl_ram_1rp_1wp' instantiated with the configuration:\n",
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

  ////////////////////////////////////////////////////////
  // Power Optimization                                 //
  // https://git.axelera.ai/ai-pd-team/flow/-/issues/52 //
  ////////////////////////////////////////////////////////

  wire       wr_clk;
  logic      wr_chip_select_n;
  addr_t     wr_address;
  data_t     wr_data;
  enable_t   wr_byte_enable_n;

  wire       rd_clk;
  logic      rd_chip_select_n;
  addr_t     rd_address;

  if (FunctionalClkGate) begin : gen_clk_gate
    axe_tcl_clk_gating u_clk_gate_pwr_wr (
      .i_clk    (i_wr_clk),
      .i_en     (i_wr_req),
      .i_test_en(i_impl.se),
      .o_clk    (wr_clk)
    );

    axe_tcl_clk_gating u_clk_gate_pwr_rd (
      .i_clk    (i_rd_clk),
      .i_en     (i_rd_req),
      .i_test_en(i_impl.se),
      .o_clk    (rd_clk)
    );
  end else begin : gen_direct_clk
    assign wr_clk = i_wr_clk;
    assign rd_clk = i_rd_clk;
  end

  always_comb wr_chip_select_n = ~i_wr_req;
  always_comb rd_chip_select_n = ~i_rd_req;

  if (FunctionalInputSilence) begin : gen_input_silence
    always_comb wr_address       =  i_wr_req ?  i_wr_addr : addr_t'(0);
    always_comb wr_data          =  i_wr_req ?  i_wr_data : data_t'(0);
    always_comb wr_byte_enable_n =  i_wr_req ? ~i_wr_mask : enable_t'(0);

    always_comb rd_address       =  i_rd_req ? i_rd_addr : addr_t'(0);
  end else begin : gen_direct_input
    always_comb wr_address       =  i_wr_addr;
    always_comb wr_data          =  i_wr_data;
    always_comb wr_byte_enable_n = ~i_wr_mask;

    always_comb rd_address       =  i_rd_addr;
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
      // ByteWidth,  We are resolving the bytewidth beforehand so no check for it
      ReadLatency,
      ImplKey
  })
    ////////////////
    // DPU bSTORE //
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

      for (genvar bank_index = 0; unsigned'(bank_index) < NumDataBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf2rwp_hsr_rvt_64x144m1b2c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),                                                     // Write Clock
          .WEN   (wr_chip_select_n),                                           // Write enable, active low
          .WA    (wr_address),                                                 // Write address input bus
          .BWEN  (wr_bit_enable_n[bank_index*BankDataWidth +: BankDataWidth]), // Write mask enable input bus
          .DI    (wr_data[bank_index*BankDataWidth +: BankDataWidth]),         // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),                                               // Read Clock
          .REN   (rd_chip_select_n),                                     // Read enable, active low
          .RA    (rd_address),                                           // Read address input bus
          .DOUT  (o_rd_data[bank_index*BankDataWidth +: BankDataWidth]), // Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////
    // AIC DMA LT //
    ////////////////
    {
      32'd128, // NumWords
      32'd64,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_128x64m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // AIC DMA HT //
    ////////////////
    {
      32'd128, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_128x128m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // AIC DMA HT //
    ////////////////
    {
      32'd256, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_256x128m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // CVA6V raptor VRF //
    //////////////////////
    {
      32'd32,  // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_32x128m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // DMA CHNL META DATA //
    ////////////////////////
    {
      32'd256, // NumWords
      32'd16,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_256x16m1b8c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // DMA CHNL TID //
    //////////////////
    {
      32'd64,  // NumWords
      32'd12,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_64x12m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd256, // NumWords
      32'd160, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_256x160m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd2688, // NumWords
      32'd64,   // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 8;
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Addr banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BankNumWords,
        "#################################################################################\n",
      );
`endif

      if (unsigned'($clog2(NumWords)) != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      // Propagate the power down chain
      logic power_down_chain[NumAddrBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      logic [BankAddrWidth-1:0] wr_bank_address;
      logic [BankAddrWidth-1:0] rd_bank_address;

      // lower part of address
      always_comb wr_bank_address = wr_address[BankAddrWidth-1:0];
      always_comb rd_bank_address = rd_address[BankAddrWidth-1:0];

      logic [NumAddrBanks-1:0] wr_bank_enable;
      logic [NumAddrBanks-1:0] rd_bank_enable;

      always_comb wr_bank_enable = NumAddrBanks'(i_wr_req) << wr_bank_address;
      always_comb rd_bank_enable = NumAddrBanks'(i_rd_req) << rd_bank_address;

      logic [BankAddrWidth-1:0] rd_bank_address_q;
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
        if (!i_rd_rst_n)   rd_bank_address_q <= BankAddrWidth'(0);
        else if (i_rd_req) rd_bank_address_q <= rd_bank_address;
      end

      data_t rd_data[NumAddrBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumAddrBanks; bank_index++) begin : gen_addr_banks
        logic wr_macro_enable_n;
        logic rd_macro_enable_n;

        always_comb wr_macro_enable_n = ~wr_bank_enable[bank_index];
        always_comb rd_macro_enable_n = ~rd_bank_enable[bank_index];

        logic [MacroAddrWidth-1:0] wr_macro_address;
        logic [MacroAddrWidth-1:0] rd_macro_address;

        // Upper part of address
        always_comb wr_macro_address = wr_address[BankAddrWidth+:MacroAddrWidth];
        always_comb rd_macro_address = rd_address[BankAddrWidth+:MacroAddrWidth];

        ///////////
        // Macro //
        ///////////
        ln05lpe_a00_mc_rf2rwp_hsr_lvt_336x64m1b8c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),             // Write Clock TODO: Additionaly gate?
          .WEN   (wr_macro_enable_n),  // Write enable, active low
          .WA    (wr_macro_address),   // Write address input bus
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .DI    (wr_data),            // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),             // Read Clock TODO: Additionaly gate?
          .REN   (rd_macro_enable_n),  // Read enable, active low
          .RA    (rd_macro_address),   // Read address input bus
          .DOUT  (rd_data[bank_index]),// Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[rd_bank_address_q];
    end
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd136, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_136x128m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd32,  // NumWords
      32'd68,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey // TODO: The implementation key does not match!
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_32x68m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd128, // NumWords
      32'd160, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_128x160m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd32,  // NumWords
      32'd32,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey TODO: IMpl key does not match macro
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rwp_hsr_rvt_32x32m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    //////////////////////////////////////
    // UART RX two port synchronous RAM //
    //////////////////////////////////////
    {
      32'd16,  // NumWords
      32'd12,  // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_16x12m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    //////////////////////////////////////
    // UART TX two port synchronous RAM //
    //////////////////////////////////////
    {
      32'd16,  // NumWords
      32'd8,   // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_16x8m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // DMA CNHL 2P DATA //
    //////////////////////
    {
      32'd256, // NumWords
      32'd128, // DataWidth
      32'd1,   // ReadLatency
      "HS_RVT_B8" // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_256x128m1b8c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd1952,
      32'd160,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 4;
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Addr banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BankNumWords,
        "#################################################################################\n",
      );
`endif

      if (unsigned'($clog2(NumWords)) != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      // Propagate the power down chain
      logic power_down_chain[NumAddrBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      logic [BankAddrWidth-1:0] wr_bank_address;
      logic [BankAddrWidth-1:0] rd_bank_address;

      // lower part of address
      always_comb wr_bank_address = wr_address[BankAddrWidth-1:0];
      always_comb rd_bank_address = rd_address[BankAddrWidth-1:0];

      logic [NumAddrBanks-1:0] wr_bank_enable;
      logic [NumAddrBanks-1:0] rd_bank_enable;

      always_comb wr_bank_enable = NumAddrBanks'(i_wr_req) << wr_bank_address;
      always_comb rd_bank_enable = NumAddrBanks'(i_rd_req) << rd_bank_address;

      logic [BankAddrWidth-1:0] rd_bank_address_q;
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
        if (!i_rd_rst_n)   rd_bank_address_q <= BankAddrWidth'(0);
        else if (i_rd_req) rd_bank_address_q <= rd_bank_address;
      end

      data_t rd_data[NumAddrBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumAddrBanks; bank_index++) begin : gen_addr_banks
        logic wr_macro_enable_n;
        logic rd_macro_enable_n;

        always_comb wr_macro_enable_n = ~wr_bank_enable[bank_index];
        always_comb rd_macro_enable_n = ~rd_bank_enable[bank_index];

        logic [MacroAddrWidth-1:0] wr_macro_address;
        logic [MacroAddrWidth-1:0] rd_macro_address;

        // Upper part of address
        always_comb wr_macro_address = wr_address[BankAddrWidth+:MacroAddrWidth];
        always_comb rd_macro_address = rd_address[BankAddrWidth+:MacroAddrWidth];

        ln05lpe_a00_mc_rf2rwp_hsr_rvt_488x160m1b8c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),             // Write Clock TODO: Additionaly gate?
          .WEN   (wr_macro_enable_n),  // Write enable, active low
          .WA    (wr_macro_address),   // Write address input bus
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .DI    (wr_data),            // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),             // Read Clock TODO: Additionaly gate?
          .REN   (rd_macro_enable_n),  // Read enable, active low
          .RA    (rd_macro_address),   // Read address input bus
          .DOUT  (rd_data[bank_index]),// Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[rd_bank_address_q];

    end

    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd2880,
      32'd48,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 6;
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Addr banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BankNumWords,
        "#################################################################################\n",
      );
`endif

      if (unsigned'($clog2(NumWords)) != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      // Propagate the power down chain
      logic power_down_chain[NumAddrBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      logic [BankAddrWidth-1:0] wr_bank_address;
      logic [BankAddrWidth-1:0] rd_bank_address;

      // lower part of address
      always_comb wr_bank_address = wr_address[BankAddrWidth-1:0];
      always_comb rd_bank_address = rd_address[BankAddrWidth-1:0];

      logic [NumAddrBanks-1:0] wr_bank_enable;
      logic [NumAddrBanks-1:0] rd_bank_enable;

      always_comb wr_bank_enable = NumAddrBanks'(i_wr_req) << wr_bank_address;
      always_comb rd_bank_enable = NumAddrBanks'(i_rd_req) << rd_bank_address;

      logic [BankAddrWidth-1:0] rd_bank_address_q;
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
        if (!i_rd_rst_n)   rd_bank_address_q <= BankAddrWidth'(0);
        else if (i_rd_req) rd_bank_address_q <= rd_bank_address;
      end

      data_t rd_data[NumAddrBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumAddrBanks; bank_index++) begin : gen_addr_banks
        logic wr_macro_enable_n;
        logic rd_macro_enable_n;

        always_comb wr_macro_enable_n = ~wr_bank_enable[bank_index];
        always_comb rd_macro_enable_n = ~rd_bank_enable[bank_index];

        logic [MacroAddrWidth-1:0] wr_macro_address;
        logic [MacroAddrWidth-1:0] rd_macro_address;

        // Upper part of address
        always_comb wr_macro_address = wr_address[BankAddrWidth+:MacroAddrWidth];
        always_comb rd_macro_address = rd_address[BankAddrWidth+:MacroAddrWidth];

        ln05lpe_a00_mc_rf2rwp_hsr_rvt_480x48m1b8c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),             // Write Clock TODO: Additionaly gate?
          .WEN   (wr_macro_enable_n),  // Write enable, active low
          .WA    (wr_macro_address),   // Write address input bus
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .DI    (wr_data),            // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),             // Read Clock TODO: Additionaly gate?
          .REN   (rd_macro_enable_n),  // Read enable, active low
          .RA    (rd_macro_address),   // Read address input bus
          .DOUT  (rd_data[bank_index]),// Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[rd_bank_address_q];

    end

    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd5760,
      32'd80,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 12;
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Addr banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BankNumWords,
        "#################################################################################\n",
      );
`endif

      if (unsigned'($clog2(NumWords)) != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      // Propagate the power down chain
      logic power_down_chain[NumAddrBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      logic [BankAddrWidth-1:0] wr_bank_address;
      logic [BankAddrWidth-1:0] rd_bank_address;

      // lower part of address
      always_comb wr_bank_address = wr_address[BankAddrWidth-1:0];
      always_comb rd_bank_address = rd_address[BankAddrWidth-1:0];

      logic [NumAddrBanks-1:0] wr_bank_enable;
      logic [NumAddrBanks-1:0] rd_bank_enable;

      always_comb wr_bank_enable = NumAddrBanks'(i_wr_req) << wr_bank_address;
      always_comb rd_bank_enable = NumAddrBanks'(i_rd_req) << rd_bank_address;

      logic [BankAddrWidth-1:0] rd_bank_address_q;
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
        if (!i_rd_rst_n)   rd_bank_address_q <= BankAddrWidth'(0);
        else if (i_rd_req) rd_bank_address_q <= rd_bank_address;
      end

      data_t rd_data[NumAddrBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumAddrBanks; bank_index++) begin : gen_addr_banks
        logic wr_macro_enable_n;
        logic rd_macro_enable_n;

        always_comb wr_macro_enable_n = ~wr_bank_enable[bank_index];
        always_comb rd_macro_enable_n = ~rd_bank_enable[bank_index];

        logic [MacroAddrWidth-1:0] wr_macro_address;
        logic [MacroAddrWidth-1:0] rd_macro_address;

        // Upper part of address
        always_comb wr_macro_address = wr_address[BankAddrWidth+:MacroAddrWidth];
        always_comb rd_macro_address = rd_address[BankAddrWidth+:MacroAddrWidth];

        ln05lpe_a00_mc_rf2rwp_hsr_rvt_480x80m1b8c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),             // Write Clock TODO: Additionaly gate?
          .WEN   (wr_macro_enable_n),  // Write enable, active low
          .WA    (wr_macro_address),   // Write address input bus
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .DI    (wr_data),            // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),             // Read Clock TODO: Additionaly gate?
          .REN   (rd_macro_enable_n),  // Read enable, active low
          .RA    (rd_macro_address),   // Read address input bus
          .DOUT  (rd_data[bank_index]),// Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[rd_bank_address_q];

    end

    ////////////////////////////////////////////////////////
    // Decoder two port synchronous RAMS with word enable //
    ////////////////////////////////////////////////////////
    {
      32'd912,
      32'd128,
      32'd1,
      "HS_RVT"
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 2;
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Addr banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BankNumWords,
        "#################################################################################\n",
      );
`endif

      if (unsigned'($clog2(NumWords)) != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      // Propagate the power down chain
      logic power_down_chain[NumAddrBanks+1];
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      logic [BankAddrWidth-1:0] wr_bank_address;
      logic [BankAddrWidth-1:0] rd_bank_address;

      // lower part of address
      always_comb wr_bank_address = wr_address[BankAddrWidth-1:0];
      always_comb rd_bank_address = rd_address[BankAddrWidth-1:0];

      logic [NumAddrBanks-1:0] wr_bank_enable;
      logic [NumAddrBanks-1:0] rd_bank_enable;

      always_comb wr_bank_enable = NumAddrBanks'(i_wr_req) << wr_bank_address;
      always_comb rd_bank_enable = NumAddrBanks'(i_rd_req) << rd_bank_address;

      logic [BankAddrWidth-1:0] rd_bank_address_q;
      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_rd_clk or negedge i_rd_rst_n) begin
        if (!i_rd_rst_n)   rd_bank_address_q <= BankAddrWidth'(0);
        else if (i_rd_req) rd_bank_address_q <= rd_bank_address;
      end

      data_t rd_data[NumAddrBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumAddrBanks; bank_index++) begin : gen_addr_banks
        logic wr_macro_enable_n;
        logic rd_macro_enable_n;

        always_comb wr_macro_enable_n = ~wr_bank_enable[bank_index];
        always_comb rd_macro_enable_n = ~rd_bank_enable[bank_index];

        logic [MacroAddrWidth-1:0] wr_macro_address;
        logic [MacroAddrWidth-1:0] rd_macro_address;

        // Upper part of address
        always_comb wr_macro_address = wr_address[BankAddrWidth+:MacroAddrWidth];
        always_comb rd_macro_address = rd_address[BankAddrWidth+:MacroAddrWidth];

        ln05lpe_a00_mc_rf2rwp_hsr_rvt_456x128m1b8c1r2_wrapper u_macro (
          ///////////////////////////////
          // Basic pins                //
          ///////////////////////////////
          ///////////////////////////////
          // Write interface           //
          ///////////////////////////////
          .WCK   (wr_clk),             // Write Clock TODO: Additionaly gate?
          .WEN   (wr_macro_enable_n),  // Write enable, active low
          .WA    (wr_macro_address),   // Write address input bus
          .BWEN  (wr_bit_enable_n),    // Write mask enable input bus
          .DI    (wr_data),            // Data input bus
          ///////////////////////////////
          // Read interface            //
          ///////////////////////////////
          .RCK   (rd_clk),             // Read Clock TODO: Additionaly gate?
          .REN   (rd_macro_enable_n),  // Read enable, active low
          .RA    (rd_macro_address),   // Read address input bus
          .DOUT  (rd_data[bank_index]),// Data output bus
          ///////////////////////////////
          // Margin Adjustment Pins    //
          ///////////////////////////////
          .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
          .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
          .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[rd_bank_address_q];

    end


    //////////////////////////
    // NoC  - 24 x 144-bit //
    /////////////////////////
    {
      32'd24,   // NumWords
      32'd144,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_24x144m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // NoC - 72 x 160-bit //
    ////////////////////////
    {
      32'd72,   // NumWords
      32'd160,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_72x160m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

    /////////////////////////
    // NoC - 136 x 160-bit //
    /////////////////////////
    {
      32'd136,  // NumWords
      32'd160,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_136x160m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // NoC - 64 x 160-bit //
    ////////////////////////
    {
      32'd64,   // NumWords
      32'd160,  // DataWidth
      32'd1,    // ReadLatency
      "HS_RVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_rf2rp_hsr_rvt_64x160m1b4c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .WA    (wr_address),         // Write address input bus
        .DI    (wr_data),            // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (o_rd_data),          // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // AIC_CD - Instruction Fetch //
    ////////////////////////////////
    {
      32'd16,
      32'd73,
      32'd1,
      "default"
    }: begin : gen_macro
      // Needs some additional padding as generator can not do 73 wide
      localparam int unsigned MacroDataWidth = 76;
      logic [MacroDataWidth-1:0] full_wr_data;
      logic [MacroDataWidth-1:0] full_wr_bit_enable_n;
      logic [MacroDataWidth-1:0] full_rd_data;

      always_comb full_wr_data         = {3'b000, wr_data};
      always_comb full_wr_bit_enable_n = {3'b111, wr_bit_enable_n};
      always_comb o_rd_data = full_rd_data[0+:DataWidth];

      ln05lpe_a00_mc_rf2rwp_hsr_rvt_16x76m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .BWEN  (full_wr_bit_enable_n),// Write mask enable input bus
        .WA    (wr_address),         // Write address input bus
        .DI    (full_wr_data),       // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (full_rd_data),       // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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
    // AIC_CD - Command and Data Copy //
    ////////////////////////////////////
    {
      32'd32,
      32'd73,
      32'd1,
      "default"
    }: begin : gen_macro
      // Needs some additional padding as generator can not do 73 wide
      localparam int unsigned MacroDataWidth = 76;
      logic [MacroDataWidth-1:0] full_wr_data;
      logic [MacroDataWidth-1:0] full_wr_bit_enable_n;
      logic [MacroDataWidth-1:0] full_rd_data;

      always_comb full_wr_data         = {3'b000, wr_data};
      always_comb full_wr_bit_enable_n = {3'b111, wr_bit_enable_n};
      always_comb o_rd_data = full_rd_data[0+:DataWidth];

      ln05lpe_a00_mc_rf2rwp_hsr_rvt_32x76m1b2c1r2_wrapper u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        ///////////////////////////////
        // Write interface           //
        ///////////////////////////////
        .WCK   (wr_clk),             // Write Clock
        .WEN   (wr_chip_select_n),   // Write enable, active low
        .BWEN  (full_wr_bit_enable_n),// Write mask enable input bus
        .WA    (wr_address),         // Write address input bus
        .DI    (full_wr_data),       // Data input bus
        ///////////////////////////////
        // Read interface            //
        ///////////////////////////////
        .RCK   (rd_clk),             // Read Clock
        .REN   (rd_chip_select_n),   // Read enable, active low
        .RA    (rd_address),         // Read address input bus
        .DOUT  (full_rd_data),       // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCSRD (axe_tcl_pkg::MCS),   // Read margin control selection
        .MCSWR (axe_tcl_pkg::MCS),   // Write margin control selection
        .KCS   ('0),                 // Keeper control selection (TODO add to impl?)
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

    default: begin : gen_macro
      $info(
        "\n",
        "#################################################################################\n",
        "# 'axe_tcl_ram_1rp_1wp' Not supported configuration:\n",
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
