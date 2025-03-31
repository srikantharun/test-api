// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Single Port (1R) Read Only Memory
///
module axe_tcl_rom_1p #(
  /// Number of Words of the Data Array `addr_t = logic [$clog2(NumWords)-1:0]`
  parameter int unsigned NumWords    = 16,
  /// The Data Width of each Individual Word in Bits
  parameter int unsigned DataWidth   = 16,
  /// The Latency for READ requests to the Memory in Cycles
  parameter int unsigned ReadLatency = 1,

  /// Adds a clock gate which enables the clock on request
  parameter bit FunctionalClkGate = 1'b1,
  /// Adds functional input silencing depending on request
  parameter bit FunctionalInputSilence = 1'b1,

  /// A technology specific key to choose between similar shaped memories
  parameter ImplKey = "default",
  /// parameterized type for implementation specific inputs
  parameter type impl_inp_t = axe_tcl_sram_pkg::impl_inp_rom_t,
  /// parameterized type for implementation specific outputs
  parameter type impl_oup_t = axe_tcl_sram_pkg::impl_oup_rom_t,

  /// Derived parameter: Address type
  localparam type addr_t   = logic[$clog2(NumWords)-1:0],
  /// Derived Parameter: Payload Data Type
  localparam type data_t   = logic[DataWidth-1:0]
)(
  /// Clock, positive edge triggered
  input  wire       i_clk,
  /// Asynchronous reset, active low
  input  wire       i_rst_n,

  /// Request read to the array, active high
  input  logic      i_req,
  /// The Word address of the request
  input  addr_t     i_addr,
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

  /////////////////////////////
  // Print the configuration //
  /////////////////////////////
`ifdef AXE_TCL_PRINT_CONFIG
  $info(
    "\n",
    "#################################################################################\n",
    "# 'axe_tcl_rom_1p' instantiated with the configuration:\n",
    "#   Number of words:   %d\n", NumWords,
    "#   Address width:     %d\n", $clog2(NumWords),
    "#   Data width:        %d\n", DataWidth,
    "#   Latency Cycles:    %d\n", ReadLatency,
    "#   ImplKey:          '%s'\n", ImplKey,
    "#################################################################################"
  );
`endif

  ////////////////////////////////////////////////////////
  // Power Optimization                                 //
  // https://git.axelera.ai/ai-pd-team/flow/-/issues/52 //
  ////////////////////////////////////////////////////////

  wire       clk;
  logic      chip_select_n;
  addr_t     address;

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
    always_comb address = i_req ? i_addr : addr_t'(0);
  end else begin : gen_direct_inpu
    always_comb address = i_addr;
  end

  /////////////////
  // The Memory! //
  /////////////////
  case ({
      NumWords,
      DataWidth,
      ReadLatency,
      ImplKey
  })
    //////////////////
    // APU Boot ROM //
    //////////////////
    {
      32'd8192, // NumWords,
      32'd64,   // DataWidth,
      32'd1,    // ReadLatency,
      "HD_LVT"  // ImplKey
    }: begin : gen_macro
      ln05lpe_a00_mc_vromp_hd_lvt_8192x64m16b4c1 u_macro (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK  (clk),                  // Clock
        .CSN (chip_select_n),        // Chip enable, active low
        .A   (address),              // Address input bus
        .DOUT(o_rd_data),            // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS (axe_tcl_sram_pkg::ROM_MCS), // Margin control selection
        .KCS (axe_tcl_sram_pkg::ROM_KCS), // Keeper control selection
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .PDE (i_impl.pde),           // Power down enable, active high
        .PRN (o_impl.prn)            // Power up ready negative
      );
    end
    ////////////////////////
    // SOC MGMT KSE-3 ROM //
    ////////////////////////
    {
      32'd32768,  // NumWords
      32'd36,     // DataWidth
      32'd1,      // ReadLatency
      "HS_RVT"    // ImplKey
    }: begin : gen_macro
      localparam int unsigned NumAddrBanks   = 2;
      localparam int unsigned AddrWidth      = unsigned'($clog2(NumWords));
      localparam int unsigned BankAddrWidth  = unsigned'($clog2(NumAddrBanks));
      localparam int unsigned BankNumWords   = NumWords / NumAddrBanks;
      localparam int unsigned MacroAddrWidth = unsigned'($clog2(BankNumWords));

`ifdef AXE_TCL_PRINT_CONFIG
      $info(
        "\n",
        "#################################################################################\n",
        "# Address banked %0dx%0d due to mem compiler limitations\n", NumAddrBanks, BanAddrWidth,
        "#################################################################################\n",
      );
`endif

      if (AddrWidth != BankAddrWidth + MacroAddrWidth) $fatal(1, "Bank Splitting by Address did not work.");

      logic                       power_down_chain[NumAddrBanks+1];
      logic [BankAddrWidth-1:0]   bank_address;
      logic [BankAddrWidth-1:0]   bank_address_q;
      logic [NumAddrBanks-1:0]    bank_enable;
      logic [NumAddrBanks-1:0]    bank_chip_select_n;
      logic [MacroAddrWidth-1:0]  macro_address;
      data_t                      rd_data[NumAddrBanks];

      // Propagate the power down chain
      always_comb power_down_chain[0] = i_impl.pde;
      always_comb o_impl.prn          = power_down_chain[NumAddrBanks];

      /////////////////////
      // Address Slicing //
      /////////////////////
      // higher part of address
      always_comb bank_address  = address[(AddrWidth-1)-:BankAddrWidth];
      always_comb macro_address = address[0+:MacroAddrWidth];

      always_comb bank_enable = NumAddrBanks'(i_req) << bank_address;
      always_comb bank_chip_select_n = ~bank_enable;

      // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n)   bank_address_q <= BankAddrWidth'(0);
        else if (i_req) bank_address_q <= bank_address;
      end

      ln05lpe_a00_mc_vromp_hd_lvt_16384x36m16b8c1_lower u_macro_lower (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK  (clk),                  // Clock
        .CSN (bank_chip_select_n[0]),// Chip enable, active low
        .A   (macro_address),        // Address input bus
        .DOUT(rd_data[0]),           // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS (axe_tcl_sram_pkg::ROM_MCS), // Margin control selection
        .KCS (axe_tcl_sram_pkg::ROM_KCS), // Keeper control selection
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .PDE (power_down_chain[0]),       // Power down enable, active high
        .PRN (power_down_chain[1])        // Power up ready negative
      );

      ln05lpe_a00_mc_vromp_hd_lvt_16384x36m16b8c1_upper u_macro_upper (
        ///////////////////////////////
        // Basic pins                //
        ///////////////////////////////
        .CK  (clk),                  // Clock
        .CSN (bank_chip_select_n[1]),// Chip enable, active low
        .A   (macro_address),        // Address input bus
        .DOUT(rd_data[1]),           // Data output bus
        ///////////////////////////////
        // Margin Adjustment Pins    //
        ///////////////////////////////
        .MCS (axe_tcl_sram_pkg::ROM_MCS), // Margin control selection
        .KCS (axe_tcl_sram_pkg::ROM_KCS), // Keeper control selection
        ///////////////////////////////
        // Power Gatins pins         //
        ///////////////////////////////
        .PDE (power_down_chain[1]),  // Power down enable, active high
        .PRN (power_down_chain[2])   // Power up ready negative
      );

      //////////////////////////////////////
      // Mux To get back proper read data //
      //////////////////////////////////////
      always_comb o_rd_data = rd_data[bank_address_q];

    end
    default: begin : gen_macro
      $info(
        "\n",
        "#################################################################################\n",
        "# 'axe_tcl_rom_1p' Not supported configuration:\n",
        "#   Number of words:   %d\n", NumWords,
        "#   Address width:     %d\n", $clog2(NumWords),
        "#   Data width:        %d\n", DataWidth,
        "#   Latency Cycles:    %d\n", ReadLatency,
        "#   ImplKey:          '%s'\n", ImplKey,
        "#################################################################################"
      );
      $fatal(1, "Not supported configuration!");
    end
  endcase
endmodule
