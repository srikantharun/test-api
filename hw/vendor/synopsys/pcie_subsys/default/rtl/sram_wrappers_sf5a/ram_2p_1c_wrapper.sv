// ------------------------------------------------------------------------------
// 
// Copyright 2002 - 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_pcie_ctl
// Component Version: 6.20a
// Release Type     : GA
// Build ID         : 87.21.47.15.PCIeParseConfig_14.PCIeSimulate_100.PCIeTbCommon_132.SNPSPHYSetup_38
// ------------------------------------------------------------------------------
// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

// -------------------------------------------------------------------------
// -------------------------------------------------------------------------
// --- Module Description: 2-Port 1-Clock RAM wrapper for sf5a memories.
// -----------------------------------------------------------------------------
 
module ram_2p_1c_wrapper #(
  // ----------------------------------------------------------------------------
  // Parameters
  // ----------------------------------------------------------------------------
  //reuse-pragma attr Visible false
  parameter WD         = -1,  // Width of RAM
  //reuse-pragma attr Visible false
  parameter PW         = -1,  // Address Width of RAM
  //reuse-pragma attr Visible false
  parameter DP         = -1,  // Depth of RAM
  //reuse-pragma attr Visible false
  parameter RD_LATENCY = -1   // Number of clock cycles an access to memory data takes
) (
  // ----------------------------------------------------------------------------
  // Ports
  // ----------------------------------------------------------------------------
  input           clk,
  input  [PW-1:0] addra,
  input  [PW-1:0] addrb,
  input  [WD-1:0] dina,
  input           ena,
  input           enb,
  input           wea,
  output [WD-1:0] doutb,

  input  axe_tcl_sram_pkg::impl_inp_t mem_cfg_i,
  output axe_tcl_sram_pkg::impl_oup_t mem_cfg_o
);

  wire           clk_g;
  logic [PW-1:0] waddr;
  logic [WD-1:0] wdata;
  logic [PW-1:0] raddr;

  axe_tcl_clk_gating u_clk_gate_pwr (
    .i_clk    (clk),
    .i_en     (ena | enb),
    .i_test_en(mem_cfg_i.se),
    .o_clk    (clk_g)
  );
  assign waddr = ena ? addra : '0;
  assign wdata = ena ? dina  : '0;
  assign raddr = enb ? addrb : '0;

  // ----------------------------------------------------------------------------
  // RAM wrapper implementation
  // -------------  -------------------------------------------------------------
  // Instantiate the appropriate Samsung memory cell according to the parameters
  case ({
    DP, WD, RD_LATENCY
  })
    {
      32'd2176, // NumWords
      32'd133,  // DataWidth
      32'd1     // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth = 272;
      localparam int unsigned BankWidth = 136;
      localparam int unsigned NumBanks  = (DP + BankDepth - 1) / BankDepth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by depth %0dx%0d due to mem compiler limitations\n", NumBanks, BankDepth,
        "##########################################################################################\n",
      );
`endif
      logic rbank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] rbank_en_index_d, rbank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic wbank_en;
        logic [$clog2(BankDepth)-1:0] wbank_addr;
        logic [$clog2(BankDepth)-1:0] rbank_addr;

        assign wbank_en = (waddr >= bank_index * BankDepth && waddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign wbank_addr = (wbank_en) ? waddr - bank_index * BankDepth : '0;
        assign rbank_en[bank_index] = (raddr >= bank_index * BankDepth && raddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign rbank_addr = (rbank_en[bank_index]) ? raddr - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2_wrapper u_ra2_272x136 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(wea & ena & wbank_en)),        // Write enable, active low
          .WA    (wbank_addr),     // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),  // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~(enb & rbank_en[bank_index])),  // Read enable, active low
          .RA    (rbank_addr),     // Read address input bus
          .DOUT  (rdata[bank_index]),              // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        rbank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (rbank_en[i]) rbank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        rbank_en_index_q <= rbank_en_index_d;
      end
      assign doutb = rdata[rbank_en_index_q][WD-1:0];
    end
    {
      32'd64,  // NumWords
      32'd145, // DataWidth
      32'd1    // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 64;
      localparam int unsigned BankWidth    = 148;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

      ln05lpe_a00_mc_rf2rp_hsr_rvt_64x148m1b2c1r2_wrapper u_rf2_64x148 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end
    {
      32'd2,   // NumWords
      32'd133, // DataWidth
      32'd1    // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 136;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

      ln05lpe_a00_mc_rf2rp_hsr_rvt_32x136m1b2c1r2_wrapper u_rf2_32x136 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end
    {
      32'd22, // NumWords
      32'd64, // DataWidth
      32'd1   // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 64;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

      ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2_wrapper u_rf2_32x64 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end
    {
      32'd5,  // NumWords
      32'd64, // DataWidth
      32'd1   // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 64;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

      ln05lpe_a00_mc_rf2rp_hsr_rvt_32x64m1b2c1r2_wrapper u_rf2_32x64 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end
    {
      32'd2176, // NumWords
      32'd128,  // DataWidth
      32'd1     // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankWidth = 136;
      localparam int unsigned BankDepth = 272;
      localparam int unsigned NumBanks  = (DP + BankDepth - 1) / BankDepth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by depth %0dx%0d due to mem compiler limitations\n", NumBanks, BankDepth,
        "##########################################################################################\n",
      );
`endif
      logic rbank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] rbank_en_index_d, rbank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic wbank_en;
        logic [$clog2(BankDepth)-1:0] wbank_addr;
        logic [$clog2(BankDepth)-1:0] rbank_addr;

        assign wbank_en = (waddr >= bank_index * BankDepth && waddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign wbank_addr = (wbank_en) ? waddr - bank_index * BankDepth : '0;
        assign rbank_en[bank_index] = (raddr >= bank_index * BankDepth && raddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign rbank_addr = (rbank_en[bank_index]) ? raddr - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_rf2rp_hsr_rvt_272x136m1b8c1r2_wrapper u_ra2_272x136 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(wea & ena & wbank_en)),        // Write enable, active low
          .WA    (wbank_addr),     // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),  // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~(enb & rbank_en[bank_index])),  // Read enable, active low
          .RA    (rbank_addr),     // Read address input bus
          .DOUT  (rdata[bank_index]),              // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        rbank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (rbank_en[i]) rbank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        rbank_en_index_q <= rbank_en_index_d;
      end
      assign doutb = rdata[rbank_en_index_q][WD-1:0];
    end
    {
      32'd64,  // NumWords
      32'd244, // DataWidth
      32'd1    // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth    = 64;
      localparam int unsigned BankWidth    = 124;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      localparam int unsigned NumBanks     = (WD + BankWidth - 1) / BankWidth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by width %0dx%0d due to mem compiler limitations\n", NumBanks, BankWidth,
        "##########################################################################################\n",
      );
`endif
      logic [NumBanks*BankWidth-1:0] wdata_padded;
      logic [NumBanks*BankWidth-1:0] rdata_padded;
      assign wdata_padded = {{NumBanks*BankWidth-WD{1'b0}}, wdata};

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf2rp_hsr_rvt_64x124m1b2c1r2_wrapper u_ra2_64x124 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(ena & wea)),   // Write enable, active low
          .WA    ({{AddrPadWidth{1'b0}}, waddr}),                 // Address input bus
          .DI    (wdata_padded[bank_index*BankWidth+:BankWidth]), // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~enb),           // Read enable, active low
          .RA    ({{AddrPadWidth{1'b0}}, raddr}),                 // Read address input bus
          .DOUT  (rdata_padded[bank_index*BankWidth+:BankWidth]), // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end

      assign doutb = rdata_padded[WD-1:0];
    end
    {
      32'd4,   // NumWords
      32'd144, // DataWidth
      32'd1    // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 144;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

      ln05lpe_a00_mc_rf2rp_hsr_rvt_32x144m1b2c1r2_wrapper u_rf2_32x144 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end
    {
      32'd32,  // NumWords
      32'd236, // DataWidth
      32'd1    // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 120;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      localparam int unsigned NumBanks     = (WD + BankWidth - 1) / BankWidth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by width %0dx%0d due to mem compiler limitations\n", NumBanks, BankWidth,
        "##########################################################################################\n",
      );
`endif
      logic [NumBanks*BankWidth-1:0] wdata_padded;
      logic [NumBanks*BankWidth-1:0] rdata_padded;
      assign wdata_padded = {{NumBanks*BankWidth-WD{1'b0}}, wdata};

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf2rp_hsr_rvt_32x120m1b2c1r2_wrapper u_rf2_32x120 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(ena & wea)),   // Write enable, active low
          .WA    ({{AddrPadWidth{1'b0}}, waddr}),                 // Address input bus
          .DI    (wdata_padded[bank_index*BankWidth+:BankWidth]), // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~enb),           // Read enable, active low
          .RA    ({{AddrPadWidth{1'b0}}, raddr}),                 // Read address input bus
          .DOUT  (rdata_padded[bank_index*BankWidth+:BankWidth]), // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end

      assign doutb = rdata_padded[WD-1:0];
    end
    {
      32'd4,  // NumWords
      32'd208, // DataWidth
      32'd1    // ReadLatency
    }: begin : inst
      localparam int unsigned BankDepth    = 32;
      localparam int unsigned BankWidth    = 104;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      localparam int unsigned NumBanks     = (WD + BankWidth - 1) / BankWidth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by width %0dx%0d due to mem compiler limitations\n", NumBanks, BankWidth,
        "##########################################################################################\n",
      );
`endif
      logic [NumBanks*BankWidth-1:0] wdata_padded;
      logic [NumBanks*BankWidth-1:0] rdata_padded;
      assign wdata_padded = {{NumBanks*BankWidth-WD{1'b0}}, wdata};

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        ln05lpe_a00_mc_rf2rp_hsr_rvt_32x104m1b2c1r2_wrapper u_rf2_32x104 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(ena & wea)),   // Write enable, active low
          .WA    ({{AddrPadWidth{1'b0}}, waddr}),                 // Address input bus
          .DI    (wdata_padded[bank_index*BankWidth+:BankWidth]), // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~enb),           // Read enable, active low
          .RA    ({{AddrPadWidth{1'b0}}, raddr}),                 // Read address input bus
          .DOUT  (rdata_padded[bank_index*BankWidth+:BankWidth]), // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end

      assign doutb = rdata_padded[WD-1:0];
    end
    {
      32'd1131, // NumWords
      32'd130,  // DataWidth
      32'd1     // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth = 284;
      localparam int unsigned BankWidth = 132;
      localparam int unsigned NumBanks  = (DP + BankDepth - 1) / BankDepth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by depth %0dx%0d due to mem compiler limitations\n", NumBanks, BankDepth,
        "##########################################################################################\n",
      );
`endif
      logic rbank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] rbank_en_index_d, rbank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic wbank_en;
        logic [$clog2(BankDepth)-1:0] wbank_addr;
        logic [$clog2(BankDepth)-1:0] rbank_addr;

        assign wbank_en = (waddr >= bank_index * BankDepth && waddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign wbank_addr = (wbank_en) ? waddr - bank_index * BankDepth : '0;
        assign rbank_en[bank_index] = (raddr >= bank_index * BankDepth && raddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign rbank_addr = (rbank_en[bank_index]) ? raddr - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_rf2rp_hsr_rvt_284x132m1b8c1r2_wrapper u_ra2_284x132 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(wea & ena & wbank_en)),        // Write enable, active low
          .WA    (wbank_addr),     // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),  // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~(enb & rbank_en[bank_index])),  // Read enable, active low
          .RA    (rbank_addr),     // Read address input bus
          .DOUT  (rdata[bank_index]),              // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        rbank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (rbank_en[i]) rbank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        rbank_en_index_q <= rbank_en_index_d;
      end
      assign doutb = rdata[rbank_en_index_q][WD-1:0];
    end
    {
      32'd705, // NumWords
      32'd140, // DataWidth
      32'd1    // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth = 356;
      localparam int unsigned BankWidth = 140;
      localparam int unsigned NumBanks  = (DP + BankDepth - 1) / BankDepth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by depth %0dx%0d due to mem compiler limitations\n", NumBanks, BankDepth,
        "##########################################################################################\n",
      );
`endif
      logic rbank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] rbank_en_index_d, rbank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic wbank_en;
        logic [$clog2(BankDepth)-1:0] wbank_addr;
        logic [$clog2(BankDepth)-1:0] rbank_addr;

        assign wbank_en = (waddr >= bank_index * BankDepth && waddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign wbank_addr = (wbank_en) ? waddr - bank_index * BankDepth : '0;
        assign rbank_en[bank_index] = (raddr >= bank_index * BankDepth && raddr < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign rbank_addr = (rbank_en[bank_index]) ? raddr - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_rf2rp_hsr_rvt_356x140m1b8c1r2_wrapper u_ra2_356x140 (
          // Basic pins
          // Write interface
          .WCK   (clk_g),          // Write Clock
          .WEN   (~(wea & ena & wbank_en)),        // Write enable, active low
          .WA    (wbank_addr),     // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),  // Data input bus
          // Read interface
          .RCK   (clk_g),          // Read Clock
          .REN   (~(enb & rbank_en[bank_index])),  // Read enable, active low
          .RA    (rbank_addr),     // Read address input bus
          .DOUT  (rdata[bank_index]),              // Data output bus
          // Margin Adjustment Pins
          .MCSRD (mem_cfg_i.mcs),  // Margin control selection
          .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
          .KCS   ('0),             // Keeper control selection
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                  // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),   // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]), // Power up ready negative
          // Scan Pins
          .DFTRAM('0),             // Test control enable, active high
          .SE    (mem_cfg_i.se),   // Scan enable, active high
          .SI_D_L('0),             // Scan Input for the lower half DI
          .SO_D_L(),               // Scan Output for the lower half DI
          .SI_D_R('0),             // Scan Input for the upper half DI
          .SO_D_R(),               // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),             // Column redundancy enable, active high, right side
          .CRE2  ('0),             // Column redundancy enable, active hig, left side
          .FCA1  ('0),             // Faulty column address, right side
          .FCA2  ('0),             // Faulty column address, left side
          .RREN1 ('0),             // Row redundancy enable, active low
          .RREN2 ('0),             // Row redundancy enable, active low
          .FRA1  ('0),             // Faulty row address
          .FRA2  ('0),             // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        rbank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (rbank_en[i]) rbank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        rbank_en_index_q <= rbank_en_index_d;
      end
      assign doutb = rdata[rbank_en_index_q][WD-1:0];
    end
    {
      32'd512, // NumWords
      32'd10,   // DataWidth
      32'd1    // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth    = 512;
      localparam int unsigned BankWidth    = 12;
      localparam int unsigned AddrPadWidth = ($clog2(BankDepth) > $clog2(DP)) ? $clog2(BankDepth) - $clog2(DP) : 0;
      logic [BankWidth-1:0] rdata;

     ln05lpe_a00_mc_rf2rp_hsr_rvt_512x12m1b8c1r2_wrapper u_ra2_512x12 (
        // Basic pins
        // Write interface
        .WCK   (clk_g),          // Write Clock
        .WEN   (~(wea & ena)),   // Write enable, active low
        .WA    ({{AddrPadWidth{1'b0}}, waddr}), // Address input bus
        .DI    ({{BankWidth-WD{1'b0}}, wdata}), // Data input bus
        // Read interface
        .RCK   (clk_g),          // Read Clock
        .REN   (~enb),           // Read enable, active low
        .RA    ({{AddrPadWidth{1'b0}}, raddr}), // Read address input bus
        .DOUT  (rdata),          // Data output bus
        // Margin Adjustment Pins
        .MCSRD (mem_cfg_i.mcs),  // Margin control selection
        .MCSWR (mem_cfg_i.mcs),  // Margin control selection write
        .KCS   ('0),             // Keeper control selection
        // Power Gatins pins
        .RET   (mem_cfg_i.ret),  // Retention mode enable input pin
        .PDE   (mem_cfg_i.pde),  // Power down enable, active high
        .PRN   (mem_cfg_o.prn),  // Power up ready negative
        // Scan Pins
        .DFTRAM('0),             // Test control enable, active high
        .SE    (mem_cfg_i.se),   // Scan enable, active high
        .SI_D_L('0),             // Scan Input for the lower half DI
        .SO_D_L(),               // Scan Output for the lower half DI
        .SI_D_R('0),             // Scan Input for the upper half DI
        .SO_D_R(),               // Scan Output for the upper half DI
        // Column Redundancy Pins
        .CRE1  ('0),             // Column redundancy enable, active high, right side
        .CRE2  ('0),             // Column redundancy enable, active hig, left side
        .FCA1  ('0),             // Faulty column address, right side
        .FCA2  ('0),             // Faulty column address, left side
        .RREN1 ('0),             // Row redundancy enable, active low
        .RREN2 ('0),             // Row redundancy enable, active low
        .FRA1  ('0),             // Faulty row address
        .FRA2  ('0),             // Faulty row address
        // Vmin Feature Control Pins
        .ADME  (mem_cfg_i.adme)  // Margin adjustment for access disturbance margin enhancement
      );

      assign doutb = rdata[WD-1:0];
    end

    default:
    begin
`ifdef DEBUG_INFO
      $info(
        "Chosen configuration is: NumWords = %0d, DataWidth = %0d, ReadLatency = %0d",
        DP,
        WD,
        RD_LATENCY,
        " is not supported!"
      );
`endif
    end
  endcase

endmodule
