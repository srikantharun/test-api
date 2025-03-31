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
// --- Module Description: 1 Port RAM wrapper for sf5a memories.
// -----------------------------------------------------------------------------

module ram_1p_wrapper #(
  // ----------------------------------------------------------------------------
  // Parameters
  // ----------------------------------------------------------------------------
  //reuse-pragma attr Visible false
  parameter      WD         = -1,      // Width of RAM
  //reuse-pragma attr Visible false
  parameter      PW         = -1,      // Address Width of RAM
  //reuse-pragma attr Visible false
  parameter      DP         = -1,      // Depth of RAM
  //reuse-pragma attr Visible false
  parameter      RD_LATENCY = -1       // Number of clock cycles an access to memory data takes
) (
  // ----------------------------------------------------------------------------
  // Ports
  // ----------------------------------------------------------------------------
  input           clk,
  input  [PW-1:0] addr,
  input  [WD-1:0] din,
  input           en,
  input           we,
  output [WD-1:0] dout,

  input  axe_tcl_sram_pkg::impl_inp_t mem_cfg_i,
  output axe_tcl_sram_pkg::impl_oup_t mem_cfg_o
);

  wire           clk_g;
  logic [WD-1:0] wdata;
  logic [PW-1:0] address;

  axe_tcl_clk_gating u_clk_gate_pwr (
    .i_clk    (clk),
    .i_en     (en),
    .i_test_en(mem_cfg_i.se),
    .o_clk    (clk_g)
  );
  assign address = en ? addr : '0;
  assign wdata   = en ? din  : '0;

  // ----------------------------------------------------------------------------
  // RAM wrapper implementation
  // -------------  -------------------------------------------------------------
  // Instantiate the appropriate Samsung memory cell according to the parameters
  case ({
    DP, WD, RD_LATENCY
  })
    {
      32'd528, // NumWords
      32'd135, // DataWidth
      32'd1    // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth = 264;
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
      logic bank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] bank_en_index_d, bank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic [$clog2(BankDepth)-1:0] bank_addr;

        assign bank_en[bank_index] = (address >= bank_index * BankDepth && address < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign bank_addr = (bank_en[bank_index]) ? address - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_rf1rp_hsr_rvt_264x136m2b1c1r2_wrapper u_rf1_264x136 (
          // Basic pins
          .CK    (clk_g),             // Clock
          .CSN   (~(en & bank_en[bank_index])),      // Chip enable, active low
          .WEN   (~(we & en & bank_en[bank_index])), // Write enable, active low
          .A     (bank_addr),         // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),    // Data input bus
          .DOUT  (rdata[bank_index]), // Data output bus
          // Margin Adjustment Pins
          .MCS   (mem_cfg_i.mcs),     // Margin control selection
          .MCSW  (mem_cfg_i.mcsw),    // Margin control selection write
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                    // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),     // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]),   // Power up ready negative
          // Scan Pins
          .DFTRAM('0),                // Test control enable, active high
          .SE    (mem_cfg_i.se),      // Scan enable, active high
          .SI_D_L('0),                // Scan Input for the lower half DI
          .SO_D_L(),                  // Scan Output for the lower half DI
          .SI_D_R('0),                // Scan Input for the upper half DI
          .SO_D_R(),                  // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),                // Column redundancy enable, active high, right side
          .CRE2  ('0),                // Column redundancy enable, active hig, left side
          .FCA1  ('0),                // Faulty column address, right side
          .FCA2  ('0),                // Faulty column address, left side
          .RREN1 ('0),                // Row redundancy enable, active low
          .RREN2 ('0),                // Row redundancy enable, active low
          .FRA1  ('0),                // Faulty row address
          .FRA2  ('0),                // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)     // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        bank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (bank_en[i]) bank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        bank_en_index_q <= bank_en_index_d;
      end
      assign dout = rdata[bank_en_index_q][WD-1:0];
    end
    {
      32'd20000, // NumWords
      32'd16,    // DataWidth
      32'd1      // ReadLatency
    }: begin : gen_inst
      localparam int unsigned BankDepth = 2560;
      localparam int unsigned BankWidth = 16;
      localparam int unsigned NumBanks  = (DP + BankDepth - 1) / BankDepth;
`ifdef DEBUG_INFO
      $info(
        "\n",
        "##########################################################################################\n",
        "# Data banked by depth %0dx%0d due to mem compiler limitations\n", NumBanks, BankDepth,
        "##########################################################################################\n",
      );
`endif
      logic bank_en[NumBanks];
      logic [BankWidth-1:0] rdata[NumBanks];
      logic [$clog2(NumBanks)-1:0] bank_en_index_d, bank_en_index_q;

      // Propagate the power down chain
      logic power_down_chain[NumBanks+1];
      assign power_down_chain[0] = mem_cfg_i.pde;
      assign mem_cfg_o.prn       = power_down_chain[NumBanks];

      for (genvar bank_index = 0; unsigned'(bank_index) < NumBanks; bank_index++) begin : gen_data_banks
        logic [$clog2(BankDepth)-1:0] bank_addr;

        assign bank_en[bank_index] = (address >= bank_index * BankDepth && address < (bank_index + 1) * BankDepth) ? 1'b1 : 1'b0;
        assign bank_addr = (bank_en[bank_index]) ? address - bank_index * BankDepth : '0;

        ln05lpe_a00_mc_ra1rp_hsr_rvt_2560x16m4b4c1r2_wrapper u_ra1_2560x16 (
          // Basic pins
          .CK    (clk_g),             // Clock
          .CSN   (~(en & bank_en[bank_index])),      // Chip enable, active low
          .WEN   (~(we & en & bank_en[bank_index])), // Write enable, active low
          .A     (bank_addr),         // Address input bus
          .DI    ({{BankWidth-WD{1'b0}}, wdata}),    // Data input bus
          .DOUT  (rdata[bank_index]), // Data output bus
          // Margin Adjustment Pins
          .MCS   (mem_cfg_i.mcs),     // Margin control selection
          .MCSW  (mem_cfg_i.mcsw),    // Margin control selection write
          // Power Gatins pins
          .RET   (mem_cfg_i.ret),                    // Retention mode enable input pin
          .PDE   (power_down_chain[bank_index]),     // Power down enable, active high
          .PRN   (power_down_chain[bank_index+1]),   // Power up ready negative
          // Scan Pins
          .DFTRAM('0),                // Test control enable, active high
          .SE    (mem_cfg_i.se),      // Scan enable, active high
          .SI_D_L('0),                // Scan Input for the lower half DI
          .SO_D_L(),                  // Scan Output for the lower half DI
          .SI_D_R('0),                // Scan Input for the upper half DI
          .SO_D_R(),                  // Scan Output for the upper half DI
          // Column Redundancy Pins
          .CRE1  ('0),                // Column redundancy enable, active high, right side
          .CRE2  ('0),                // Column redundancy enable, active hig, left side
          .FCA1  ('0),                // Faulty column address, right side
          .FCA2  ('0),                // Faulty column address, left side
          .RREN1 ('0),                // Row redundancy enable, active low
          .RREN2 ('0),                // Row redundancy enable, active low
          .FRA1  ('0),                // Faulty row address
          .FRA2  ('0),                // Faulty row address
          // Vmin Feature Control Pins
          .ADME  (mem_cfg_i.adme)     // Margin adjustment for access disturbance margin enhancement
        );
      end
      always_comb begin
        bank_en_index_d = '0;
        for (int i = 0; unsigned'(i) < NumBanks; i++) begin
          if (bank_en[i]) bank_en_index_d = i;
        end
      end
      always_ff @(posedge clk_g) begin
        bank_en_index_q <= bank_en_index_d;
      end
      assign dout = rdata[bank_en_index_q][WD-1:0];
    end

    default: begin
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
