
module DWC_pcie_phy_memory_top #(
  parameter WD_RAM = 16,
  parameter PW_RAM = 15,
  parameter DP_RAM = 20000,
  parameter WD_ROM = 16,
  parameter PW_ROM = 15
) (
    input               phy0_sram_clk,
    input  [PW_RAM-1:0] phy0_sram_addr,
    output [WD_RAM-1:0] phy0_sram_rd_data,
    input               phy0_sram_rd_en,
    input  [WD_RAM-1:0] phy0_sram_wr_data,
    input               phy0_sram_wr_en,
    
    input               phy0_rom_clk,
    input  [PW_ROM-1:0] phy0_rom_addr,
    output [WD_ROM-1:0] phy0_rom_rd_data
);

  axe_tcl_sram_pkg::impl_inp_t mem_cfg_i;
  axe_tcl_sram_pkg::impl_oup_t mem_cfg_o;

   initial begin
      mem_cfg_i.mcs    = axe_tcl_pkg::MCS;
      mem_cfg_i.mcsw   = axe_tcl_pkg::MCSW;
      mem_cfg_i.ret    = 1'b0;
      mem_cfg_i.se     = 1'b0;
      mem_cfg_i.adme   = axe_tcl_pkg::ADME;
      mem_cfg_i.pde    = 1'b0;
   end

  ram_1p_wrapper #(
    .RD_LATENCY(1),
    .WD        (WD_RAM),
    .DP        (DP_RAM),
    .PW        (PW_RAM)
  ) u_phy_ram_0 (
    .addr        (phy0_sram_addr),
    .clk         (phy0_sram_clk),
    .din         (phy0_sram_wr_data),
    .dout        (phy0_sram_rd_data),
    .en          (phy0_sram_rd_en | phy0_sram_wr_en),
    .we          (phy0_sram_wr_en),
    .mem_cfg_i,
    .mem_cfg_o
  );

  ln05lpe_a00_mc_vromp_hd_lvt_20480x16m32b8c1_wrapper u_phy_rom_0 (
    // Basic pins
    .CK  (phy0_rom_clk),     // Clock
    .A   (phy0_rom_addr),    // Address input bus
    .DOUT(phy0_rom_rd_data), // Data output bus
    .CSN ('0),               // Chip enable, active low
    // Power Gatins pins
    .PDE ('0),               // Power down enable, active high
    .PRN (),                 // Power up ready negative
    // Margin Adjustment Pins
    .MCS ('0),               // Margin control selection
    .KCS ('0)                // Keeper control selection  
  );

endmodule 


