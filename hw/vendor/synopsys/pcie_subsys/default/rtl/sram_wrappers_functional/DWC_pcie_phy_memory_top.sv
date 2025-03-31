
module DWC_pcie_phy_memory_top #(
  parameter WD_RAM    = 16,
  parameter PW_RAM    = 15,
  parameter DP_RAM    = 32768,
  parameter WD_ROM    = 16,
  parameter PW_ROM    = 15
) (
    input             phy0_sram_clk,
    input   [PW_RAM-1:0]  phy0_sram_addr,
    output  [WD_RAM-1:0]  phy0_sram_rd_data,
    input                  phy0_sram_rd_en,
    input   [WD_RAM-1:0]  phy0_sram_wr_data,
    input             phy0_sram_wr_en,
    
    input                                       phy0_rom_clk,
    input  [PW_ROM-1:0]                             phy0_rom_addr,
    output [WD_ROM-1:0]                             phy0_rom_rd_data
);


ram1p
#(
    .WD (WD_RAM),
    .DP (DP_RAM),
    .PW (PW_RAM)
) u_phy_ram_0 (
    .addr     (phy0_sram_addr),
    .clk      (phy0_sram_clk),
    .din      (phy0_sram_wr_data),
    .dout     (phy0_sram_rd_data),
    .en       (phy0_sram_rd_en | phy0_sram_wr_en),
    .we       (phy0_sram_wr_en)
);



`ifdef SYNTHESIS

`else
tb_pcs_raw_ext_rom u_phy_rom_0 (
    .phy_rom_clk                            (phy0_rom_clk),
    .phy_rom_addr                           (phy0_rom_addr),
    .phy_rom_rd_data                        (phy0_rom_rd_data)
);



`endif // SYNTHESIS

endmodule 


