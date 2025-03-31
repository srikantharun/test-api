// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
// KSE-3 Secure IP wrapper
//

module kudelski_kse3_top
  import kudelski_kse3_pkg::*;
 (
  // Clock and reset
  input  logic                                  i_clk,              // Clock for SECURE IP
  input  logic                                  i_rst_n,            // Active-low reset async assertion, external synchronized de-assertion with clk_i
  // AHB subordinate port
  input  kudelski_kse3_pkg::kse3_ahb_haddr_t    i_ahb_s_haddr,      // 4.5KB RAM + CSR  registers
  input  logic                                  i_ahb_s_hsel,
  input  logic                                  i_ahb_s_hready,
  input  logic                                  i_ahb_s_hwrite,
  input  axe_ahb_pkg::htrans_e                  i_ahb_s_htrans,
  input  axe_ahb_pkg::hburst_e                  i_ahb_s_hburst,
  input  axe_ahb_pkg::hsize_e                   i_ahb_s_hsize,
  input  kudelski_kse3_pkg::kse3_ahb_hdata_t    i_ahb_s_hwdata,
  output kudelski_kse3_pkg::kse3_ahb_hdata_t    o_ahb_s_hrdata,
  output logic                                  o_ahb_s_hreadyout,
  output logic                                  o_ahb_s_hresp,
  // Manager APB port
  output kudelski_kse3_pkg::kse3_apb_paddr_t    o_apb_m_paddr,     // 2048 bit OTP followed by 16 Bytes of Always-ON registers
  output logic                                  o_apb_m_psel,
  output logic                                  o_apb_m_penable,
  output logic                                  o_apb_m_pwrite,
  output kudelski_kse3_pkg::kse3_apb_pdata_t    o_apb_m_pwdata,
  input  kudelski_kse3_pkg::kse3_apb_pdata_t    i_apb_m_prdata,
  input  logic                                  i_apb_m_pready,
  input  logic                                  i_apb_m_pslverr,
  // Misc
  input  kudelski_kse3_pkg::kse3_config_t       i_config,           // Static configuration input including security config info
  output logic                                  o_interrupt,        // Active-high level interrupt
  // RAM logical size 16 kB (excluding integrity)
  output kudelski_kse3_pkg::kse3_dram_addr_t    o_mem_addr,         // Mem word addr
  output logic                                  o_mem_me,           // Active-high memory enable
  output logic                                  o_mem_gwe,          // Active-high global write enable , to be set to 1 for write access, to be to set to 0 for read accesses
  output kudelski_kse3_pkg::kse3_dram_data_t    o_mem_we,           // Active-high bit wise write enable
  output kudelski_kse3_pkg::kse3_dram_data_t    o_mem_wdata,        // Write data to mem
  input  kudelski_kse3_pkg::kse3_dram_data_t    i_mem_rdata,        // Read data from mem
  // ROM logical size 128 kB (excluding integrity)
  output kudelski_kse3_pkg::kse3_rom_addr_t     o_rom_addr,         // ROM  word addr
  output logic                                  o_rom_me,           // Active-high ROM enable
  input  kudelski_kse3_pkg::kse3_rom_data_t     i_rom_rdata,        // Read data from ROM
  // IRAM logical size 32 kB (excluding integrity)
  output kudelski_kse3_pkg::kse3_iram_addr_t    o_iram_addr,
  output logic                                  o_iram_me,
  output logic                                  o_iram_we,
  output kudelski_kse3_pkg::kse3_iram_data_t    o_iram_wem,
  output kudelski_kse3_pkg::kse3_iram_data_t    o_iram_wdata,
  input  kudelski_kse3_pkg::kse3_iram_data_t    i_iram_rdata,
  // Ring-oscillators
  output logic                                  o_ro_en,            // Enable signal for ring-oscillators, synchronous to clk_i
  input  kudelski_kse3_pkg::kse_ro_clk_t        i_ro_clk,           // Asynchronous clocks from ring-oscillators
  // KeyBus
  input  kudelski_kse3_pkg::kse_keybus_ack_t    i_kb_ack,           // KeyBus acknowledment signals
  output kudelski_kse3_pkg::kse_keybus_sel_t    o_kb_sel,           // KeyBus selection signals
  output kudelski_kse3_pkg::kse_keybus_addr_t   o_kb_addr,          // KeyBus address
  output kudelski_kse3_pkg::kse_keybus_data_t   o_kb_data           // KeyBus data
);

localparam int unsigned MEM_ADDR_W = 16;

logic [MEM_ADDR_W-1:0] mem_addr;
logic [MEM_ADDR_W-1:0] rom_addr;
logic [MEM_ADDR_W-1:0] iram_addr;

axe_ahb_pkg::htrans_t ahb_s_htrans;
axe_ahb_pkg::hburst_t ahb_s_hburst;
axe_ahb_pkg::hsize_t  ahb_s_hsize;

always_comb ahb_s_htrans = axe_ahb_pkg::htrans_t'(i_ahb_s_htrans);
always_comb ahb_s_hburst = axe_ahb_pkg::hburst_t'(i_ahb_s_hburst);
always_comb ahb_s_hsize  = axe_ahb_pkg::hsize_t'(i_ahb_s_hsize);

// Unused memory address MSbits are left open.
always_comb o_mem_addr  = kudelski_kse3_pkg::kse3_dram_addr_t'(mem_addr);
always_comb o_rom_addr  = kudelski_kse3_pkg::kse3_rom_addr_t'(rom_addr);
always_comb o_iram_addr = kudelski_kse3_pkg::kse3_iram_addr_t'(iram_addr);

kse3_ip u_kse3_ip (
  .clk_i              (i_clk),
  .rstn_i             (i_rst_n),
  .s_haddr_i          (i_ahb_s_haddr),
  .s_hsel_i           (i_ahb_s_hsel),
  .s_hready_i         (i_ahb_s_hready),
  .s_hwrite_i         (i_ahb_s_hwrite),
  .s_hwdata_i         (i_ahb_s_hwdata),
  .s_htrans_i         (ahb_s_htrans),
  .s_hburst_i         (ahb_s_hburst),
  .s_hsize_i          (ahb_s_hsize),
  .s_hrdata_o         (o_ahb_s_hrdata),
  .s_hreadyout_o      (o_ahb_s_hreadyout),
  .s_hresp_o          (o_ahb_s_hresp),
  .m_pwdata_o         (o_apb_m_pwdata),
  .m_paddr_o          (o_apb_m_paddr),
  .m_penable_o        (o_apb_m_penable),
  .m_psel_o           (o_apb_m_psel),
  .m_pwrite_o         (o_apb_m_pwrite),
  .m_prdata_i         (i_apb_m_prdata),
  .m_pready_i         (i_apb_m_pready),
  .m_pslverr_i        (i_apb_m_pslverr),
  .config_i           (i_config),
  .interrupt_o        (o_interrupt),
  .busy_o             (/*UNUSED*/),             // not used, for integration debug only
  .alarm_o            (/*UNUSED*/),             // not used, for integration debug only
  .mem_addr_o         (mem_addr),
  .mem_wdata_o        (o_mem_wdata),
  .mem_rdata_i        (i_mem_rdata),
  .mem_me_o           (o_mem_me),
  .mem_gwe_o          (o_mem_gwe),
  .mem_we_o           (o_mem_we),
  .rom_addr_o         (rom_addr),
  .rom_rdata_i        (i_rom_rdata),
  .rom_me_o           (o_rom_me),
  .iram_me_o          (o_iram_me),
  .iram_we_o          (o_iram_we),
  .iram_wem_o         (o_iram_wem),
  .iram_addr_o        (iram_addr),
  .iram_rdata_i       (i_iram_rdata),
  .iram_wdata_o       (o_iram_wdata),
  .ro_en_o            (o_ro_en),
  .ro_clk_i           (i_ro_clk),
  .kb_ack_i           (i_kb_ack),
  .kb_sel_o           (o_kb_sel),
  .kb_addr_o          (o_kb_addr),
  .kb_data_o          (o_kb_data)
);

endmodule
