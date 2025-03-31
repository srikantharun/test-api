// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
// APB 8-bit to 32-bit data width converter.
// Future improvement: make it generic for any data width change.
//

module axe_apb_8to32 #(
  // width definition for APB address bus
  parameter int   unsigned PAW               = 16                       ,
  // width definition for APB data bus
  localparam int  unsigned PD_INW            = 8                        ,
  localparam int  unsigned PD_OUTW           = 32                       ,
  // width definition for APB strobe bus
  localparam int  unsigned PSTRBW            = 4                        ,
  // APB types
  localparam type          paddr_t       = logic [PAW              -1:0] ,
  localparam type          pdata_in_t    = logic [PD_INW           -1:0] ,
  localparam type          pdata_out_t   = logic [PD_OUTW          -1:0] ,
  localparam type          pstrb_t       = logic [PSTRBW           -1:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk                 ,
  // Asynchronous reset, active low
  input  wire                         i_rst_n               ,

  // APB subordinate interface (IN)
  input  paddr_t                      i_apb_s_paddr         ,
  input  pdata_in_t                   i_apb_s_pwdata        ,
  input  logic                        i_apb_s_pwrite        ,
  input  logic                        i_apb_s_psel          ,
  input  logic                        i_apb_s_penable       ,
  input  axe_apb_pkg::apb_prot_t      i_apb_s_pprot         ,
  output logic                        o_apb_s_pready        ,
  output pdata_in_t                   o_apb_s_prdata        ,
  output logic                        o_apb_s_pslverr       ,

  // APB manager interface (OUT)
  output paddr_t                      o_apb_m_paddr         ,
  output pdata_out_t                  o_apb_m_pwdata        ,
  output logic                        o_apb_m_pwrite        ,
  output logic                        o_apb_m_psel          ,
  output logic                        o_apb_m_penable       ,
  output pstrb_t                      o_apb_m_pstrb         ,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot         ,
  input  logic                        i_apb_m_pready        ,
  input  pdata_out_t                  i_apb_m_prdata        ,
  input  logic                        i_apb_m_pslverr
);

// ----------------------------------------------------------------------------
// RTL
// ----------------------------------------------------------------------------

// Incoming PADDR is addressing bytes, clear 2 LSbits to obtain word address.
assign o_apb_m_paddr = {i_apb_s_paddr[PAW-1:2], 2'b00};

// Use incoming PADDR 2 LSbits to generate the PSTRB signal
// Note that in the APB protocol PSTRB is only meaningful for write transactions,
// here it will be also used to select the right 8-bit portion of PRDATA[31:0].
always_comb begin

  o_apb_m_pwdata = '0;

  unique case (i_apb_s_paddr[1:0])
    2'b00: begin
      o_apb_m_pstrb   = 4'b0001;
      o_apb_s_prdata  = i_apb_m_prdata[7:0];
      o_apb_m_pwdata |= i_apb_s_pwdata;
    end
    2'b01: begin
      o_apb_m_pstrb   = 4'b0010;
      o_apb_s_prdata  = i_apb_m_prdata[15:8];
      o_apb_m_pwdata |= i_apb_s_pwdata << 8;
    end
    2'b10: begin
      o_apb_m_pstrb   = 4'b0100;
      o_apb_s_prdata  = i_apb_m_prdata[23:16];
      o_apb_m_pwdata |= i_apb_s_pwdata << 16;
    end
    2'b11: begin
      o_apb_m_pstrb   = 4'b1000;
      o_apb_s_prdata  = i_apb_m_prdata[31:24];
      o_apb_m_pwdata |= i_apb_s_pwdata << 24;
    end
    default: begin // Unreachable
      o_apb_m_pstrb  = '0;
      o_apb_s_prdata = '0;
      o_apb_m_pwdata = '0;
    end
  endcase
end

// Remaining signals are simply forwarded

assign o_apb_m_pwrite    = i_apb_s_pwrite;
assign o_apb_m_psel      = i_apb_s_psel;
assign o_apb_m_penable   = i_apb_s_penable;
assign o_apb_m_pprot     = i_apb_s_pprot;
assign o_apb_s_pready    = i_apb_m_pready;
assign o_apb_s_pslverr   = i_apb_m_pslverr;

endmodule
