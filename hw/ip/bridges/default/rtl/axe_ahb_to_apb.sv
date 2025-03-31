// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// Synchronous AHB to APB bridge.
///

module axe_ahb_to_apb #(
  /// Width definition for address bus
  parameter int  unsigned AW    = 16,
  /// Width definition for data bus
  parameter int  unsigned DW    = 32,
  /// Width definition for APB strobe bus
  parameter int  unsigned PSTRBW = 4,
  // APB types
  parameter type          addr_t        = logic [AW              -1:0],
  parameter type          data_t        = logic [DW              -1:0],
  parameter type          pstrb_t       = logic [PSTRBW          -1:0]
)(
  /// Clock, positive edge triggered
  input  wire                         i_clk,
  /// Asynchronous reset, active low
  input  wire                         i_rst_n,
  //////////////////////////
  /// AHB input interface //
  //////////////////////////
  input  addr_t                       i_ahb_s_haddr,
  input  logic                        i_ahb_s_hwrite,
  input  data_t                       i_ahb_s_hwdata,
  input  axe_ahb_pkg::htrans_e        i_ahb_s_htrans,
  input  axe_ahb_pkg::hburst_e        i_ahb_s_hburst,
  input  axe_ahb_pkg::hsize_e         i_ahb_s_hsize,
  output data_t                       o_ahb_s_hrdata,
  output logic                        o_ahb_s_hready,
  output logic                        o_ahb_s_hresp,
  //////////////////////////
  // APB output interface //
  //////////////////////////
  output addr_t                       o_apb_m_paddr,
  output data_t                       o_apb_m_pwdata,
  output logic                        o_apb_m_pwrite,
  output logic                        o_apb_m_psel,
  output logic                        o_apb_m_penable,
  output pstrb_t                      o_apb_m_pstrb,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot,
  input  logic                        i_apb_m_pready,
  input  data_t                       i_apb_m_prdata,
  input  logic                        i_apb_m_pslverr
);

// -----------------------------------------------------------------------------
// Local parameters
// -----------------------------------------------------------------------------
// AHB subordinate FSM state.
typedef enum { AHB_IDLE, AHB_REQ, AHB_WAIT_RESP, AHB_ERROR } ahb_sub_state_e;

logic                 ahb_addr_phase;
logic                 ahb_done;
logic                 apb_req;
logic                 apb_wr_req_q;
addr_t                apb_address_q;
pstrb_t               apb_pstrb;
axe_ahb_pkg::hsize_e  ahb_hsize_q;
logic                 apb_manager_ready;
ahb_sub_state_e       ahb_state_d;
ahb_sub_state_e       ahb_state_q;
data_t                hrdata;
data_t                apb_manager_rdata;
logic                 apb_manager_error;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

// Detect AHB address phase.
always_comb ahb_addr_phase = o_ahb_s_hready & ((i_ahb_s_htrans == axe_ahb_pkg::NONSEQ) | (i_ahb_s_htrans == axe_ahb_pkg::SEQ));
always_comb ahb_done = o_ahb_s_hready & (i_ahb_s_htrans == axe_ahb_pkg::IDLE);

// AHB address phase signals are sampled and kept stable throughout the APB transaction
always_ff @(posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    apb_wr_req_q   <= 1'b0;
    apb_address_q  <= '0;
    ahb_hsize_q    <= axe_ahb_pkg::BYTE;
  end else begin
    if (ahb_addr_phase) begin
      apb_wr_req_q   <= i_ahb_s_hwrite;
      apb_address_q  <= i_ahb_s_haddr;
      ahb_hsize_q    <= i_ahb_s_hsize;
    end
  end
end

// Convert from HSIZE to PSTRB.
always_comb begin
  unique case (ahb_hsize_q)
    axe_ahb_pkg::BYTE:       apb_pstrb =                   'h0000_0001;
    axe_ahb_pkg::HALFWORD:   apb_pstrb =  (PSTRBW >= 2)  ? 'h0000_0003 : '0;
    axe_ahb_pkg::WORD:       apb_pstrb =  (PSTRBW >= 4)  ? 'h0000_000F : '0;
    axe_ahb_pkg::DOUBLEWORD: apb_pstrb =  (PSTRBW >= 8)  ? 'h0000_00FF : '0;
    axe_ahb_pkg::QUADWORD:   apb_pstrb =  (PSTRBW >= 16) ? 'h0000_FFFF : '0;
    axe_ahb_pkg::OCTWORD:    apb_pstrb =  (PSTRBW >= 32) ? 'hFFFF_FFFF : '0;
    default:                 apb_pstrb = '0;
  endcase
end

// Cut APB read data based on HSIZE, since APB does not support any read strobe/size.
always_comb begin
  unique case (ahb_hsize_q)
    axe_ahb_pkg::BYTE:       o_ahb_s_hrdata =                                        DW'(hrdata[axe_ahb_pkg::BYTE_W       -1:0]);
    axe_ahb_pkg::HALFWORD:   o_ahb_s_hrdata =  ( DW >= axe_ahb_pkg::HALFWORD_W   ) ? DW'(hrdata[axe_ahb_pkg::HALFWORD_W   -1:0]) : '0;
    axe_ahb_pkg::WORD:       o_ahb_s_hrdata =  ( DW >= axe_ahb_pkg::WORD_W       ) ? DW'(hrdata[axe_ahb_pkg::WORD_W       -1:0]) : '0;
    axe_ahb_pkg::DOUBLEWORD: o_ahb_s_hrdata =  ( DW >= axe_ahb_pkg::DOUBLEWORD_W ) ? DW'(hrdata[axe_ahb_pkg::DOUBLEWORD_W -1:0]) : '0;
    axe_ahb_pkg::QUADWORD:   o_ahb_s_hrdata =  ( DW >= axe_ahb_pkg::QUADWORD_W   ) ? DW'(hrdata[axe_ahb_pkg::QUADWORD_W   -1:0]) : '0;
    axe_ahb_pkg::OCTWORD:    o_ahb_s_hrdata =  ( DW >= axe_ahb_pkg::OCTWORD_W    ) ? DW'(hrdata[axe_ahb_pkg::OCTWORD_W    -1:0]) : '0;
    default:                 o_ahb_s_hrdata = '0;
  endcase
end

// ----------------------------------------------------------------------------
// AHB subordinate FSM
// ----------------------------------------------------------------------------
always_comb begin

  ahb_state_d = ahb_state_q;

  unique case (ahb_state_q)
    AHB_IDLE: begin
      if (ahb_addr_phase) ahb_state_d = AHB_REQ;
    end
    AHB_REQ: ahb_state_d = AHB_WAIT_RESP;
    AHB_WAIT_RESP: begin
      if (apb_manager_ready) begin
        if (i_apb_m_pslverr)      ahb_state_d = AHB_ERROR;
        else if (ahb_addr_phase)  ahb_state_d = AHB_REQ;
        else                      ahb_state_d = AHB_IDLE;
      end
    end
    AHB_ERROR: ahb_state_d = AHB_IDLE;
    default:   ahb_state_d = AHB_IDLE;
  endcase
end

// Error response.
//
// AHB subordinates must generate error response in two cycles:
//  - CYCLE 1: HREADY=0, HRESP=1
//  - CYCLE 2: HREADY=1, HRESP=1
//
// APB subordinates generate an error response in one cycle:
//  - CYCLE 1: PREADY=1, PENABLE=1, PSLVERR=1
//
always_comb begin

  hrdata            = '0;
  o_ahb_s_hready    = 1'b1;
  o_ahb_s_hresp     = 1'b0;
  apb_req           = 1'b0;

  unique case (ahb_state_q)
    AHB_IDLE: /*Keep default values*/ ;
    AHB_REQ: begin
      // 1-cycle request to APB manager, while stalling AHB
      apb_req = 1'b1;
      o_ahb_s_hready = 1'b0;
    end
    AHB_WAIT_RESP: begin
      o_ahb_s_hready = 1'b0;
      if (apb_manager_ready) begin
        if (apb_manager_error) begin
          // Error response first cycle
          o_ahb_s_hresp  = 1'b1;
        end else begin
          // No error response
          hrdata = apb_manager_rdata;
          o_ahb_s_hready = 1'b1;
        end
      end
    end
    AHB_ERROR: begin
      // Error response second cycle
      o_ahb_s_hresp  = 1'b1;
    end
    default: /*Keep default values*/ ;
  endcase
end

// AHB state register
always_ff @ (posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    ahb_state_q <= AHB_IDLE;
  end else begin
    ahb_state_q <= ahb_state_d;
  end
end

// ----------------------------------------------------------------------------
// APB manager in charge of generating the transaction
// ----------------------------------------------------------------------------
axe_apb_manager #(
  .PAW                        ( AW                   ),
  .PDW                        ( DW                   ),
  .PSTRBW                     ( PSTRBW               )
) u_apb_master (
  .i_clk                      ( i_clk                ),
  .i_rst_n                    ( i_rst_n              ),
  .o_apb_m_paddr              ( o_apb_m_paddr        ),
  .o_apb_m_pwdata             ( o_apb_m_pwdata       ),
  .o_apb_m_pwrite             ( o_apb_m_pwrite       ),
  .o_apb_m_psel               ( o_apb_m_psel         ),
  .o_apb_m_penable            ( o_apb_m_penable      ),
  .o_apb_m_pstrb              ( o_apb_m_pstrb        ),
  .o_apb_m_pprot              ( o_apb_m_pprot        ),
  .i_apb_m_pready             ( i_apb_m_pready       ),
  .i_apb_m_prdata             ( i_apb_m_prdata       ),
  .i_apb_m_pslverr            ( i_apb_m_pslverr      ),
  .i_apb_valid                ( apb_req              ),
  .i_apb_wr_req               ( apb_wr_req_q         ),
  .i_apb_address              ( apb_address_q        ),
  .i_apb_wdata                ( i_ahb_s_hwdata       ),
  .i_apb_pstrb                ( apb_pstrb            ),
  .i_apb_pprot                ( axe_apb_pkg::apb_prot_t'(3'h2) ), // Non-secure normal access
  .o_apb_ready                ( apb_manager_ready    ),
  .o_apb_rdata                ( apb_manager_rdata    ),
  .o_apb_error                ( apb_manager_error    )
);


endmodule
