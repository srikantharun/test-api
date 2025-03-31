
module dma_channel_ll
    import dma_pkg::*;
(
    input  wire             i_clk,
    input  wire             i_rst_n,

    input  dma_addr_t       i_ll_addr,
    input  logic            i_ll_mode,
    input  logic            i_ll_en,

    output logic            o_ll_req,
    input  logic            i_ll_gnt,
    output dma_ll_t         o_ll,

    input  logic            i_ll_data_req,
    output logic            o_ll_data_gnt,
    input  dma_bufdata_t    i_ll_data,

    output dma_desc_t       o_desc,
    output logic            o_desc_req,
    input  logic            i_desc_gnt,

    input  dma_desc_t       i_default_desc
);

    localparam int unsigned MAX_DESC_SIZE = 80;
    typedef enum logic [1:0] { LL_FSM_IDLE, LL_FSM_FETCH_REQ, LL_FSM_FETCH_ACTIVE, LL_FSM_DESC_REQ } dma_ll_state_t;
    typedef logic [7:0] desc_siz_t;

    dma_ll_state_t ll_fetch_state_d, ll_fetch_state_q;
    dma_addr_t     ll_addr_q;
    logic          ll_mode_q;
    logic [MAX_DESC_SIZE*8-1:0] ll_raw_data;
    desc_siz_t bytes_avail;
    logic desc_loaded;

    always_ff @ (posedge i_clk or negedge i_rst_n)
      if (!i_rst_n) begin
        ll_fetch_state_q <= LL_FSM_IDLE;
        ll_addr_q        <= 'b0;
        ll_mode_q        <= 1'b0;
      end
      else begin
        ll_fetch_state_q <= ll_fetch_state_d;
        if ((ll_fetch_state_q == LL_FSM_IDLE) && i_ll_en) begin
          ll_addr_q <= i_ll_addr;
          ll_mode_q <= i_ll_mode;
        end
      end

    always_comb begin
      o_ll_req = 1'b0;
      o_desc_req = 1'b0;
      o_ll = '0;
      ll_fetch_state_d = ll_fetch_state_q;
      case(ll_fetch_state_q)
        LL_FSM_IDLE: begin
          if (i_ll_en)
            ll_fetch_state_d = LL_FSM_FETCH_REQ;
        end
        LL_FSM_FETCH_REQ: begin
          o_ll_req = 1'b1;
          o_ll     = '{ addr : ll_addr_q,
                        size : ll_mode_q ? 'd80 : 'd56 };
          if(i_ll_gnt)
            ll_fetch_state_d = LL_FSM_FETCH_ACTIVE;
        end
        LL_FSM_FETCH_ACTIVE: begin
          if(desc_loaded) begin
            ll_fetch_state_d = LL_FSM_DESC_REQ;
          end
        end
        LL_FSM_DESC_REQ: begin
          o_desc_req = 1'b1;
          if(i_desc_gnt) begin
            ll_fetch_state_d = LL_FSM_IDLE;
          end
        end
        default: begin
          ll_fetch_state_d = LL_FSM_IDLE;
        end
      endcase
    end

 /////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// SRC DATA COALESCOR                                            ///
/// ==================                                            ///
///                                                               ///
///    - Remove gaps from incoming data read packets to           ///
///      provide a continuous stream of bytes for creating        ///
///      AXI write data words.                                    ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////


  dma_coalesce #(
    .UNIT_SIZE      ( 8 ),
    .N_UNITS_IF     ( 64 ),
    .N_UNITS_OUT_IF ( 80 ),
    .N_UNITS_BUF    ( 80 )
  ) u_coalesce_buffer
  (
    .i_clk,
    .i_rst_n,

    .i_push_req           (i_ll_data_req),
    .o_push_gnt           (o_ll_data_gnt),
    .i_push_data          (i_ll_data.data),
    .i_push_offset        (i_ll_data.offset),
    .i_push_size          (i_ll_data.size),

    .i_pull_req           (o_ll_req),
    .i_pull_size          (ll_mode_q ? desc_siz_t'(80) : desc_siz_t'(56)),
    .o_pull_gnt           (),
    .o_pull_data          (ll_raw_data),
    .o_pull_avail         (bytes_avail),

    .i_drain              (1'b0)
  );

   always_comb desc_loaded = bytes_avail == (ll_mode_q ? desc_siz_t'(80) : desc_siz_t'(56));
   always_comb o_desc = decode_ll_f(ll_raw_data, i_default_desc);

endmodule
