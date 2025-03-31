// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>

module dma_channel_dst
    import dma_pkg::*;
    import axe_tcl_sram_pkg::*;
    import dma_mmu_reg_pkg::*;
#(
    parameter int unsigned NUM_PORTS = 2,
    parameter int unsigned NUM_BYTES_PORT = 64
)
(
    input  wire                    i_clk,
    input  wire                    i_rst_n,

    input  dma_mmu_reg2hw_t        i_mmu_cfg,
    output logic                   o_mmu_irq,

    input  dma_desc_t              i_desc,
    input  logic                   i_en,
    output logic                   o_busy,

    input  logic                   i_data_req,
    output logic                   o_data_gnt,
    input  dma_bufdata_t           i_data,

    input  logic                   i_src_busy,
    input  logic                   i_buf_busy,

    output logic  [NUM_PORTS-1:0]  o_dst_xfer_req,
    input  logic  [NUM_PORTS-1:0]  i_dst_xfer_gnt,
    output dma_wr_xfer_t           o_dst_xfer,

    input  logic  [NUM_PORTS-1:0]  i_dst_resp_req,
    output logic  [NUM_PORTS-1:0]  o_dst_resp_gnt,
    input  dma_wr_resp_t           i_dst_resp   [NUM_PORTS]
);

  localparam int unsigned N_BYTES_COALESCE = 192;

  typedef logic [$clog2(NUM_PORTS)-1:0]        dma_dst_port_sel_t;
  typedef logic [$clog2(N_BYTES_COALESCE):0]   dma_coal_bcnt_t;
  typedef logic [NUM_BYTES_PORT-1:0]           dma_line_be_t;

  logic [3:0]                       valid;
  logic [3:0]                       mv_req;
  logic [3:0]                       mv_gnt;

  logic                             ct_mode, ct_mode_q;

  logic [$clog2(DMA_N_TIDS):0] n_tid_active;
  dma_tid_t                         nxt_tid;


  always_comb o_busy   = |{valid, n_tid_active};

  // ct_mode = combined transfer mode - xinc == 1 so can go big.

  always_ff @(posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    ct_mode_q <= 1'b0;
  end
  else begin
    ct_mode_q <= i_desc.dst.xaddrinc == 1;
  end
  always_comb ct_mode = ct_mode_q;



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

  logic                             s2_data_req;
  logic                             s2_data_gnt;
  dma_data_t                        s2_data_raw;
  logic                             auto_drain_q, drain;
  logic                             s0_non0desc;

  always_comb drain = auto_drain_q || (!o_busy && (i_buf_busy || i_src_busy));

  always_ff @ (posedge i_clk or negedge i_rst_n)
    if (!i_rst_n)
      auto_drain_q <= 1'b0;
    else if (i_en && !s0_non0desc)
      auto_drain_q <= 1'b1;
    else if (!i_buf_busy && !i_src_busy)
      auto_drain_q <= 1'b0;

  dma_coalesce #(
    .UNIT_SIZE    ( 8 ),
    .N_UNITS_IF   ( 64 ),
    .N_UNITS_BUF  ( N_BYTES_COALESCE )
  ) u_coalesce_buffer
  (
    .i_clk,
    .i_rst_n,

    .i_push_req           (i_data_req),
    .o_push_gnt           (o_data_gnt),
    .i_push_data          (i_data.data),
    .i_push_offset        (i_data.offset),
    .i_push_size          (i_data.size),

    .i_pull_req           (s2_data_req),
    .i_pull_size          (s2.data_needed),
    .o_pull_gnt           (s2_data_gnt),
    .o_pull_data          (s2_data_raw),
    .o_pull_avail         (),

    .i_drain              (drain)
  );

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// PIPESTAGE 0                                                   ///
/// ===========                                                   ///
///                                                               ///
///    - Create list of contiguous data sections                  ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

typedef struct packed {
    dma_addr_t     addr;
    dma_addr_t     xstart;
    dma_size_t     sx_rem;
    dma_size_t     sy_rem;
    dma_size_t     dx_rem;
    dma_size_t     dy_rem;
    dma_size_t     st_rem;
  } pipestage_0_t;

  pipestage_0_t s0_d, s0;

  dma_addr_t s0_addr_next;
  dma_size_t s0_data_size;
  dma_size_t s0_size;
  logic      s0_fill_x, s0_fill_y;
  logic      s0_last;
  logic      s0_last_x;
  logic      s0_last_y;
  logic      s0_last_s;
  logic      s0_ld_init;
  logic      s0_ld_start;
  logic      s0_ld_x;
  logic      s0_ld_y;
  logic      s0_ld_next;
  logic      s0_ld_srow;


  dma_pipeline_ctrl #(
    .dma_pipedata_t ( pipestage_0_t )
  ) u_s0 (
    .i_clk,
    .i_rst_n,

    .i_us_mv_req (i_en && s0_non0desc),
    .o_us_mv_gnt (),

    .o_ds_mv_req (mv_req[0]),
    .i_ds_mv_gnt (mv_gnt[0]),

    .o_vld_q     (valid[0]),

    .i_us_pipe_d (s0_d),
    .i_pipe_d    (s0_d),
    .o_pipe_q    (s0),
    .i_stall     (1'b0),
    .i_last      (s0_last),
    .o_update    ()
  );

  always_comb s0_non0desc = (i_desc.glb.xtype != DSBL && |i_desc.dst.xbytesize && (|i_desc.src.xbytesize || i_desc.glb.xtype == FILL)) &&
                            (|i_desc.src.yrowsize && |i_desc.dst.yrowsize);
  always_comb s0_last = i_desc.glb.ytype == WRAP ? s0_last_s : s0_last_x && s0_last_y;

  // events
  // ------
  // s0_ld_init   : first load of descriptor data
  // s0_ld_start  : load the starting addresses
  // s0_ld_y      : start a new y row
  // s0_ld_x      : restart a row
  // s0_ld_next   : load next in a row

  always_comb s0_last_x   = s0.dx_rem == s0_size;
  always_comb s0_last_y   = !(|(s0.dy_rem >> 1));
  always_comb s0_last_s   = s0.st_rem == s0_size && !(|s0.sy_rem);
  always_comb s0_ld_init  = i_en && !o_busy;
  always_comb s0_ld_start = s0_last_x && s0_last_y && s0_last_s && i_desc.glb.ytype == WRAP;
  always_comb s0_ld_y     = i_desc.glb.ytype != DSBL && s0_last_x && !s0_last_y;
  always_comb s0_ld_x     = i_desc.glb.xtype == WRAP && s0_last_x && |(s0.dx_rem); // TODO
  always_comb s0_ld_next  = 1'b1;

  // i_desc.src_addr
  // s0_x_start_q
  // s0_addr_q

  always_comb begin
    case (1'b1)
      s0_ld_init  : s0_d.addr = i_desc.dst.addr;
      s0_ld_start : s0_d.addr = i_desc.dst.addr;
      s0_ld_y     : s0_d.addr = s0.xstart + i_desc.dst.yaddrstride;
      s0_ld_x     : s0_d.addr = s0.xstart;
      s0_ld_next  : s0_d.addr = s0_addr_next;
      default     : s0_d.addr = s0.addr;
    endcase
  end

  always_comb s0_addr_next = s0.addr + (ct_mode ? s0_size : (i_desc.dst.xaddrinc << i_desc.glb.trans_size));

  always_comb begin
    case (1'b1)
      s0_ld_init : s0_d.xstart = i_desc.dst.addr;
      s0_ld_y    : s0_d.xstart = s0.xstart + i_desc.dst.yaddrstride;
      default    : s0_d.xstart = s0.xstart;
    endcase
  end

  // s0_sx_rem_q - source row bytes remaining
  // s0_sy_rem_q - source rows remaining
  // s0_dx_rem_q - destination row bytes remaining
  // s0_dy_rem_q - destination rows remaining - used for destination total calcs
  // s0_st_rem_q - source total bytes remaining - used for 2D cases

  always_comb begin
    priority case (1'b1)
      s0_ld_init : begin
        s0_d.sx_rem = i_desc.src.xbytesize;
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.dy_rem = i_desc.glb.ytype == DSBL ? dma_size_t'(1) : i_desc.dst.yrowsize;
      end
      s0_ld_start: begin
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.sx_rem = s0.sx_rem - s0_size; // may need to change this for 2D cont...
        s0_d.dy_rem = i_desc.dst.yrowsize;
      end
      s0_ld_y    : begin
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.sx_rem = |s0.sy_rem ? i_desc.src.xbytesize : '0;
        s0_d.dy_rem = s0.dy_rem - 'd1;
      end
      s0_ld_x    : begin
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.sx_rem = s0_size > s0.sx_rem ? '0 : s0.sx_rem - s0_size;
        s0_d.dy_rem = s0.dy_rem;
      end
      s0_ld_next : begin
        s0_d.dx_rem = s0.dx_rem - s0_size;
        s0_d.sx_rem = s0_size > s0.sx_rem ? '0 : s0.sx_rem - s0_size;
        s0_d.dy_rem = s0.dy_rem;
      end
      default : begin
        s0_d.dx_rem = s0.dx_rem;
        s0_d.sx_rem = s0.sx_rem;
        s0_d.dy_rem = s0.dy_rem;
      end
    endcase
  end

  always_comb s0_ld_srow = (s0.st_rem <= s0_size) && (s0.sy_rem > 'd1);

  always_comb begin
    case (1'b1)
      s0_ld_init : begin
        s0_d.st_rem = |i_desc.src.yrowsize ? i_desc.src.xbytesize : '0;
        s0_d.sy_rem = i_desc.glb.ytype == DSBL ? dma_size_t'(1) : i_desc.src.yrowsize;
      end
      s0_ld_srow : begin
        s0_d.st_rem = s0.st_rem - s0_size + i_desc.src.xbytesize;
        s0_d.sy_rem = s0.sy_rem - 'd1;
      end
      default : begin
        s0_d.st_rem = s0_size > s0.st_rem ? '0 : s0.st_rem - s0_size;
        s0_d.sy_rem = s0.sy_rem;
      end
    endcase
  end

  always_comb s0_size      = ct_mode ?  s0.dx_rem : dma_size_t'(1) << i_desc.glb.trans_size;
  always_comb s0_fill_x    = ((i_desc.glb.xtype == FILL) && (s0_size > s0.sx_rem));
  always_comb s0_fill_y    = ((i_desc.glb.ytype == FILL) && (s0_size > s0.st_rem));
  always_comb s0_data_size = s0_fill_x ? s0.sx_rem : (s0_fill_y ? s0.st_rem : s0_size);

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// PIPESTAGE 1                                                   ///
/// ===========                                                   ///
///                                                               ///
///    - Legalise S0 reqs into AXI transfers                      ///
///      - 4K (or other non cross threshold)                      ///
///      - splitting over a transaction boundary                  ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

  typedef logic [5:0] burst_sel_t;
  typedef logic [6:0] burst_size_t;

  typedef struct packed {
    dma_addr_t     addr;
    dma_size_t     size;
    dma_size_t     data_size;
    logic          fill;
    burst_size_t   beatcnt;
    dma_size_t     datacnt;
  } pipestage_1_t;

  pipestage_1_t s1_us_d, s1_d, s1;

  burst_sel_t   s1_burst_sel_addr;
  burst_sel_t   s1_burst_sel_size;
  burst_size_t  s1_burst_addr;
  burst_size_t  s1_burst_size;
  dma_size_t    s1_beat_size;
  dma_size_t    s1_xfsize_mask;
  dma_size_t    s1_lines;
  dma_size_t    s1_data_size;
  dma_size_t    s1_size;
  logic         s1_last;
  logic         s1_last_beat;
  logic         s1_first_beat;
  dma_bufline_siz_t                 s1_data_needed;
  dma_bufline_siz_t                 s1_data_needed_;

  dma_pipeline_ctrl #(
    .dma_pipedata_t ( pipestage_1_t )
  ) u_s1 (
    .i_clk,
    .i_rst_n,

    .i_us_mv_req (mv_req[0]),
    .o_us_mv_gnt (mv_gnt[0]),

    .o_ds_mv_req (mv_req[1]),
    .i_ds_mv_gnt (mv_gnt[1]),

    .o_vld_q     (valid[1]),

    .i_us_pipe_d (s1_us_d),
    .i_pipe_d    (s1_d),
    .o_pipe_q    (s1),
    .i_stall     (1'b0),
    .i_last      (s1_last),
    .o_update    ()
  );

  dma_addr_t s1_addr_end;
  dma_addr_t s1_limit_end;
  dma_size_t s1_limit_size;

  dma_size_t s1_line_start;
  dma_size_t s1_line_end;
  dma_size_t s1_line_limit_end;

  dma_size_t s1_lines_size;
  dma_size_t s1_lines_limit;

  logic s1_limit_n;

  always_comb s1_addr_end     = s1.addr + s1.size - 'd1;
  always_comb s1_limit_end    = s1.addr | ((dma_addr_t'(1)<<12)-'d1);
  always_comb s1_limit_size   = s1_limit_end - s1.addr + 'd1;

  always_comb s1_line_start     = s1.addr >> (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size);
  always_comb s1_line_end       = s1_addr_end >> (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size);
  always_comb s1_line_limit_end = s1_limit_end >> (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size);

  always_comb s1_lines_size   = s1_line_end - s1_line_start;
  always_comb s1_lines_limit  = s1_line_limit_end - s1_line_start;

  always_comb s1_limit_n    = s1_lines_limit >= s1_lines_size ;

  always_comb s1_lines      = s1_limit_n ? s1_lines_size : s1_lines_limit;
  always_comb s1_size       = s1_limit_n ? s1.size : s1_limit_size;
  always_comb s1_data_size  = s1_size > s1.data_size ? s1.data_size : s1_size;

  always_comb s1_last       = s1_limit_n && s1_last_beat;

  always_comb s1_us_d = '{addr : s0.addr, size : s0_size, data_size : s0_data_size, fill : s0_fill_x || s0_fill_y, beatcnt : '0, datacnt : '0};

  always_comb s1_d    = '{addr : s1_last_beat ? s1.addr + s1_size : s1.addr,
                          size : s1_last_beat ? s1.size - s1_size : s1.size,
                          data_size : s1.data_size - s1_data_needed,
                          fill : s1.fill,
                          beatcnt : s1_last_beat ? '0 : s1.beatcnt + 'd1,
                          datacnt : s1_last_beat ? '0 : s1.datacnt + s1_data_needed_};

  always_comb s1_beat_size      = ct_mode ? NUM_BYTES_PORT : (dma_size_t'(1) << i_desc.glb.trans_size);
  always_comb s1_last_beat = s1.beatcnt == s1_lines;
  always_comb s1_first_beat = !(|s1.beatcnt);

  always_comb s1_xfsize_mask = s1_beat_size - 'd1;

  always_comb
    unique case ({s1_first_beat, s1_last_beat})
                2'b11 : s1_data_needed_ = s1_size;
                2'b10 : s1_data_needed_ = (|(s1.addr & s1_xfsize_mask) ? s1_beat_size - (s1.addr & s1_xfsize_mask) : s1_beat_size);
                2'b01 : s1_data_needed_ = s1_size - s1.datacnt;
                default : s1_data_needed_ = s1_beat_size;
    endcase

  always_comb s1_data_needed = s1_data_needed_ > s1.data_size ? s1.data_size : s1_data_needed_;

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// PIPESTAGE 2                                                   ///
/// ===========                                                   ///
///                                                               ///
///    - Fetch data for the transaciton                           ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

  typedef struct packed {
    dma_addr_t     addr;
    dma_size_t     lines;
    dma_size_t     beat_size;
    logic          last_beat;
    logic          first_beat;
    dma_coal_bcnt_t data_needed;
    dma_coal_bcnt_t bytes_needed;
    logic [$clog2(NUM_BYTES_PORT)-1:0] shift;
  } pipestage_2_t;

  pipestage_2_t s2_us_d, s2_d, s2;

  logic         s2_first_beat;
  logic         s2_last_beat;
  dma_data_t    s2_data_sht;
  dma_data_t    s2_data;
  dma_line_be_t s2_be_data;
  dma_line_be_t s2_be;
  dma_size_t    s2_xfsize_mask;

  dma_pipeline_ctrl #(
    .dma_pipedata_t ( pipestage_2_t )
  ) u_s2 (
    .i_clk,
    .i_rst_n,

    .i_us_mv_req (mv_req[1]),
    .o_us_mv_gnt (mv_gnt[1]),

    .o_ds_mv_req (mv_req[2]),
    .i_ds_mv_gnt (mv_gnt[2]),

    .o_vld_q     (valid[2]),

    .i_us_pipe_d (s2_us_d),
    .i_pipe_d    (s2_d),
    .o_pipe_q    (s2),
    .i_stall     (!s2_data_gnt),
    .i_last      (1'b1),
    .o_update    ()
  );

  always_comb s2_data_req = valid[2] && mv_gnt[2];

  always_comb s2_us_d = '{addr : s1.addr, lines : s1_lines, beat_size: s1_beat_size,
                          last_beat: s1_last_beat, first_beat: s1_first_beat, data_needed: s1_data_needed,
                          bytes_needed: s1_data_needed_,
                          shift : s1_first_beat ? s1.addr[$clog2(NUM_BYTES_PORT)-1:0] : s2.shift + s1_data_needed};

  always_comb s2_d    = s2;

  always_comb s2_xfsize_mask = s2.beat_size - 'd1;

  typedef logic [$clog2(NUM_BYTES_PORT)-1:0] dma_wr_shift_t;
  dma_wr_shift_t  shift;
  always_comb shift          = s2.first_beat ? dma_wr_shift_t'(s2.addr) : '0;
  //always_comb shift        = s2.shift;
  always_comb s2_be_data     = ((dma_line_be_t'(1) << s2.data_needed) - dma_line_be_t'(1)) << shift;
  always_comb s2_be          = ((dma_line_be_t'(1) << s2.bytes_needed) - dma_line_be_t'(1)) << shift;
  always_comb begin
    s2_data = '0;
    foreach (s2_be[i]) begin
      if (s2_be[i]) begin
        if (s2_be_data[i])
          s2_data[8*i+:8]        = s2_data_sht[8*i+:8] & {8{s2_be[i]}};
        else if (!i_desc.glb.fill_mode || (i%2==0))
          s2_data[8*i+:8]        = i_desc.glb.fill_val[7:0];
        else
          s2_data[8*i+:8]        = i_desc.glb.fill_val[15:0];
      end
    end
  end

  always_comb s2_data_sht    = dma_data_t'(s2_data_raw << {shift, 3'b000});



/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// PIPESTAGE 3                                                   ///
/// ===========                                                   ///
///                                                               ///
///    - Issue requrests to the port arbiters                     ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

  dma_wr_xfer_t s3_us_d, s3_d, s3;
  dma_addr_t s3_mmu_addr;

  logic s3_movout;

  dma_mmu #( .dma_axi_addr_t(dma_addr_t)
  ) s_mmu (
   .i_clk,
   .i_rst_n,
   .i_stall(!i_dst_xfer_gnt && valid[3]),
   .i_addr(s2.addr),
   .o_addr(s3_mmu_addr),
   .i_en(i_desc.glb.mmu_en),
   .i_cfg(i_mmu_cfg),
   .o_irq(o_mmu_irq)
  );


  always_comb s3_us_d     = '{ addr  : s2.addr,
                               size  : ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size,
                               len   : s2.lines,
                               first : s2.first_beat,
                               tid   : nxt_tid,
                               last  : s2.last_beat,
                               be    : s2_be,
                               data  : s2_data };

  always_comb s3_d        = s3;

  dma_pipeline_ctrl #(
    .dma_pipedata_t ( dma_wr_xfer_t )
  ) u_s3 (
    .i_clk,
    .i_rst_n,

    .i_us_mv_req (mv_req[2]),
    .o_us_mv_gnt (mv_gnt[2]),

    .o_ds_mv_req (mv_req[3]),
    .i_ds_mv_gnt (mv_gnt[3]),

    .o_vld_q     (valid[3]),

    .i_us_pipe_d (s3_us_d),
    .i_pipe_d    (s3_d),
    .o_pipe_q    (s3),
    .i_stall     (!i_dst_xfer_gnt),
    .i_last      (1'b1),
    .o_update    (s3_movout)
  );

  always_comb mv_gnt[3] = 1'b1;

  always_comb begin
    o_dst_xfer = s3;
    o_dst_xfer.addr = s3_mmu_addr;
  end

  always_comb begin
    o_dst_xfer_req = '0;
    o_dst_xfer_req[dma_dst_port_sel_t'(i_desc.dst.port)] = valid[3];
  end


/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// WRITE RESPONSE ID MANAGEMENT                                  ///
/// ============================                                  ///
///                                                               ///
///    - Take responses and add the ID back into circulation      ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

  dma_tid_t                           tid_fifo_rdaddr;
  dma_tid_t                           tid_fifo_wraddr;
  logic                               tid_push;
  logic                               tid_pop;
  dma_wr_resp_t                       resp;
  logic                               resp_req;
  logic                               resp_gnt;
  dma_dst_port_sel_t                  resp_idx;

  dma_port_arb #(
    .N_REQ (NUM_PORTS)
  ) u_rd_port_arb (
    .i_clk,
    .i_rst_n,

    .i_req     (i_dst_resp_req),
    .o_gnt     (o_dst_resp_gnt),
    .i_last    (1'b1),

    .o_val     (resp_req),
    .o_idx     (resp_idx),
    .i_ack     (resp_gnt)
  );

  always_comb resp_gnt = 1'b1;
  always_comb resp     = i_dst_resp[resp_idx];
  always_comb tid_push = resp_req;
  always_comb tid_pop  = valid[3] && s3_movout && s3.last;

  dma_fifo_logic #(
    .FIFO_DEPTH (DMA_N_TIDS),
    .START_FULL (1'b1)
  ) u_tid_fifo_logic (
    .i_clk,
    .i_rst_n,

    .i_push   (tid_push),
    .o_full_n (),
    .i_pop    (tid_pop),
    .o_empty_n(),
    .o_free_entries(n_tid_active),

    .o_wr_idx (tid_fifo_wraddr),
    .o_rd_idx (tid_fifo_rdaddr)
  );

  dma_tid_t tid_queue_q [DMA_N_TIDS];

  always_ff @ (posedge i_clk or negedge i_rst_n)
    if (!i_rst_n) begin
      for (int I = 0; I < DMA_N_TIDS; I++)
        tid_queue_q[I] <= dma_tid_t'(I);
    end
    else if (tid_push) begin
      tid_queue_q[tid_fifo_wraddr] <= resp.tid;
    end

  always_comb nxt_tid = tid_queue_q[tid_fifo_rdaddr];



endmodule
