
module dma_channel_src
    import dma_pkg::*;
    import dma_mmu_reg_pkg::*;
#(
    parameter int unsigned NUM_PORTS      = 2,
    parameter int unsigned NUM_BYTES_PORT = 64
) (
    input  wire             i_clk,
    input  wire             i_rst_n,

    input  dma_mmu_reg2hw_t i_mmu_cfg,
    output logic            o_mmu_irq,

    input  logic            i_ll_req,
    input  dma_ll_t         i_ll,

    input  dma_desc_t       i_desc,
    input  logic            i_en,
    output logic            o_busy,

    output logic            o_alloc_req,
    input  logic            i_alloc_gnt,
    output dma_alloc_t      o_alloc,
    input  dma_tid_t        i_tid,

    output logic [NUM_PORTS-1:0] o_src_xfer_req,
    input  logic [NUM_PORTS-1:0] i_src_xfer_gnt,
    output dma_rd_xfer_t         o_src_xfer

);

  typedef logic [$clog2(NUM_PORTS)-1:0] dma_src_port_sel_t;

  logic [2:0] mv_req;
  logic [2:0] mv_gnt;
  logic [2:0] valid;
  logic       ct_mode, ct_mode_q;
  logic       ll_mode_q;
  logic       ll_mode_set, ll_mode_clr;
  logic       s0_ld_ll;

  always_comb o_busy = |valid;

  always_ff @(posedge i_clk or negedge i_rst_n)
    if (!i_rst_n) begin
      ct_mode_q <= 1'b0;
      ll_mode_q <= 1'b0;
    end
    else begin
      ct_mode_q <= i_desc.src.xaddrinc == 1 || ll_mode_set || ll_mode_q;
      ll_mode_q <= (ll_mode_q || ll_mode_set) & !ll_mode_clr;
    end
  always_comb ct_mode = ct_mode_q;

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
    dma_size_t     dt_rem;
  } pipestage_0_t;


  pipestage_0_t s0_d, s0;

  logic      s0_last;

  logic      s0_last_x;
  logic      s0_last_y;
  logic      s0_last_d;
  logic      s0_ld_init;
  logic      s0_ld_start;
  logic      s0_ld_x;
  logic      s0_ld_y;
  logic      s0_ld_next;
  logic      s0_ld_drow;
  dma_addr_t s0_addr_next;
  dma_size_t s0_size;
  logic      s0_non0desc;

  always_comb ll_mode_set = s0_ld_ll;
  always_comb ll_mode_clr = s0_ld_init;

  dma_pipeline_ctrl #(
    .dma_pipedata_t ( pipestage_0_t )
  ) u_s0 (
    .i_clk,
    .i_rst_n,

    .i_us_mv_req (i_en && s0_non0desc ),
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

  always_comb s0_non0desc = ((i_desc.glb.xtype != DSBL) && |i_desc.src.xbytesize) &&
                            (|i_desc.src.yrowsize) && (|i_desc.dst.yrowsize);
  always_comb s0_last = (i_desc.glb.ytype == WRAP || (i_desc.glb.ytype == DSBL && i_desc.glb.xtype == WRAP)) ? s0_last_d : s0_last_x && s0_last_y;


  // events
  // ------
  // s0_ld_init   : first load of descriptor data
  // s0_ld_start  : load the starting addresses
  // s0_ld_y      : start a new y row
  // s0_ld_x      : restart a row
  // s0_ld_next   : load next in a row

  always_comb s0_last_x   = s0.sx_rem == s0_size;
  always_comb s0_last_y   = s0.sy_rem == 'd1;
  always_comb s0_last_d   = s0.dt_rem == s0_size && !(|s0.dy_rem);
  always_comb s0_ld_init  = i_en && !o_busy;
  always_comb s0_ld_ll    = i_ll_req && !o_busy;
  always_comb s0_ld_start = s0_last_x && s0_last_y && !s0_last_d && i_desc.glb.ytype == WRAP;
  always_comb s0_ld_y     = i_desc.glb.ytype != DSBL; // && (s0_last_x) || (i_desc.glb.ytype == WRAP && s0_dx;
  always_comb s0_ld_x     = i_desc.glb.xtype == WRAP && s0_last_x && !s0_last_d;
  always_comb s0_ld_next  = 1'b1;

  // i_desc.src_addr
  // s0_x_start_q
  // s0_addr_q

  always_comb begin
    priority case (1'b1)
      s0_ld_ll    : s0_d.addr = i_ll.addr;
      s0_ld_init  : s0_d.addr = i_desc.src.addr;
      s0_ld_start : s0_d.addr = i_desc.src.addr;
      s0_ld_y     : s0_d.addr = s0.xstart + i_desc.src.yaddrstride;
      s0_ld_x     : s0_d.addr = s0.xstart;
      s0_ld_next  : s0_d.addr = s0_addr_next;   // only used when ct_mode == 0
      default     : s0_d.addr = s0.addr;
    endcase
  end

  // ct_mode = combined transfer mode - xinc == 1 so can go big.
  always_comb s0_addr_next = s0.addr + (ct_mode ? s0_size : (i_desc.src.xaddrinc << i_desc.glb.trans_size));

  always_comb begin
    case (1'b1)
      s0_ld_ll   : s0_d.xstart = i_ll.addr;
      s0_ld_init : s0_d.xstart = i_desc.src.addr;
      s0_ld_y    : s0_d.xstart = s0.xstart + i_desc.src.yaddrstride;
      default    : s0_d.xstart = s0.xstart;
    endcase
  end

  // s0_sx_rem_q - source row bytes remaining
  // s0_sy_rem_q - source rows remaining
  // s0_dx_rem_q - destination row bytes remaining
  // s0_dy_rem_q - destination rows remaining - used for destination total calcs
  // s0_dt_rem_q - destination total bytes remaining - used for 2D cases

  always_comb begin
    case (1'b1)
      s0_ld_ll : begin
        s0_d.sx_rem = i_ll.size;
        s0_d.dx_rem = i_ll.size;
        s0_d.sy_rem = dma_size_t'(1);
      end
      s0_ld_init : begin
        s0_d.sx_rem = i_desc.src.xbytesize;
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.sy_rem = i_desc.glb.ytype == DSBL ? dma_size_t'(1) : i_desc.src.yrowsize;
      end
      s0_ld_start: begin
        s0_d.sx_rem = i_desc.src.xbytesize;
        s0_d.dx_rem = s0.dx_rem - s0_size; // may need to change this for 2D cont...
        s0_d.sy_rem = i_desc.src.yrowsize;
      end
      s0_ld_y    : begin
        s0_d.sx_rem = i_desc.src.xbytesize;
        s0_d.dx_rem = i_desc.dst.xbytesize;
        s0_d.sy_rem = s0.sy_rem > 0 ? s0.sy_rem - 'd1 : '0;
      end
      s0_ld_x    : begin
        s0_d.sx_rem = i_desc.src.xbytesize;
        s0_d.dx_rem = s0.dx_rem - s0_size;
        s0_d.sy_rem = s0.sy_rem;
      end
      s0_ld_next : begin
        s0_d.sx_rem = s0.sx_rem - s0_size;
        s0_d.dx_rem = s0.dx_rem - s0_size;
        s0_d.sy_rem = s0.sy_rem;
      end
      default : begin
        s0_d.sx_rem = s0.sx_rem;
        s0_d.dx_rem = s0.dx_rem;
        s0_d.sy_rem = s0.sy_rem;
      end
    endcase
  end

  always_comb s0_ld_drow = (s0.dt_rem <= s0_size) && |s0.dy_rem;

  always_comb begin
    case (1'b1)
      s0_ld_ll : begin
        s0_d.dt_rem = i_ll.size;
        s0_d.dy_rem = dma_size_t'(1);
      end
      s0_ld_init : begin
        s0_d.dt_rem = i_desc.dst.xbytesize;
        s0_d.dy_rem = i_desc.dst.yrowsize - 'd1;
      end
      s0_ld_drow : begin
        s0_d.dt_rem = s0.dt_rem - s0_size + i_desc.dst.xbytesize;
        s0_d.dy_rem = s0.dy_rem - 'd1;
      end
      default : begin
        s0_d.dt_rem = s0.dt_rem - s0_size;
        s0_d.dy_rem = s0.dy_rem;
      end
    endcase
  end

  always_comb s0_size = ct_mode ? s0.sx_rem : dma_size_t'(1) << i_desc.glb.trans_size;


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

  typedef struct packed {
    dma_addr_t     addr;
    dma_size_t     size;
  } pipestage_1_t;

  pipestage_1_t s1_us_d, s1_d, s1;

  typedef logic [5:0] burst_sel_t;
  typedef logic [6:0] burst_size_t;

  burst_sel_t  s1_burst_sel_addr;
  burst_sel_t  s1_burst_sel_size;
  burst_size_t s1_burst_addr;
  burst_size_t s1_burst_size;
  dma_size_t   s1_beat_size;
  dma_size_t   s1_xfsize_mask;
  dma_size_t   s1_lines;
  dma_size_t   s1_size;
  dma_size_t   s1_size_;
  logic        s1_last;

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
    .i_stall     (!i_alloc_gnt),
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

  always_comb s1_limit_n    = s1_lines_limit >= s1_lines_size;


  always_comb s1_lines      = s1_limit_n ? s1_lines_size : s1_lines_limit;
  always_comb s1_size       = s1_limit_n ? s1.size : s1_limit_size;

  always_comb s1_last       = s1_limit_n;

  always_comb s1_us_d = '{addr : s0.addr, size : s0_size};

  always_comb s1_d    = '{addr : s1.addr + s1_size,
                          size : s1.size - s1_size };

 /*
  always_comb s1_last = s1.size == s1_size;
  always_comb s1_beat_size      = ct_mode ? NUM_BYTES_PORT : (dma_size_t'(1) << i_desc.glb.trans_size);

  always_comb s1_burst_sel_addr = burst_sel_t'(s1.addr >> (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size));
  always_comb
    priority case (1'b1)
      s1_burst_sel_addr[0] : s1_burst_addr = 1;
      s1_burst_sel_addr[1] : s1_burst_addr = 2;
      s1_burst_sel_addr[2] : s1_burst_addr = 4;
      s1_burst_sel_addr[3] : s1_burst_addr = 8;
      s1_burst_sel_addr[4] : s1_burst_addr = 16;
      s1_burst_sel_addr[5] : s1_burst_addr = 32;
      default              : s1_burst_addr = 64;
    endcase

  always_comb s1_xfsize_mask = s1_beat_size - 'd1;
  always_comb s1_burst_sel_size = burst_sel_t'(s1.size >> (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size) )
                               + |(s1.size & s1_xfsize_mask);
  always_comb
    priority case (1'b1)
      s1_burst_sel_size[0] : s1_burst_size = 1;
      s1_burst_sel_size[1] : s1_burst_size = 2;
      s1_burst_sel_size[2] : s1_burst_size = 4;
      s1_burst_sel_size[3] : s1_burst_size = 8;
      s1_burst_sel_size[4] : s1_burst_size = 16;
      s1_burst_sel_size[5] : s1_burst_size = 32;
      default              : s1_burst_size = 64;
    endcase

  always_comb s1_lines = s1_burst_addr > s1_burst_size ? s1_burst_size : s1_burst_addr;
  always_comb s1_size_ = (s1_lines << (ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size)) - (s1.size & s1_xfsize_mask);
  always_comb s1_size  = s1_size_ > s1.size ? s1.size : s1_size_;
*/
  always_comb o_alloc_req = mv_req[1] && mv_gnt[1];
  always_comb o_alloc     = '{ offset : dma_bufline_idx_t'(s1.addr),
                               size   : dma_bufline_siz_t'(s1_size),
                               ct_mode: ct_mode,
                               xfer_size : i_desc.glb.trans_size,
                               len    : s1_lines,
                               rx_id  : ll_mode_q};



/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
///                                                               ///
/// PIPESTAGE 2                                                   ///
/// ===========                                                   ///
///                                                               ///
///    - Issue requrests to the port arbiters                     ///
///                                                               ///
/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

  dma_rd_xfer_t s2_us_d, s2_d, s2;
  dma_addr_t s2_mmu_addr;

  dma_mmu #( .dma_axi_addr_t(dma_addr_t)
  ) s_mmu (
   .i_clk,
   .i_rst_n,
   .i_stall(!i_src_xfer_gnt && valid[2]),
   .i_addr(s1.addr),
   .o_addr(s2_mmu_addr),
   .i_en(i_desc.glb.mmu_en),
   .i_cfg(i_mmu_cfg),
   .o_irq(o_mmu_irq)
  );

  always_comb s2_us_d     = '{ addr : s1.addr,
                               size : ct_mode ? $clog2(NUM_BYTES_PORT) : i_desc.glb.trans_size,
                               len  : s1_lines,
                               tid  : i_tid };

  always_comb s2_d        = s2;

  dma_pipeline_ctrl #(
    .dma_pipedata_t ( dma_rd_xfer_t )
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
    .i_stall     (!i_src_xfer_gnt),
    .i_last      (1'b1),
    .o_update    ()
  );

  always_comb mv_gnt[2] = 1'b1;

  always_comb begin
    o_src_xfer = s2;
    o_src_xfer.addr = s2_mmu_addr;
  end

  always_comb begin
    o_src_xfer_req = '0;
    o_src_xfer_req[dma_src_port_sel_t'(i_desc.src.port)] = valid[2];
  end

endmodule
