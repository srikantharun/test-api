// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA Channel
// Owner: Matt Morris <matt.morris@axelera.ai>

module dma_channel_buffer
  import dma_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
    parameter  int unsigned NUM_PORTS = 2,
    parameter  int unsigned DMA_N_BUF_IDXS = 256,
    parameter  int unsigned DMA_N_IMPL_BUF_IDXS = 256,
    localparam int unsigned DATA_RAM_DEPTH = DMA_N_IMPL_BUF_IDXS,
    localparam int unsigned DMA_PORT_DATA_W = 512,
    localparam int unsigned DATA_RAM_W = 128,
    localparam int unsigned DATA_RAM_INSTS_X = DMA_PORT_DATA_W/DATA_RAM_W,
    localparam type dma_buf_idx_t = logic [$clog2(DMA_N_BUF_IDXS)-1:0],
    localparam type dma_impl_buf_idx_t = logic [$clog2(DMA_N_IMPL_BUF_IDXS)-1:0]
)
(

    input  wire            i_clk,
    input  wire            i_rst_n,

    input  impl_inp_t [DATA_RAM_INSTS_X-1:0] i_impl,
    output impl_oup_t [DATA_RAM_INSTS_X-1:0] o_impl,

    input  logic           i_en,
    output logic           o_busy,
    input  logic [1:0]     i_overalloc_mode,
    output logic           o_dataloss_irq,

    input  logic           i_alloc_req,
    output logic           o_alloc_gnt,
    input  dma_alloc_t     i_alloc,
    output dma_tid_t       o_tid,

    input  logic [NUM_PORTS-1:0] i_src_resp_req,
    output logic [NUM_PORTS-1:0] o_src_resp_gnt,
    input  dma_rd_resp_t         i_src_resp      [NUM_PORTS],

    output logic [DMA_N_RX_IDS-1:0]     o_rx_data_req,
    input  logic [DMA_N_RX_IDS-1:0]     i_rx_data_gnt,
    output dma_bufdata_t   o_rx_data

);

  localparam int unsigned DMA_CHNL_OS_MAX = DMA_N_TIDS;

  dma_buf_idx_t alloc_ptr_q;
  dma_buf_idx_t rd_ptr_q;
  dma_buf_metadata_t [DMA_N_BUF_IDXS-1:0] meta_data_q, meta_data_d;
  dma_buf_metadata2_t [DMA_N_BUF_IDXS-1:0] meta_data_2_q;
  dma_buf_idx_t [DMA_CHNL_OS_MAX-1:0] tid_wr_ptr_q;
  dma_rx_id_t [DMA_CHNL_OS_MAX-1:0] tid_rx_id_q;
  logic alloc_gnt;
  logic tid_pop;

  logic resp_gnt;
  logic resp_req;
  typedef logic [$clog2(NUM_PORTS)-1:0] prt_idx_t;
  prt_idx_t resp_idx;
  logic chnl_wr_req_s0;
  logic chnl_wr_req_s1_q;
  dma_data_t chnl_wr_data_s1_q;
  dma_impl_buf_idx_t chnl_wr_ptr_s1_q;
  dma_buf_idx_t alloc_top_line;
  dma_bufline_siz_t alloc_tail_size;
  dma_bufline_siz_t alloc_head_size;
  //dma_bufline_siz_t alloc_line_bytes;
  dma_tid_t tid_fifo_rdaddr, tid_fifo_wraddr;
  logic [$clog2(DMA_N_TIDS):0] n_tid_used;
  logic tid_push;
  logic rd_en;
  dma_rd_resp_t resp;
  logic wr_req;
  logic wr_ovfl;
  dma_data_t read_data;
  logic rd_val_q;
  dma_buf_metadata_t rd_meta_q;
  dma_buf_metadata2_t rd_meta_2_q;
  logic [DMA_N_IMPL_BUF_IDXS-1:0] buf_val_q;
  logic [$clog2(DMA_N_IMPL_BUF_IDXS):0] buf_cnt_q;

  always_comb o_alloc_gnt = alloc_gnt;
  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    alloc_ptr_q <= '0;
    for (int unsigned I=0; I<DMA_CHNL_OS_MAX; I++) begin
      tid_wr_ptr_q[I] <= '0;
      tid_rx_id_q[I] <= '0;
    end
  end
  else begin
    if (tid_pop) begin
      alloc_ptr_q <= alloc_ptr_q + i_alloc.len + 1;
      tid_wr_ptr_q[o_tid] <= alloc_ptr_q;
      tid_rx_id_q[o_tid]  <= i_alloc.rx_id;
    end
    if (chnl_wr_req_s0) begin
      tid_wr_ptr_q[resp.tid] <= tid_wr_ptr_q[resp.tid] + 'd1;
    end
  end

  dma_bufline_siz_t meta_xfer_size_q, meta_xfer_size_d;
  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    for (int unsigned I=0; I<DMA_N_BUF_IDXS; I++)
      meta_data_q[I] <= '0;
  end
  else begin
    meta_data_q <= meta_data_d;
  end

  dma_bufline_siz_t xfer_size;
  dma_bufline_idx_t size_mask;
  dma_bufline_idx_t tail_offset;

  always_comb xfer_size = i_alloc.ct_mode ? DMA_PORT_DATA_W : dma_bufline_siz_t'(1) << i_alloc.xfer_size;
  always_comb size_mask = xfer_size - 'd1;
  always_comb alloc_top_line   = alloc_ptr_q + i_alloc.len;
  always_comb alloc_tail_size  = (i_alloc.offset + i_alloc.size) & size_mask;
  always_comb alloc_head_size  = (|i_alloc.len ? (DMA_PORT_DATA_W - i_alloc.offset) : i_alloc.size);// & size_mask;
  always_comb tail_offset      = i_alloc.offset + alloc_head_size;

  always_comb begin
    meta_data_d = meta_data_q;
    if (tid_pop) begin
        meta_data_d[alloc_ptr_q] = '{ offset : i_alloc.offset,
                                      //size   : dma_bufline_siz_t'(i_alloc.size) < alloc_line_bytes ? i_alloc.size : dma_bufline_idx_t'(alloc_line_bytes),
                                      size   : alloc_head_size,
                                      last   : !(|i_alloc.len) };

        if (|i_alloc.len)
          meta_data_d[dma_buf_metadata_t'(alloc_top_line)] = '{ offset : tail_offset,
                                                  size   : dma_bufline_idx_t'(alloc_tail_size),
                                                  last   : 1'b1};
    end
    if (rd_en)
      meta_data_d[rd_ptr_q] = '{ offset : '0,
                                 size   : '0,
                                 last   : 1'b0};
  end

  always_comb o_busy   = |{n_tid_used,buf_cnt_q};
  always_comb tid_push = resp_req && resp.last;
  always_comb alloc_gnt = n_tid_used <= DMA_N_TIDS && (i_overalloc_mode[1] || ((alloc_ptr_q - rd_ptr_q) <= DMA_N_IMPL_BUF_IDXS));
  always_comb tid_pop = alloc_gnt && i_alloc_req;

  dma_fifo_logic #( .FIFO_DEPTH (DMA_CHNL_OS_MAX),
                    .START_FULL (1'b1))
  u_tid_fifo_logic (
    .i_clk,
    .i_rst_n,

    .i_push   (tid_push),
    .o_full_n (),
    .i_pop    (tid_pop),
    .o_empty_n(tid_avail),
    .o_free_entries (n_tid_used),

    .o_wr_idx (tid_fifo_wraddr),
    .o_rd_idx (tid_fifo_rdaddr)
  );

  dma_tid_t tid_queue_q [DMA_CHNL_OS_MAX];

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    for (int I = 0; I < DMA_CHNL_OS_MAX; I++)
      tid_queue_q[I] <= dma_tid_t'(I);
  end
  else if (tid_push) begin
    tid_queue_q[tid_fifo_wraddr] <= resp.tid;
  end

  always_comb o_tid = tid_queue_q[tid_fifo_rdaddr];

  dma_port_arb #( .N_REQ (NUM_PORTS) )
  u_rd_port_arb
  (
    .i_clk,
    .i_rst_n,

    .i_req     (i_src_resp_req),
    .o_gnt     (o_src_resp_gnt),
    .i_last    (1'b1),

    .o_val     (resp_req),
    .o_idx     (resp_idx),
    .i_ack     (resp_gnt)
  );


  always_comb
    case(i_overalloc_mode)
      2'b11   : resp_gnt = !buf_val_q[dma_impl_buf_idx_t'(tid_wr_ptr_q[resp.tid])];
      default : resp_gnt = 1'b1;
    endcase

  always_comb
    case(i_overalloc_mode)
      2'b10   : o_dataloss_irq = buf_val_q[dma_impl_buf_idx_t'(tid_wr_ptr_q[resp.tid])];
      default : o_dataloss_irq = 1'b0;
    endcase


  always_comb resp  = i_src_resp[resp_idx];
  always_comb chnl_wr_req_s0 = resp_req && resp_gnt;


  always_ff @ (posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      chnl_wr_req_s1_q <= 1'b0;
      chnl_wr_ptr_s1_q <= '0;
      chnl_wr_data_s1_q <= '0;
      for (int unsigned I=0; I<DMA_N_BUF_IDXS; I++)
        meta_data_2_q[I] <= '0;
    end
    else if (chnl_wr_req_s0 || chnl_wr_req_s1_q) begin
      chnl_wr_req_s1_q <= chnl_wr_req_s0;
      chnl_wr_ptr_s1_q <= dma_impl_buf_idx_t'(tid_wr_ptr_q[resp.tid]);
      chnl_wr_data_s1_q <= resp.data;
      meta_data_2_q[dma_impl_buf_idx_t'(tid_wr_ptr_q[resp.tid])] <= '{ rx_id: tid_rx_id_q[resp.tid] };
    end
  end

  always_comb wr_req  = chnl_wr_req_s1_q && !buf_val_q[chnl_wr_ptr_s1_q];
  always_comb wr_ovfl = chnl_wr_req_s1_q &&  buf_val_q[chnl_wr_ptr_s1_q];


  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    buf_val_q <= '0;
  end
  else begin
    if (wr_req)
      buf_val_q[chnl_wr_ptr_s1_q] <= 1'b1;
    if (rd_en)
      buf_val_q[dma_impl_buf_idx_t'(rd_ptr_q)] <= 1'b0;
  end

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    buf_cnt_q <= '0;
  end
  else begin
    if (wr_req && !rd_en)
      buf_cnt_q <= buf_cnt_q + 'd1;
    else if (!wr_req && rd_en)
      buf_cnt_q <= buf_cnt_q - 'd1;
  end


  logic rx_data_gnt;


  for (genvar I = 0; I< DATA_RAM_INSTS_X; I++) begin: g_data_ram_x

    logic [DATA_RAM_W-1:0] ram_read_data;
    axe_tcl_ram_1rp_1wp #(
      .NumWords (DATA_RAM_DEPTH),
      .DataWidth(DATA_RAM_W),
      .ByteWidth(DATA_RAM_W),
      .ReadLatency  (1),
      .ImplKey  ("HS_RVT"),
      .impl_inp_t(impl_inp_t),
      .impl_oup_t(impl_oup_t)
    ) u_chnl_data_ram (
      .i_wr_clk   (i_clk),
      .i_wr_rst_n (i_rst_n),
      .i_wr_req   (wr_req),
      .i_wr_addr  (chnl_wr_ptr_s1_q),
      .i_wr_data  (chnl_wr_data_s1_q[DATA_RAM_W*I+:DATA_RAM_W]),
      .i_wr_mask  (1'b1),
      .i_rd_clk   (i_clk),
      .i_rd_rst_n (i_rst_n),
      .i_rd_req   (rd_en),
      .i_rd_addr  (dma_impl_buf_idx_t'(rd_ptr_q)),
      .o_rd_data  (ram_read_data),
      .i_impl     (i_impl[I]),
      .o_impl     (o_impl[I])
    );
    always_comb read_data[DATA_RAM_W*I+:DATA_RAM_W] = ram_read_data;
  end: g_data_ram_x

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    rd_ptr_q <= '0;
    rd_val_q <= '0;
    rd_meta_q <= '0;
    rd_meta_2_q <= '0;
  end
  else begin
    rd_val_q <= rd_en; // || (rd_val_q && !rx_data_gnt);
    if (rd_en) begin
      rd_ptr_q <= rd_ptr_q + 'd1;
      rd_meta_q <= meta_data_q[rd_ptr_q];
      rd_meta_2_q <= meta_data_2_q[rd_ptr_q];
    end
  end

  logic rd_spill_vld_q;
  dma_data_t rd_spill_dat_q;


  always_comb rd_en = buf_val_q[dma_impl_buf_idx_t'(rd_ptr_q)] && !rd_spill_vld_q && (!rd_val_q || rx_data_gnt);
  always_comb o_rx_data = '{ data : rd_spill_vld_q ? rd_spill_dat_q : read_data,
                             offset : rd_meta_q.offset,
                             size   : rd_meta_q.size };
  always_comb begin
    o_rx_data_req = '0;
    o_rx_data_req[rd_meta_2_q.rx_id] = (rd_val_q || rd_spill_vld_q);
  end


  always_comb rx_data_gnt = i_rx_data_gnt[rd_meta_2_q.rx_id];
  // Add Spill

  always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    rd_spill_dat_q <= '0;
    rd_spill_vld_q <= 1'b0;
  end
  else if (rd_val_q && !rx_data_gnt) begin
    rd_spill_dat_q <= read_data;
    rd_spill_vld_q <= 1'b1;
  end
  else if (rx_data_gnt) begin
    rd_spill_vld_q <= 1'b0;
  end

endmodule
