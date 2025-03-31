// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


/// TODO:__one_line_summary_of_dma_pkg__
///
package dma_pkg;

  typedef logic [63:0] dma_addr_t;
  typedef logic  [3:0] dma_xfer_size_t;
  typedef logic [31:0] dma_size_t;
  typedef logic [31:0] dma_inc_t;
  typedef logic [31:0] dma_stride_t;
  typedef logic  [1:0] dma_port_sel_t;

  parameter int unsigned MAX_OS = 64;
  typedef logic [$clog2(MAX_OS)-1:0] dma_osr_t;

  parameter int unsigned MAX_BURSTLEN = 256;
  typedef logic [$clog2(MAX_BURSTLEN)-1:0] dma_burstlen_t;

  typedef enum logic [3:0] { DSBL, CONT, WRAP, FILL,
                             RES4, RES5, RES6, RES7,
                             RES8, RES9, RES10, RES11,
                             RES12, RES13, RES14, RES15 } dma_type_e;


  typedef struct packed {
    dma_osr_t      osr_lmt;
    dma_burstlen_t max_burstlen;
    dma_stride_t   yaddrstride;
    dma_size_t     yrowsize;
    dma_inc_t      xaddrinc;
    dma_size_t     xbytesize;
    dma_addr_t     addr;
    dma_port_sel_t port;
  } dma_desc_end_t;

  typedef struct packed {
    dma_xfer_size_t trans_size;
    dma_type_e      ytype;
    dma_type_e      xtype;
    logic           mmu_en;
    logic           int_en;
    logic           fill_mode;
    logic [15:0]    fill_val;
  } dma_desc_glb_t;

  typedef struct packed {
    dma_port_sel_t  port;
    logic           ll_en;
    logic           ll_mode;
    logic           ll_last;
    dma_addr_t      ll_addr;
  } dma_desc_ll_t;

  typedef struct packed {
    logic [9:0]     xfer_attr_user;
    logic           xfer_attr_priv;
    logic           xfer_attr_nonsecure;
    logic [1:0]     xfer_attr_shareable;
    logic [3:0]     mem_attr_hi;
    logic [3:0]     mem_attr_lo;
  } dma_desc_transcfg_t;

  typedef struct packed {
    dma_desc_glb_t  glb;
    dma_desc_transcfg_t dst_xfer;
    dma_desc_transcfg_t src_xfer;
    dma_desc_ll_t   ll;
    dma_desc_end_t  dst;
    dma_desc_end_t  src;
  } dma_desc_t;


  typedef logic [6:0] dma_ll_size_t;

  typedef struct packed {
    dma_addr_t addr;
    dma_ll_size_t size;
  } dma_ll_t;


  typedef struct packed {
    logic mode;
  } dma_global_cfg_t;

  typedef struct packed {
    logic busy;
  } dma_global_sts_t;

  //parameter int unsigned DMA_BUF_DEPTH      = 256;
  //parameter int unsigned DMA_BUF_IMPL_DEPTH = 256;
  //parameter int unsigned DMA_BUF_IDX_W = $clog2(DMA_BUF_DEPTH);
  //parameter int unsigned DMA_BUF_IMPL_IDX_W = $clog2(DMA_BUF_IMPL_DEPTH);
  parameter int unsigned DMA_N_TIDS = 64;
  parameter int unsigned DMA_DATA_W = 512;
  parameter int unsigned DMA_DATA_BYTE_W = DMA_DATA_W/8;
  parameter int unsigned DMA_MAX_BURST = 64;
  parameter int unsigned DMA_PAGE_SIZE  = 4096;
  parameter int unsigned DMA_PAGE_SIZE_BITS = $clog2(DMA_PAGE_SIZE);

  //typedef logic [DMA_BUF_IDX_W-1:0]        dma_bufidx_t;
  //typedef logic [DMA_BUF_IMPL_IDX_W-1:0]   dma_buframidx_t;
  typedef logic [$clog2(DMA_DATA_BYTE_W)-1:0]               dma_bufline_idx_t;
  typedef logic [$clog2(DMA_DATA_BYTE_W):0]                 dma_bufline_siz_t;
  typedef logic [$clog2(DMA_MAX_BURST)-1:0]        dma_len_t;
  typedef logic [$clog2(DMA_N_TIDS)-1:0]           dma_tid_t;
  typedef logic [DMA_DATA_W-1:0]                   dma_data_t;
  typedef logic [(DMA_DATA_W/8)-1:0]               dma_be_t;

  parameter int unsigned DMA_N_RX_IDS = 2;
  typedef logic [$clog2(DMA_N_RX_IDS)-1:0] dma_rx_id_t;
  parameter dma_rx_id_t DMA_RX_ID_DST = dma_rx_id_t'(0);
  parameter dma_rx_id_t DMA_RX_ID_LL  = dma_rx_id_t'(1);

  typedef struct packed {
    dma_addr_t addr;
    dma_xfer_size_t size;
    dma_len_t  len;
    dma_tid_t  tid;
  } dma_rd_xfer_t;

  typedef struct packed {
    dma_tid_t tid;
    dma_data_t data;
    logic      last;
  } dma_rd_resp_t;

  typedef struct packed {
    dma_addr_t addr;
    dma_xfer_size_t size;
    dma_len_t  len;
    logic      first;
    dma_tid_t  tid;
    dma_be_t   be;
    dma_data_t data;
    logic      last;
  } dma_wr_xfer_t;

  typedef struct packed {
    dma_tid_t tid;
  } dma_wr_resp_t;

  typedef struct packed {
    dma_bufline_idx_t offset;
    dma_bufline_siz_t size;
    logic             ct_mode;
    dma_xfer_size_t   xfer_size;
    dma_len_t         len;
    dma_rx_id_t       rx_id;
  } dma_alloc_t;

  typedef struct packed {
    dma_data_t data;
    dma_bufline_idx_t offset;
    dma_bufline_idx_t size;
  } dma_bufdata_t;

  typedef struct packed {
    dma_bufline_idx_t offset;
    dma_bufline_siz_t size;
    logic             last;
  } dma_buf_metadata_t;

  typedef struct packed {
    dma_rx_id_t     rx_id;
  } dma_buf_metadata2_t;

  typedef struct packed {
    logic active;
  } dma_chnl_sts_t;

  parameter int unsigned DMA_CMD_N_FORMATS = 5;
  parameter int unsigned DMA_CMD_SIZE = 'h240;  // CMD without token, 9 x 8 = 72B  = 10 0100 0000

  typedef logic [$clog2(DMA_CMD_N_FORMATS)-1:0] dma_cmd_format_t;
  typedef logic [DMA_CMD_SIZE-1:0] dma_cmd_data_t;

  parameter int unsigned WORD_W = 64;

  function automatic dma_desc_t decode_cmd_f (dma_cmd_data_t data, dma_cmd_format_t fmt, dma_desc_t q);
    dma_desc_t d;
    d = q;
    case (fmt)
      // FMT = 0
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORD[4] = CH_CFG
      // WORD[5] = CH_CTRL
      dma_cmd_format_t'(0) : begin
        d.glb.trans_size   =              data[ 4 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( DSBL );
        d.glb.xtype        = dma_type_e'( data[ 4 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 5 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 5 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 4 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 4 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 5 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 5 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 5 * WORD_W + 29 +:  2 ];
        d.dst.osr_lmt      =              data[ 5 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 4 * WORD_W + 40 +:  8 ];
        d.dst.yaddrstride  = '0;
        d.dst.yrowsize     = dma_size_t'( 1 );
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 5 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 5 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 4 * WORD_W + 32 +:  8 ];
        d.src.yaddrstride  = '0;
        d.src.yrowsize     = dma_size_t'( 1 );
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 32 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 16 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 5 * WORD_W + 25 +:  2 ];
      end

      // FMT = 1
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORK[4] = TRANS_CFG
      // WORD[5] = CH_CFG
      // WORD[6] = CH_CTRL
      dma_cmd_format_t'(1) : begin
        d.glb.trans_size   =              data[ 5 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( DSBL );
        d.glb.xtype        = dma_type_e'( data[ 5 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 6 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 6 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 5 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 5 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 6 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 6 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 6 * WORD_W + 29 +:  2 ];
        d.dst_xfer.xfer_attr_user       = data[ 4 * WORD_W + 48 +: 10 ];
        d.dst_xfer.xfer_attr_priv       = data[ 4 * WORD_W + 43 +:  1 ];
        d.dst_xfer.xfer_attr_nonsecure  = data[ 4 * WORD_W + 42 +:  1 ];
        d.dst_xfer.xfer_attr_shareable  = data[ 4 * WORD_W + 40 +:  2 ];
        d.dst_xfer.mem_attr_hi          = data[ 4 * WORD_W + 36 +:  4 ];
        d.dst_xfer.mem_attr_lo          = data[ 4 * WORD_W + 32 +:  4 ];
        d.src_xfer.xfer_attr_user       = data[ 4 * WORD_W + 16 +: 10 ];
        d.src_xfer.xfer_attr_priv       = data[ 4 * WORD_W + 11 +:  1 ];
        d.src_xfer.xfer_attr_nonsecure  = data[ 4 * WORD_W + 10 +:  1 ];
        d.src_xfer.xfer_attr_shareable  = data[ 4 * WORD_W +  8 +:  2 ];
        d.src_xfer.mem_attr_hi          = data[ 4 * WORD_W +  4 +:  4 ];
        d.src_xfer.mem_attr_lo          = data[ 4 * WORD_W +  0 +:  4 ];
        d.dst.osr_lmt      =              data[ 6 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 5 * WORD_W + 40 +:  8 ];
        d.dst.yaddrstride  = '0;
        d.dst.yrowsize     = dma_size_t'( 1 );
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 6 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 6 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 5 * WORD_W + 32 +:  8 ];
        d.src.yaddrstride  = '0;
        d.src.yrowsize     = dma_size_t'( 1 );
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 32 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 16 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 6 * WORD_W + 25 +:  2 ];
      end

      // FMT = 2
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORK[4] = YROWSIZE
      // WORK[5] = YADDRSTRIDE
      // WORD[6] = CH_CFG
      // WORD[7] = CH_CTRL
      dma_cmd_format_t'(2) : begin
        d.glb.trans_size   =              data[ 6 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( data[ 6 * WORD_W +  8 +:  4 ] );
        d.glb.xtype        = dma_type_e'( data[ 6 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 7 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 7 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 6 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 6 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 7 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 7 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 7 * WORD_W + 29 +:  2 ];
        d.dst.osr_lmt      =              data[ 7 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 6 * WORD_W + 40 +:  8 ];
        d.dst.yaddrstride  =              data[ 5 * WORD_W + 32 +: 32 ];
        d.dst.yrowsize     =              data[ 4 * WORD_W + 32 +: 32 ];
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 7 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 7 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 6 * WORD_W + 32 +:  8 ];
        d.src.yaddrstride  =              data[ 5 * WORD_W +  0 +: 32 ];
        d.src.yrowsize     =              data[ 4 * WORD_W +  0 +: 32 ];
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 32 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 16 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 7 * WORD_W + 25 +:  2 ];
      end

      // FMT = 3
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORK[4] = YROWSIZE
      // WORK[5] = YADDRSTRIDE
      // WORK[6] = TRANS_CFG
      // WORD[7] = CH_CFG
      // WORD[8] = CH_CTRL
      dma_cmd_format_t'(3) : begin
        d.glb.trans_size   =              data[ 7 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( data[ 7 * WORD_W +  8 +:  4 ] );
        d.glb.xtype        = dma_type_e'( data[ 7 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 8 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 8 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 7 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 7 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 8 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 8 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 8 * WORD_W + 29 +:  2 ];
        d.dst_xfer.xfer_attr_user       = data[ 6 * WORD_W + 48 +: 10 ];
        d.dst_xfer.xfer_attr_priv       = data[ 6 * WORD_W + 43 +:  1 ];
        d.dst_xfer.xfer_attr_nonsecure  = data[ 6 * WORD_W + 42 +:  1 ];
        d.dst_xfer.xfer_attr_shareable  = data[ 6 * WORD_W + 40 +:  2 ];
        d.dst_xfer.mem_attr_hi          = data[ 6 * WORD_W + 36 +:  4 ];
        d.dst_xfer.mem_attr_lo          = data[ 6 * WORD_W + 32 +:  4 ];
        d.src_xfer.xfer_attr_user       = data[ 6 * WORD_W + 16 +: 10 ];
        d.src_xfer.xfer_attr_priv       = data[ 6 * WORD_W + 11 +:  1 ];
        d.src_xfer.xfer_attr_nonsecure  = data[ 6 * WORD_W + 10 +:  1 ];
        d.src_xfer.xfer_attr_shareable  = data[ 6 * WORD_W +  8 +:  2 ];
        d.src_xfer.mem_attr_hi          = data[ 6 * WORD_W +  4 +:  4 ];
        d.src_xfer.mem_attr_lo          = data[ 6 * WORD_W +  0 +:  4 ];
        d.dst.osr_lmt      =              data[ 8 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 7 * WORD_W + 40 +:  8 ];
        d.dst.yaddrstride  =              data[ 5 * WORD_W + 32 +: 32 ];
        d.dst.yrowsize     =              data[ 4 * WORD_W + 32 +: 32 ];
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 8 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 8 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 7 * WORD_W + 32 +:  8 ];
        d.src.yaddrstride  =              data[ 5 * WORD_W +  0 +: 32 ];
        d.src.yrowsize     =              data[ 4 * WORD_W +  0 +: 32 ];
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 32 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 16 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 8 * WORD_W + 25 +:  2 ];
      end

      // FMT = 4
      // WORD[0] = LINK_DESC
      // WORD[1] = CH_CTRL
      dma_cmd_format_t'(4) : begin
        d.glb.mmu_en       =              data[ 1 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 1 * WORD_W +  8 +:  1 ];
        d.ll.port          =              data[ 1 * WORD_W + 29 +:  2 ];
        d.ll.ll_en         =              data[ 1 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 1 * WORD_W + 49 +:  1 ];
        d.ll.ll_last       =              data[ 0 * WORD_W +  0 +:  1 ];
        d.ll.ll_addr       =            { data[ 0 * WORD_W +  3 +: 61 ], 3'b000 };
        d.dst.osr_lmt      =              data[ 1 * WORD_W + 19 +:  6 ];
        d.dst.port         =              data[ 1 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 1 * WORD_W + 13 +:  6 ];
        d.src.port         =              data[ 1 * WORD_W + 25 +:  2 ];
      end
    default: ; // null
    endcase

    return d;
  endfunction

  // obs struct
  typedef struct packed {
    logic [1:0] state;
    logic token_stall;
    logic dp_instr_stall;
  } dma_dev_obs_t;

  typedef logic [639:0] dma_ll_data_t;

  function automatic dma_desc_t decode_ll_f (dma_ll_data_t data, dma_desc_t q);
    dma_desc_t d;
    d = q;
    case (q.ll.ll_mode)
      1'b1 : begin
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORK[4] = YROWSIZE
      // WORK[5] = YADDRSTRIDE
      // WORK[6] = TRANS_CFG
      // WORD[7] = CH_CFG
      // WORD[8] = CH_CTRL
      // WORD[9] = LL
        d.glb.trans_size   =              data[ 7 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( data[ 7 * WORD_W +  8 +:  4 ] );
        d.glb.xtype        = dma_type_e'( data[ 7 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 8 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 8 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 7 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 7 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 8 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 8 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 8 * WORD_W + 29 +:  2 ];
        d.dst_xfer.xfer_attr_user       = data[ 6 * WORD_W + 48 +: 10 ];
        d.dst_xfer.xfer_attr_priv       = data[ 6 * WORD_W + 43 +:  1 ];
        d.dst_xfer.xfer_attr_nonsecure  = data[ 6 * WORD_W + 42 +:  1 ];
        d.dst_xfer.xfer_attr_shareable  = data[ 6 * WORD_W + 40 +:  2 ];
        d.dst_xfer.mem_attr_hi          = data[ 6 * WORD_W + 36 +:  4 ];
        d.dst_xfer.mem_attr_lo          = data[ 6 * WORD_W + 32 +:  4 ];
        d.src_xfer.xfer_attr_user       = data[ 6 * WORD_W + 16 +: 10 ];
        d.src_xfer.xfer_attr_priv       = data[ 6 * WORD_W + 11 +:  1 ];
        d.src_xfer.xfer_attr_nonsecure  = data[ 6 * WORD_W + 10 +:  1 ];
        d.src_xfer.xfer_attr_shareable  = data[ 6 * WORD_W +  8 +:  2 ];
        d.src_xfer.mem_attr_hi          = data[ 6 * WORD_W +  4 +:  4 ];
        d.src_xfer.mem_attr_lo          = data[ 6 * WORD_W +  0 +:  4 ];
        d.dst.osr_lmt      =              data[ 8 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 7 * WORD_W + 40 +:  8 ];
        d.dst.yaddrstride  =              data[ 5 * WORD_W + 32 +: 32 ];
        d.dst.yrowsize     =              data[ 4 * WORD_W + 32 +: 32 ];
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 8 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 8 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 7 * WORD_W + 32 +:  8 ];
        d.src.yaddrstride  =              data[ 5 * WORD_W +  0 +: 32 ];
        d.src.yrowsize     =              data[ 4 * WORD_W +  0 +: 32 ];
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 32 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 16 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 8 * WORD_W + 25 +:  2 ];
        d.ll.ll_last       =              data[ 9 * WORD_W +  0 +:  1 ];
        d.ll.ll_addr       =            { data[ 9 * WORD_W +  3 +: 61 ], 3'b000 };
      end
      default : begin
      // WORD[0] = SRC ADDR
      // WORD[1] = DST ADDR
      // WORD[2] = XBYTESIZE
      // WORK[3] = XADDRINC
      // WORD[4] = CH_CFG
      // WORD[5] = CH_CTRL
      // WORD[6] = LL
        d.glb.trans_size   =              data[ 4 * WORD_W +  0 +:  4 ];
        d.glb.ytype        = dma_type_e'( DSBL );
        d.glb.xtype        = dma_type_e'( data[ 4 * WORD_W +  4 +:  4 ] );
        d.glb.mmu_en       =              data[ 5 * WORD_W + 31 +:  1 ];
        d.glb.int_en       =              data[ 5 * WORD_W +  8 +:  1 ];
        d.glb.fill_mode    =              data[ 4 * WORD_W + 12 +:  1 ];
        d.glb.fill_val     =              data[ 4 * WORD_W + 16 +: 16 ];
        d.ll.ll_en         =              data[ 5 * WORD_W + 48 +:  1 ];
        d.ll.ll_mode       =              data[ 5 * WORD_W + 49 +:  1 ];
        d.ll.port          =              data[ 5 * WORD_W + 29 +:  2 ];
        d.dst.osr_lmt      =              data[ 5 * WORD_W + 19 +:  6 ];
        d.dst.max_burstlen =              data[ 4 * WORD_W + 40 +:  8 ];
        d.dst.xaddrinc     =              data[ 3 * WORD_W + 32 +: 32 ];
        d.dst.xbytesize    =              data[ 2 * WORD_W + 32 +: 16 ];
        d.dst.addr         =              data[ 1 * WORD_W +  0 +: 64 ];
        d.dst.port         =              data[ 5 * WORD_W + 27 +:  2 ];
        d.src.osr_lmt      =              data[ 5 * WORD_W + 13 +:  6 ];
        d.src.max_burstlen =              data[ 4 * WORD_W + 32 +:  8 ];
        d.src.xaddrinc     =              data[ 3 * WORD_W +  0 +: 16 ];
        d.src.xbytesize    =              data[ 2 * WORD_W +  0 +: 32 ];
        d.src.addr         =              data[ 0 * WORD_W +  0 +: 64 ];
        d.src.port         =              data[ 5 * WORD_W + 25 +:  2 ];
        d.ll.ll_last       =              data[ 6 * WORD_W +  0 +:  1 ];
        d.ll.ll_addr       =            { data[ 6 * WORD_W +  3 +: 61 ], 3'b000 };
      end
    endcase
    return d;
  endfunction


  typedef enum int {
    common_csr_idx = 0,
    mmu_base_idx = 1, // base, idx will be base + 3*ch_nr
    ch_cmdb_base_idx = 2, // base, idx will be base + 3*ch_nr
    ch_csr_base_idx = 3 // base, idx will be base + 3*ch_nr
  } dev_ep_idx_e;

  parameter int unsigned DmaMaxNrChannels = 4;
  parameter int unsigned DmaMaxRegions = 1 + 3*DmaMaxNrChannels;
  typedef longint dma_max_region_t[DmaMaxRegions];

  parameter dma_addr_t DMA_MMU_ADDR_MASK = 'h00fff;
  parameter dma_addr_t DMA_CMD_ADDR_MASK = 'h00fff;
  parameter dma_addr_t DMA_CSR_ADDR_MASK = 'h00fff;

  parameter longint DmaMmuCsrOffset = 'h1000;
  parameter longint DmaChCsrOffset = 'h2000;
  parameter longint DmaChCmdbOffset = 'h2000;

  function automatic dma_max_region_t get_default_addr(bit is_end);
    get_default_addr[common_csr_idx] = 'h10000 + (is_end ? 'hffff : 'h0);
    for (int ch=0; ch<DmaMaxNrChannels; ch++) begin
      longint offset = is_end ? 'hfff : 'h0;
      get_default_addr[mmu_base_idx     + 3*ch] = 'h00000 + (ch * DmaMmuCsrOffset) + offset;
      get_default_addr[ch_cmdb_base_idx + 3*ch] = 'h20000 + (ch * DmaChCsrOffset)  + offset;
      get_default_addr[ch_csr_base_idx  + 3*ch] = 'h21000 + (ch * DmaChCmdbOffset) + offset;
    end
  endfunction

  typedef bit dma_max_priv_t[DmaMaxRegions];
  function automatic dma_max_priv_t get_default_priv();
    get_default_priv[common_csr_idx] = 1'b0;
    for (int ch=0; ch<DmaMaxNrChannels; ch++) begin
      get_default_priv[mmu_base_idx     + 3*ch] = 1'b1;
      get_default_priv[ch_cmdb_base_idx + 3*ch] = 1'b0;
      get_default_priv[ch_csr_base_idx  + 3*ch] = 1'b0;
    end
  endfunction

  parameter dma_max_region_t DmaDefaultRegionStAddr   = get_default_addr(0);
  parameter dma_max_region_t DmaDefaultRegionEndAddr  = get_default_addr(1);
  parameter dma_max_priv_t DmaDefaultRegionPrivileged = get_default_priv();

endpackage
