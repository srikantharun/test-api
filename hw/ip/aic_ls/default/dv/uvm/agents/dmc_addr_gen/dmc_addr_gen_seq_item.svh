`ifndef DMC_ADDR_GEN_SEQ_ITEM
`define DMC_ADDR_GEN_SEQ_ITEM

class dmc_addr_gen_seq_item extends uvm_sequence_item;
  `uvm_object_utils(dmc_addr_gen_seq_item)

  // Rand variables
  // header parameters
  rand bit[ 7:0] header_triggers;  // doesn't affect inner works
  rand bit[15:0] header_token_consumer;  // handled in ifd_odr_seq.
  rand bit[15:0] header_token_producer;  // handled in ifd_odr_seq.
  rand bit[ 7:0] header_cmd_format;  // need to understand what's going on here.
  rand bit       header_vector_mode; // affects int8/int16 formatting

  // rest
  rand bit[31:0] m_mem_stride_d;
  rand bit[31:0] m_mem_stride_c;
  rand bit[31:0] m_mem_stride_b;
  rand bit[31:0] m_mem_stride_a;
  rand bit signed[15:0] m_outer_stride_d;
  rand bit signed[15:0] m_outer_stride_c;
  rand bit signed[15:0] m_outer_stride_b;
  rand bit signed[15:0] m_outer_stride_a;
  rand bit signed[15:0] m_inner_stride_d;
  rand bit signed[15:0] m_inner_stride_c;
  rand bit signed[15:0] m_inner_stride_b;
  rand bit signed[15:0] m_inner_stride_a;
  rand bit[15:0] m_outer_length_d;
  rand bit[15:0] m_outer_length_c;
  rand bit[15:0] m_outer_length_b;
  rand bit[15:0] m_outer_length_a;
  rand bit[15:0] m_inner_length_d;
  rand bit[15:0] m_inner_length_c;
  rand bit[15:0] m_inner_length_b;
  rand bit[15:0] m_inner_length_a;
  rand bit[15:0] m_dim_width_d;
  rand bit[15:0] m_dim_width_c;
  rand bit[15:0] m_dim_width_b;
  rand bit[15:0] m_dim_width_a;
  rand bit signed[15:0] m_dim_offset_d;
  rand bit signed[15:0] m_dim_offset_c;
  rand bit signed[15:0] m_dim_offset_b;
  rand bit signed[15:0] m_dim_offset_a;

  rand bit[31:0] m_mem_bsize;
  rand bit       m_decomp_en;
  rand bit       m_pad_mode;
  rand bit       m_format;
  rand bit[ 1:0] m_vtrsp_mode;
  rand bit[ 1:0] m_vect_dim;
  rand bit[23:0] m_ring_buff_size;
  rand bit[31:0] m_mem_offset;
  rand bit[ 7:0] m_mask_end;
  rand bit[ 7:0] m_mask_start;
  rand bit signed[15:0]       m_pad_val;
  rand bit signed[15:0]       m_intra_pad_val;
  rand bit[31:0] m_mem_baseaddr;

  // Seetings byte
  rand bit[ 7:0]      m_settings;
  // Linear settings only
  rand bit[15:0]      m_length;
  rand bit[ 7:0]      m_lin_settings;
  // Def based and offset based only
  rand bit[ 7:0]      m_num_dim;
  rand bit[ 1:0]      m_num_dim_in_cmd;
  rand bit[ 7:0]      m_loop_def_ptr;
  rand bit[ 7:0]      m_dim_def_ptr;

  rand addr_gen_cmdformat_t  m_cmd_format;

  // rand reserved variables (no impact, total random, for toggle coverage)
  rand bit[7:0] header_reserved_a; // reserved bits
  rand bit[6:0] header_reserved_b; // reserved bits
  rand bit[7:0] m_rsrv_linear;
  rand bit[2:0] m_rsrv_settings;
  rand bit[6:0] m_rsrv_lin_settings;
  rand bit[7:0] m_rsrv_def_based_outer_a;
  rand bit[7:0] m_rsrv_def_based_outer_b;
  rand bit[7:0] m_rsrv_def_based_outer_c;
  rand bit[7:0] m_rsrv_def_based_outer_d;
  rand bit[7:0] m_rsrv_def_based_inner_a;
  rand bit[7:0] m_rsrv_def_based_inner_b;
  rand bit[7:0] m_rsrv_def_based_inner_c;
  rand bit[7:0] m_rsrv_def_based_inner_d;
  rand bit[15:0] m_rsrv_def_based_offset_a;
  rand bit[15:0] m_rsrv_def_based_offset_b;
  rand bit[15:0] m_rsrv_def_based_offset_c;
  rand bit[15:0] m_rsrv_def_based_offset_d;
  rand bit[7:0]  m_rsrv_3dimfallback_word_3;
  rand bit[15:0] m_rsrv_4dimfallback_word_3;
  rand bit[15:0] m_rsrv_dim_offset_a;
  rand bit[15:0] m_rsrv_dim_offset_b;
  rand bit[15:0] m_rsrv_dim_offset_c;
  rand bit[15:0] m_rsrv_dim_offset_d;

  rand bit m_high_mbsize;
  rand bit m_memstride_wrt_dim_width; // random variable to whether mem_stride will be computed based on dim width

  // Non rand variables
  bit[63:0]           m_header;
  addr_gen_cmd_t      m_cmd;
  bit                 m_reset_an_i;
  bit                 m_has_cmd;
  bit                 m_has_dpc_cmd;
  dpc_cmd_t           m_dpc_cmd;
  mem_baseaddr_t      m_l1_base_addr;

  cfg_data_t          m_cmd_q[$];
  cfg_data_t          m_dim_def_q[$];
  cfg_data_t          m_loop_def_q[$];

  int unsigned        iteration;  // simple tool when you need to be able to follow the refmodel

  // for coverage use only
  int unsigned m_pword_len;

  constraint C_NUM_DIM {
    m_num_dim >= 1 && m_num_dim <= 4;
    (m_cmd_format == CMDFORMAT_LINEAR) -> m_num_dim == 1;
    (m_cmd_format == CMDFORMAT_3DIM_FALLBACK) -> m_num_dim == 3;
    (m_cmd_format == CMDFORMAT_4DIM_FALLBACK) -> m_num_dim == 4;
    (m_cmd_format == CMDFORMAT_DEF_BASED) ->  soft m_num_dim dist { 1:= 10, 2:= 20, 3:=30, 4:=40};
    (m_cmd_format == CMDFORMAT_OFFSET_BASED) -> soft m_num_dim dist { 1:= 10, 2:= 20, 3:=30, 4:=40};
  }

  constraint C_NUM_DIM_IN_CMD {
    m_num_dim_in_cmd == m_num_dim-1;
  }

  constraint C_LINEAR_LENGTH {
    m_length > 0;
  }

  constraint C_PAD_MODE_DEFAULT {
    (m_cmd_format== CMDFORMAT_LINEAR) -> soft m_pad_mode == 0;
  }

  constraint C_PAD_VAL_DEFAULT {
    (m_cmd_format == CMDFORMAT_LINEAR) -> soft m_pad_val == 0;  // 16 bits signed int
    (m_cmd_format != CMDFORMAT_LINEAR) -> soft m_pad_val inside {[-32768:32767]};  // 16 bits signed int
  }

  constraint C_INTRA_PAD_VAL_DEFAULT {
    (m_cmd_format == CMDFORMAT_LINEAR) -> soft m_intra_pad_val == 0;  // 16 bits signed int
    (m_cmd_format != CMDFORMAT_LINEAR) -> soft m_intra_pad_val inside {[-32768:32767]};  // 16 bits signed int
  }


  constraint C_VECTOR_MODE_DEFAULT {
    (m_cmd_format == CMDFORMAT_LINEAR) -> soft header_vector_mode == 0;  // in linear mode, vector mode is always 0
  }

  constraint C_FORMAT_DEFAULT {
    (m_cmd_format == CMDFORMAT_LINEAR || header_vector_mode == 0) -> soft m_format == 0;  // in linear mode, format is always 0, in addition, if vector_mode = 0, format can't be 1
  }

  constraint C_MASK_DEFAULT {
    soft m_mask_start dist { 0:=80, [1:63]:/ 20};
    soft m_mask_end  dist { 64:=80, [0:63]:/ 20};
    m_mask_start <= m_mask_end;
    (m_format == 1) -> soft m_mask_end  <= 32;  // in case of pword32int16, there's only 32 words, so mask should be up to 32
  }

  constraint C_VTRSP_DEFAULT {
    soft m_vtrsp_mode == 0;
  }

  constraint C_VTRSP_WRT_LEN {
    (m_vtrsp_mode != 0 && m_num_dim==4) -> soft (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_inner_length_d * m_outer_length_a * m_outer_length_b * m_outer_length_c * m_outer_length_d) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==3) -> soft (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_outer_length_a * m_outer_length_b * m_outer_length_c) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==2) -> soft (m_inner_length_a * m_inner_length_b * m_outer_length_a * m_outer_length_b) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
    (m_vtrsp_mode != 0 && m_num_dim==1) -> soft (m_inner_length_a * m_outer_length_a) % (PWORD_ALIGN_SIZE/(2**(m_vtrsp_mode-1))) == 0;
  }

  constraint C_VTRSP_WRT_NUM_DIM {
    (m_vtrsp_mode != 0) -> soft m_num_dim  dist { 1:=10, 2:=20, 3:=30, 4:=40};
  }

  constraint C_VECTDIM_DEFAULT {
    (m_num_dim == 1) -> soft m_vect_dim  dist { 0:=80, [1:3]:/ 20};     // 80% legal values
    (m_num_dim == 2) -> soft m_vect_dim  dist { [0:1]:/80, [2:3]:/ 20}; // 80% legal values
    (m_num_dim == 3) -> soft m_vect_dim  dist { [0:2]:/80, 3:= 20};    // 80% legal values
    (m_num_dim == 4) -> soft m_vect_dim  <= 3;
  }

  constraint C_MEM_OFFSET_DEFAULT{
    soft m_mem_offset == 0;
  }

  constraint C_RINGBUFF_SIZE_DEFAULT{
    soft m_ring_buff_size == 0;
  }

  constraint C_DECOMPRESSION_DEFAULT {
    soft m_decomp_en == 0;
  }

  constraint C_DESCMEM_PTR_DEFAULT {
    m_loop_def_ptr != m_dim_def_ptr;
    m_dim_def_ptr + m_num_dim <= 127;
    m_loop_def_ptr + m_num_dim <= 127;
    (m_dim_def_ptr > m_loop_def_ptr) -> (m_loop_def_ptr + m_num_dim <= m_dim_def_ptr);
    (m_dim_def_ptr < m_loop_def_ptr) -> (m_loop_def_ptr >= m_dim_def_ptr + m_num_dim);
  }

  // Linear/ 1D constraint
  constraint C_LINEAR_FORMAT {
    (m_cmd_format == CMDFORMAT_LINEAR) -> soft m_lin_settings == m_decomp_en;
  }

  constraint C_1D_DIM_WIDTH_DEFAULT {
    (m_num_dim == 1) -> soft m_dim_width_a dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 1 && m_pad_mode==1) -> soft m_dim_width_a > 0;
  }

  constraint C_1D_DIM_OFFSET_DEFAULT {
    (m_num_dim == 1 && m_vtrsp_mode == 0) -> soft m_dim_offset_a dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 1 && m_vtrsp_mode != 0) -> soft m_dim_offset_a dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 1) -> m_dim_offset_b == 0;
    (m_num_dim == 1) -> m_dim_offset_c == 0;
    (m_num_dim == 1) -> m_dim_offset_d == 0;
  }

  constraint C_1D_MEM_STRIDE_DEFAULT {
    (m_num_dim == 1) -> soft m_mem_stride_a dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
  }

  constraint C_1D_OUTER_LENGTH_DEFAULT {
    (m_num_dim == 1) -> soft m_outer_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_1D_INNER_LENGTH_DEFAULT {
    (m_num_dim == 1) -> soft m_inner_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_1D_OUTER_STRIDE_DEFAULT {
    (m_num_dim == 1) -> soft m_outer_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_1D_INNER_STRIDE_DEFAULT {
    (m_num_dim == 1) -> soft m_inner_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_1D_MEM_BSIZE_DEFAULT {
    (m_num_dim == 1) -> soft m_mem_bsize == m_dim_width_a * m_mem_stride_a; // a x 64
  }

  // 2D constraint
  constraint C_2D_DIM_WIDTH_DEFAULT {
    (m_num_dim == 2) -> soft m_dim_width_a dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 2) -> soft m_dim_width_b dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 2 && m_pad_mode==1) -> soft m_dim_width_a > 0;
    (m_num_dim == 2 && m_pad_mode==1) -> soft m_dim_width_b > 0;
  }

  constraint C_2D_DIM_OFFSET_DEFAULT {
    (m_num_dim == 2 && m_vtrsp_mode == 0) -> soft m_dim_offset_a dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 2 && m_vtrsp_mode != 0) -> soft m_dim_offset_a dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 2 && m_vtrsp_mode == 0) -> soft m_dim_offset_b dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 2 && m_vtrsp_mode != 0) -> soft m_dim_offset_b dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 2) -> m_dim_offset_c == 0;
    (m_num_dim == 2) -> m_dim_offset_d == 0;
  }

  constraint C_2D_MEM_STRIDE_DEFAULT {
    (m_num_dim == 2) -> soft m_mem_stride_b dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 2 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_a == m_dim_width_b * m_mem_stride_b;
    (m_num_dim == 2 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_a dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
  }

  constraint C_2D_OUTER_LENGTH_DEFAULT {
    (m_num_dim == 2) -> soft m_outer_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 2) -> soft m_outer_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_2D_INNER_LENGTH_DEFAULT {
    (m_num_dim == 2) -> soft m_inner_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 2) -> soft m_inner_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_2D_OUTER_STRIDE_DEFAULT {
    (m_num_dim == 2) -> soft m_outer_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 2) -> soft m_outer_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_2D_INNER_STRIDE_DEFAULT {
    (m_num_dim == 2) -> soft m_inner_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 2) -> soft m_inner_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_2D_MEM_BSIZE_DEFAULT {
    (m_num_dim == 2) -> soft m_mem_bsize == m_dim_width_a * m_mem_stride_a; // width_b x stride_b x width_a = a x b x 64
  }

  // 3D constraint
  constraint C_3D_DIM_WIDTH_DEFAULT {
    (m_num_dim == 3) -> soft m_dim_width_a dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 3) -> soft m_dim_width_b dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 3) -> soft m_dim_width_c dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 3 && m_pad_mode==1) -> soft m_dim_width_a > 0;
    (m_num_dim == 3 && m_pad_mode==1) -> soft m_dim_width_b > 0;
    (m_num_dim == 3 && m_pad_mode==1) -> soft m_dim_width_c > 0;
  }

  constraint C_3D_DIM_OFFSET_DEFAULT {
    (m_num_dim == 3 && m_vtrsp_mode == 0) -> soft m_dim_offset_a dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 3 && m_vtrsp_mode != 0) -> soft m_dim_offset_a dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 3 && m_vtrsp_mode == 0) -> soft m_dim_offset_b dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 3 && m_vtrsp_mode != 0) -> soft m_dim_offset_b dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 3 && m_vtrsp_mode == 0) -> soft m_dim_offset_c dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 3 && m_vtrsp_mode != 0) -> soft m_dim_offset_c dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 3) -> m_dim_offset_d == 0;
  }

  constraint C_3D_MEM_STRIDE_DEFAULT {
    (m_num_dim == 3) -> soft m_mem_stride_c dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 3 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_b == m_dim_width_c * m_mem_stride_c;
    (m_num_dim == 3 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_a == m_dim_width_b * m_mem_stride_b; // a x b x c x 64
    (m_num_dim == 3 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_b dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 3 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_a dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
  }

  constraint C_3D_OUTER_LENGTH_DEFAULT {
    (m_num_dim == 3) -> soft m_outer_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 3) -> soft m_outer_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 3) -> soft m_outer_length_c dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_3D_INNER_LENGTH_DEFAULT {
    (m_num_dim == 3) -> soft m_inner_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 3) -> soft m_inner_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 3) -> soft m_inner_length_c dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_3D_OUTER_STRIDE_DEFAULT {
    (m_num_dim == 3) -> soft m_outer_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 3) -> soft m_outer_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 3) -> soft m_outer_stride_c dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_3D_INNER_STRIDE_DEFAULT {
    (m_num_dim == 3) -> soft m_inner_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 3) -> soft m_inner_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 3) -> soft m_inner_stride_c dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_3D_MEM_BSIZE_DEFAULT {
    (m_num_dim == 3) -> soft m_mem_bsize == m_dim_width_a * m_mem_stride_a; // width_b x stride_b x width_a = a x b c x 64
  }

  constraint C_MEM_STRIDE_WRT_DIM_WIDTH_DEFAULT {
    m_memstride_wrt_dim_width == 1;
  }

  // 4D constraint
  constraint C_4D_DIM_WIDTH_DEFAULT {
    (m_num_dim == 4) -> soft m_dim_width_a dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 4) -> soft m_dim_width_b dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 4) -> soft m_dim_width_c dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 4) -> soft m_dim_width_d dist { 0:=25, 1:=25, [2:5]:/ 25, [6:8]:/ 25};
    (m_num_dim == 4 && m_pad_mode==1) -> soft m_dim_width_a > 0;
    (m_num_dim == 4 && m_pad_mode==1) -> soft m_dim_width_b > 0;
    (m_num_dim == 4 && m_pad_mode==1) -> soft m_dim_width_c > 0;
    (m_num_dim == 4 && m_pad_mode==1) -> soft m_dim_width_d > 0;
  }

  constraint C_4D_DIM_OFFSET_DEFAULT {
    (m_num_dim == 4 && m_vtrsp_mode == 0) -> soft m_dim_offset_a dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 4 && m_vtrsp_mode != 0) -> soft m_dim_offset_a dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 4 && m_vtrsp_mode == 0) -> soft m_dim_offset_b dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 4 && m_vtrsp_mode != 0) -> soft m_dim_offset_b dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 4 && m_vtrsp_mode == 0) -> soft m_dim_offset_c dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 4 && m_vtrsp_mode != 0) -> soft m_dim_offset_c dist { 0:=90, [1:8]:/ 10};
    (m_num_dim == 4 && m_vtrsp_mode == 0) -> soft m_dim_offset_d dist { 0:=20, 1:=20, [2:5]:/ 40, [6:8]:/ 20};
    (m_num_dim == 4 && m_vtrsp_mode != 0) -> soft m_dim_offset_d dist { 0:=90, [1:8]:/ 10};
  }

  constraint C_4D_MEM_STRIDE_DEFAULT {
    (m_num_dim == 4) -> soft m_mem_stride_d dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 4 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_c == m_dim_width_d * m_mem_stride_d;
    (m_num_dim == 4 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_b == m_dim_width_c * m_mem_stride_c;
    (m_num_dim == 4 && m_memstride_wrt_dim_width)  -> soft m_mem_stride_a == m_dim_width_b * m_mem_stride_b; // a x b x c x 64
    (m_num_dim == 4 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_c dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 4 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_b dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
    (m_num_dim == 4 && !m_memstride_wrt_dim_width) -> soft m_mem_stride_a dist { 0:=16, 64:=17, 128:= 17, 192:= 17, 256:= 17, 320:=16};
  }

  constraint C_4D_OUTER_LENGTH_DEFAULT {
    (m_num_dim == 4) -> soft m_outer_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_outer_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_outer_length_c dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_outer_length_d dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_4D_INNER_LENGTH_DEFAULT {
    (m_num_dim == 4) -> soft m_inner_length_a dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_inner_length_b dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_inner_length_c dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
    (m_num_dim == 4) -> soft m_inner_length_d dist { 1:=50, 2:=20, [3:5]:/ 20, [6:8]:/ 10};
  }

  constraint C_4D_OUTER_STRIDE_DEFAULT {
    (m_num_dim == 4) -> soft m_outer_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_outer_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_outer_stride_c dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_outer_stride_d dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_4D_INNER_STRIDE_DEFAULT {
    (m_num_dim == 4) -> soft m_inner_stride_a dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_inner_stride_b dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_inner_stride_c dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
    (m_num_dim == 4) -> soft m_inner_stride_d dist { 0:=16, 1:=28, [2:3]:/ 28, [4:5]:/ 28};
  }

  constraint C_4D_MEM_BSIZE_DEFAULT {
    (m_num_dim == 4) -> soft m_mem_bsize == m_dim_width_a * m_mem_stride_a; // width_b x stride_b x width_a = a x b x c x d x 64
  }

  constraint C_SIM_CONTROL {
    (m_num_dim == 3) -> (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_outer_length_a * m_outer_length_b * m_outer_length_c) <= 50000;
    (m_num_dim == 4) -> (m_inner_length_a * m_inner_length_b * m_inner_length_c * m_inner_length_d * m_outer_length_a * m_outer_length_b * m_outer_length_c * m_outer_length_d) <= 50000;
  }

  constraint C_SOLVER {
    solve m_cmd_format before m_num_dim, m_lin_settings;
    solve m_vtrsp_mode before m_num_dim;
    solve m_num_dim before m_dim_def_ptr, m_vect_dim, m_pad_mode;
    solve m_dim_def_ptr before m_loop_def_ptr;
    solve m_pad_mode before m_dim_width_a, m_dim_width_b, m_dim_width_c, m_dim_width_d;
    solve header_vector_mode before m_format;
    solve m_num_dim before m_dim_offset_a, m_dim_offset_b, m_dim_offset_c, m_dim_offset_d;
    solve m_num_dim, m_memstride_wrt_dim_width before m_mem_stride_a, m_mem_stride_b, m_mem_stride_c, m_mem_stride_d;
    solve m_num_dim before m_outer_length_a, m_outer_length_b, m_outer_length_c, m_outer_length_d;
    solve m_num_dim before m_inner_length_a, m_inner_length_b, m_inner_length_c, m_inner_length_d;
    solve m_num_dim before m_outer_stride_a, m_outer_stride_b, m_outer_stride_c, m_outer_stride_d;
    solve m_num_dim before m_inner_stride_a, m_inner_stride_b, m_inner_stride_c, m_inner_stride_d;
    solve m_dim_width_a, m_mem_stride_a, m_num_dim before m_mem_bsize;
    solve m_dim_width_b, m_mem_stride_b before m_mem_stride_a;
    solve m_dim_width_c, m_mem_stride_c before m_mem_stride_b;
    solve m_dim_width_d, m_mem_stride_d before m_mem_stride_c;
    solve m_decomp_en before m_lin_settings;
  }

  function new (string name = "dmc_addr_gen_seq_item");
    super.new (name);
  endfunction

  virtual function dmc_addr_gen_seq_item do_clone();
    dmc_addr_gen_seq_item item;

    if(!$cast(item, this.clone()))
      `uvm_error(get_full_name(), "Clone failed")

    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    dmc_addr_gen_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.header_token_consumer = seq_rhs.header_token_consumer;
    this.header_token_producer = seq_rhs.header_token_producer;
    this.header_triggers      = seq_rhs.header_triggers;
    this.header_cmd_format    = seq_rhs.header_cmd_format;
    this.header_vector_mode   = seq_rhs.header_vector_mode;
    this.m_header             = seq_rhs.m_header;
    this.m_mem_stride_d       = seq_rhs.m_mem_stride_d;
    this.m_mem_stride_c       = seq_rhs.m_mem_stride_c;
    this.m_mem_stride_b       = seq_rhs.m_mem_stride_b;
    this.m_mem_stride_a       = seq_rhs.m_mem_stride_a;
    this.m_outer_stride_d     = seq_rhs.m_outer_stride_d;
    this.m_outer_stride_c     = seq_rhs.m_outer_stride_c;
    this.m_outer_stride_b     = seq_rhs.m_outer_stride_b;
    this.m_outer_stride_a     = seq_rhs.m_outer_stride_a;
    this.m_inner_stride_d     = seq_rhs.m_inner_stride_d;
    this.m_inner_stride_c     = seq_rhs.m_inner_stride_c;
    this.m_inner_stride_b     = seq_rhs.m_inner_stride_b;
    this.m_inner_stride_a     = seq_rhs.m_inner_stride_a;
    this.m_outer_length_d     = seq_rhs.m_outer_length_d;
    this.m_outer_length_c     = seq_rhs.m_outer_length_c;
    this.m_outer_length_b     = seq_rhs.m_outer_length_b;
    this.m_outer_length_a     = seq_rhs.m_outer_length_a;
    this.m_inner_length_d     = seq_rhs.m_inner_length_d;
    this.m_inner_length_c     = seq_rhs.m_inner_length_c;
    this.m_inner_length_b     = seq_rhs.m_inner_length_b;
    this.m_inner_length_a     = seq_rhs.m_inner_length_a;
    this.m_dim_width_d        = seq_rhs.m_dim_width_d;
    this.m_dim_width_c        = seq_rhs.m_dim_width_c;
    this.m_dim_width_b        = seq_rhs.m_dim_width_b;
    this.m_dim_width_a        = seq_rhs.m_dim_width_a;
    this.m_dim_offset_d       = seq_rhs.m_dim_offset_d;
    this.m_dim_offset_c       = seq_rhs.m_dim_offset_c;
    this.m_dim_offset_b       = seq_rhs.m_dim_offset_b;
    this.m_dim_offset_a       = seq_rhs.m_dim_offset_a;
    this.m_mem_bsize          = seq_rhs.m_mem_bsize;
    this.m_decomp_en          = seq_rhs.m_decomp_en;
    this.m_pad_mode           = seq_rhs.m_pad_mode;
    this.m_format             = seq_rhs.m_format;
    this.m_vtrsp_mode         = seq_rhs.m_vtrsp_mode;
    this.m_vect_dim           = seq_rhs.m_vect_dim;
    this.m_ring_buff_size     = seq_rhs.m_ring_buff_size;
    this.m_mem_offset         = seq_rhs.m_mem_offset;
    this.m_mask_end           = seq_rhs.m_mask_end;
    this.m_mask_start         = seq_rhs.m_mask_start;
    this.m_pad_val            = seq_rhs.m_pad_val;
    this.m_intra_pad_val      = seq_rhs.m_intra_pad_val;
    this.m_mem_baseaddr       = seq_rhs.m_mem_baseaddr;
    this.m_length             = seq_rhs.m_length;
    this.m_lin_settings       = seq_rhs.m_lin_settings;
    this.m_num_dim            = seq_rhs.m_num_dim;
    this.m_loop_def_ptr       = seq_rhs.m_loop_def_ptr;
    this.m_dim_def_ptr        = seq_rhs.m_dim_def_ptr;
    this.m_cmd_format         = seq_rhs.m_cmd_format;
    this.m_cmd                = seq_rhs.m_cmd;
    this.m_reset_an_i         = seq_rhs.m_reset_an_i;
    this.m_has_cmd            = seq_rhs.m_has_cmd;
    this.m_has_dpc_cmd        = seq_rhs.m_has_dpc_cmd;
    this.m_dpc_cmd            = seq_rhs.m_dpc_cmd;
    this.m_l1_base_addr       = seq_rhs.m_l1_base_addr;
    this.m_pword_len          = seq_rhs.m_pword_len;
    this.iteration            = seq_rhs.iteration;
    //delete garbage data if any before copying all queues
    this.m_cmd_q.delete();
    this.m_loop_def_q.delete();
    this.m_dim_def_q.delete();
    foreach (seq_rhs.m_cmd_q[i]) begin
      this.m_cmd_q.push_back(seq_rhs.m_cmd_q[i]);
    end
    foreach (seq_rhs.m_loop_def_q[i]) begin
      this.m_loop_def_q.push_back(seq_rhs.m_loop_def_q[i]);
    end
    foreach (seq_rhs.m_dim_def_q[i]) begin
      this.m_dim_def_q.push_back(seq_rhs.m_dim_def_q[i]);
    end
  endfunction

  virtual function void reset();
    m_reset_an_i    = 0;
    m_has_cmd       = 0;
    m_has_dpc_cmd   = 0;
    m_cmd           = 0;
    m_dpc_cmd       = 0;
    iteration       = 0;
  endfunction

  virtual function void copy_def_params(dmc_addr_gen_seq_item seq_rhs);
    if(seq_rhs == null) begin
      `uvm_fatal(get_full_name(), "do_copy from null ptr");
    end
    this.m_mem_stride_d       = seq_rhs.m_mem_stride_d;
    this.m_mem_stride_c       = seq_rhs.m_mem_stride_c;
    this.m_mem_stride_b       = seq_rhs.m_mem_stride_b;
    this.m_mem_stride_a       = seq_rhs.m_mem_stride_a;
    this.m_outer_stride_d     = seq_rhs.m_outer_stride_d;
    this.m_outer_stride_c     = seq_rhs.m_outer_stride_c;
    this.m_outer_stride_b     = seq_rhs.m_outer_stride_b;
    this.m_outer_stride_a     = seq_rhs.m_outer_stride_a;
    this.m_inner_stride_d     = seq_rhs.m_inner_stride_d;
    this.m_inner_stride_c     = seq_rhs.m_inner_stride_c;
    this.m_inner_stride_b     = seq_rhs.m_inner_stride_b;
    this.m_inner_stride_a     = seq_rhs.m_inner_stride_a;
    this.m_outer_length_d     = seq_rhs.m_outer_length_d;
    this.m_outer_length_c     = seq_rhs.m_outer_length_c;
    this.m_outer_length_b     = seq_rhs.m_outer_length_b;
    this.m_outer_length_a     = seq_rhs.m_outer_length_a;
    this.m_inner_length_d     = seq_rhs.m_inner_length_d;
    this.m_inner_length_c     = seq_rhs.m_inner_length_c;
    this.m_inner_length_b     = seq_rhs.m_inner_length_b;
    this.m_inner_length_a     = seq_rhs.m_inner_length_a;
    this.m_dim_width_d        = seq_rhs.m_dim_width_d;
    this.m_dim_width_c        = seq_rhs.m_dim_width_c;
    this.m_dim_width_b        = seq_rhs.m_dim_width_b;
    this.m_dim_width_a        = seq_rhs.m_dim_width_a;
    this.m_dim_offset_d       = seq_rhs.m_dim_offset_d;
    this.m_dim_offset_c       = seq_rhs.m_dim_offset_c;
    this.m_dim_offset_b       = seq_rhs.m_dim_offset_b;
    this.m_dim_offset_a       = seq_rhs.m_dim_offset_a;
    this.m_num_dim            = seq_rhs.m_num_dim;
    this.m_loop_def_ptr       = seq_rhs.m_loop_def_ptr;
    this.m_dim_def_ptr        = seq_rhs.m_dim_def_ptr;
    this.m_cmd_format         = seq_rhs.m_cmd_format;
    this.m_num_dim            = seq_rhs.m_num_dim;
    this.m_mem_bsize          = seq_rhs.m_mem_bsize;
    this.m_pad_mode           = seq_rhs.m_pad_mode; // for simplicity of reusing dim_width parameters
    this.m_format             = seq_rhs.m_format;
    this.header_token_consumer = seq_rhs.header_token_consumer;
    this.header_token_producer = seq_rhs.header_token_producer;
    this.header_triggers      = seq_rhs.header_triggers;
    this.header_cmd_format    = seq_rhs.header_cmd_format;
    this.header_vector_mode   = seq_rhs.header_vector_mode;
    this.m_header             = seq_rhs.m_header;
    this.m_high_mbsize        = 1;
    set_high_mbsize();
    set_fields_to_cmd();
    cmd_struct_to_array();
    m_cmd_q[0][55:48] = this.m_cmd_format;
    `uvm_info(get_name(), $sformatf("Copied item: m_cmd_q[0] 0x%0x cmd_format: %s", m_cmd_q[0], this.m_cmd_format.name()), UVM_LOW)
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- ADDR_GEN COMMAND ITEM ----------------") };
    s = {s, $sformatf("\n iteration             : %0d",    iteration)};
    s = {s, $sformatf("\n Command Format        : %s",    m_cmd_format.name())};
    s = {s, $sformatf("\n header_token_producer : 0x%0x", header_token_producer)};
    s = {s, $sformatf("\n header_token_consumer : 0x%0x", header_token_consumer)};
    s = {s, $sformatf("\n mem_baseaddr          : 0x%0x", m_mem_baseaddr)};
    s = {s, $sformatf("\n l1_base_addr          : 0x%0x", m_l1_base_addr)};
    s = {s, $sformatf("\n mem_baseaddr (eff)    : 0x%0x", get_mem_base_addr())};
    s = {s, $sformatf("\n vector_mode           : %0d",   header_vector_mode)};
    s = {s, $sformatf("\n format                : 0x%0x", m_format)};
    s = {s, $sformatf("\n pad_val               : %0d (0x%4x)",   m_pad_val, m_pad_val)};
    s = {s, $sformatf("\n intra_pad_val         : %0d (0x%4x)",   m_intra_pad_val, m_intra_pad_val)};
    s = {s, $sformatf("\n mask_start            : 0x%0x", m_mask_start)};
    s = {s, $sformatf("\n mask_end              : 0x%0x", m_mask_end)};
    s = {s, $sformatf("\n mem_offset            : 0x%0x", m_mem_offset)};
    s = {s, $sformatf("\n ring_buff_size        : 0x%0x", m_ring_buff_size)};
    s = {s, $sformatf("\n vect_dim              : 0x%0x", m_vect_dim)};
    s = {s, $sformatf("\n vtrsp_mode            : 0x%0x", m_vtrsp_mode)};
    s = {s, $sformatf("\n pad_mode              : 0x%0x", m_pad_mode)};
    s = {s, $sformatf("\n mem_bsize             : 0x%0x", m_mem_bsize)};
    s = {s, $sformatf("\n m_num_dim             : 0x%0x", m_num_dim)};
    if (m_cmd_format == CMDFORMAT_LINEAR) begin
      s = {s, $sformatf("\n m_length            : 0x%0x", m_length)};
      s = {s, $sformatf("\n m_lin_settings      : 0x%0x", m_lin_settings)};
    end
    if (m_cmd_format inside {CMDFORMAT_DEF_BASED, CMDFORMAT_OFFSET_BASED}) begin
      s = {s, $sformatf("\n m_loop_def_ptr    : 0x%0x", m_loop_def_ptr)};
      s = {s, $sformatf("\n m_dim_def_ptr     : 0x%0x", m_dim_def_ptr)};
    end
    s = {s, $sformatf("\n dim_width_a       : 0x%0x", m_dim_width_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n dim_width_b       : 0x%0x", m_dim_width_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n dim_width_c       : 0x%0x", m_dim_width_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n dim_width_d       : 0x%0x", m_dim_width_d)};
    s = {s, $sformatf("\n dim_offset_a      : %0d (0x%4x)", m_dim_offset_a, m_dim_offset_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n dim_offset_b      : %0d (0x%4x)", m_dim_offset_b, m_dim_offset_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n dim_offset_c      : %0d (0x%4x)", m_dim_offset_c, m_dim_offset_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n dim_offset_d      : %0d (0x%4x)", m_dim_offset_d, m_dim_offset_d)};
    s = {s, $sformatf("\n inner_length_a    : 0x%0x", m_inner_length_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n inner_length_b    : 0x%0x", m_inner_length_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n inner_length_c    : 0x%0x", m_inner_length_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n inner_length_d    : 0x%0x", m_inner_length_d)};
    s = {s, $sformatf("\n outer_length_a    : 0x%0x", m_outer_length_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n outer_length_b    : 0x%0x", m_outer_length_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n outer_length_c    : 0x%0x", m_outer_length_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n outer_length_d    : 0x%0x", m_outer_length_d)};
    s = {s, $sformatf("\n mem_stride_a      : 0x%0x", m_mem_stride_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n mem_stride_b      : 0x%0x", m_mem_stride_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n mem_stride_c      : 0x%0x", m_mem_stride_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n mem_stride_d      : 0x%0x", m_mem_stride_d)};
    s = {s, $sformatf("\n inner_stride_a    : %0d (0x%2x)", m_inner_stride_a, m_inner_stride_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n inner_stride_b    : %0d (0x%2x)", m_inner_stride_b, m_inner_stride_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n inner_stride_c    : %0d (0x%2x)", m_inner_stride_c, m_inner_stride_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n inner_stride_d    : %0d (0x%2x)", m_inner_stride_d, m_inner_stride_d)};
    s = {s, $sformatf("\n outer_stride_a    : %0d (0x%2x)", m_outer_stride_a, m_outer_stride_a)};
    if (m_num_dim > 1) s = {s, $sformatf("\n outer_stride_b    : %0d (0x%2x)", m_outer_stride_b, m_outer_stride_b)};
    if (m_num_dim > 2) s = {s, $sformatf("\n outer_stride_c    : %0d (0x%2x)", m_outer_stride_c, m_outer_stride_c)};
    if (m_num_dim > 3) s = {s, $sformatf("\n outer_stride_d    : %0d (0x%2x)", m_outer_stride_d, m_outer_stride_d)};
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction
  
  virtual function string dpc_cmd_2string();
    string mask;
    string padding;
    string last;
    string out_of_range;
    string s;
    mask = ( m_dpc_cmd.dpc_msk == '1) ? $sformatf(", mask: 0x%0x", m_dpc_cmd.dpc_msk) : $sformatf(", mask: 0x%0x, intra_pad_value: 0x%0x", m_dpc_cmd.dpc_msk, m_dpc_cmd.dpc_intra_pad_val);
    padding = (m_dpc_cmd.dpc_pad) ? $sformatf(", pad: 0x%0x", m_dpc_cmd.dpc_pad_val) : ", pad: 0";
    out_of_range = (m_dpc_cmd.err_addr_out_of_range) ? $sformatf(", err_addr_out_of_range: 1") : "";
    last = (m_dpc_cmd.dpc_last) ? $sformatf(", last: 1") : "";
    s = $sformatf("DPC_CMD | address: 0x%0x, format: %0d, config: %0d%s%s%s%s", m_dpc_cmd.dpc_addr, m_dpc_cmd.dpc_format, m_dpc_cmd.dpc_config, mask, padding, last, out_of_range);
    // s = $sformatf("DPC CMD | dpc_addr: 0x%0x, dpc_msk: 0x%0x, dpc_pad: %0d,  dpc_last: %0d, dpc_pad_val: 0x%0x, dpc_intra_pad_val: 0x%0x, err_addr_out_of_range: %0d", m_dpc_cmd.dpc_addr, m_dpc_cmd.dpc_msk, m_dpc_cmd.dpc_pad, m_dpc_cmd.dpc_last, m_dpc_cmd.dpc_pad_val, m_dpc_cmd.dpc_intra_pad_val, m_dpc_cmd.err_addr_out_of_range);
    return s;
  endfunction

  function void fill_linear_cmd();
    m_cmd_q.push_back({m_length, m_lin_settings, m_rsrv_linear, m_cmd.mem_baseaddr}); // WORD1 CMDFORMAT_LINEAR DONE
  endfunction

  function void fill_def_based_cmd();
    m_cmd_q.push_back({m_cmd.intra_pad_val, m_cmd.pad_val, m_cmd.mem_baseaddr}); // WORD1
    m_cmd_q.push_back({m_settings, m_cmd.ring_buff_size, m_cmd.mem_offset}); // WORD2
    m_cmd_q.push_back({m_cmd.mem_bsize, m_cmd.mask_end, m_cmd.mask_start, m_loop_def_ptr, m_dim_def_ptr}); //WORD3 CMDFORMAT_DEF_BASED DONE
  endfunction

  function void fill_offset_based_cmd();
    m_cmd_q.push_back({m_cmd.intra_pad_val, m_cmd.pad_val, m_cmd.mem_baseaddr}); // WORD1
    m_cmd_q.push_back({m_settings, m_cmd.ring_buff_size, m_cmd.mem_offset}); // WORD2
    m_cmd_q.push_back({m_cmd.mem_bsize, m_cmd.mask_end, m_cmd.mask_start, m_loop_def_ptr, m_dim_def_ptr}); //WORD3 CMDFORMAT_DEF_BASED DONE
    m_cmd_q.push_back({m_cmd.dim_offset_d, m_cmd.dim_offset_c, m_cmd.dim_offset_b, m_cmd.dim_offset_a}); // WORD4 CMDFORMAT_OFFSET_BASED DONE
  endfunction

  function void fill_3dim_fallback_cmd();
    m_cmd_q.push_back({m_cmd.intra_pad_val, m_cmd.pad_val, m_cmd.mem_baseaddr}); // WORD1
    m_cmd_q.push_back({m_settings, m_cmd.ring_buff_size, m_cmd.mem_offset}); // WORD2
    m_cmd_q.push_back({m_cmd.mem_bsize, m_cmd.mask_end, m_cmd.mask_start, m_cmd.inner_length_c}); // WORD3
    m_cmd_q.push_back({m_cmd.mem_stride_a, m_cmd.dim_width_a, m_cmd.dim_offset_a}); // WORD4
    m_cmd_q.push_back({m_cmd.mem_stride_b, m_cmd.dim_width_b, m_cmd.dim_offset_b}); // WORD5
    m_cmd_q.push_back({m_cmd.mem_stride_c, m_cmd.dim_width_c, m_cmd.dim_offset_c}); // WORD6
    m_cmd_q.push_back({m_cmd.outer_length_c, m_cmd.outer_stride_a, m_cmd.inner_stride_a, m_cmd.outer_length_a, m_cmd.inner_length_a}); // WORD7
    m_cmd_q.push_back({m_cmd.outer_stride_c, m_cmd.inner_stride_c, m_cmd.outer_stride_b, m_cmd.inner_stride_b, m_cmd.outer_length_b, m_cmd.inner_length_b});  // WORD8 CMDFORMAT_3DIM_FALLBACK DONE
  endfunction

  function void fill_4dim_fallback_cmd();
    m_cmd_q.push_back({m_cmd.intra_pad_val, m_cmd.pad_val, m_cmd.mem_baseaddr}); // WORD1
    m_cmd_q.push_back({m_settings, m_cmd.ring_buff_size, m_cmd.mem_offset}); // WORD2
    m_cmd_q.push_back({m_cmd.mem_bsize, m_cmd.mask_end, m_cmd.mask_start, m_rsrv_4dimfallback_word_3}); // WORD3
    m_cmd_q.push_back({m_cmd.mem_stride_a, m_cmd.dim_width_a, m_cmd.dim_offset_a}); // WORD4
    m_cmd_q.push_back({m_cmd.mem_stride_b, m_cmd.dim_width_b, m_cmd.dim_offset_b}); // WORD5
    m_cmd_q.push_back({m_cmd.mem_stride_c, m_cmd.dim_width_c, m_cmd.dim_offset_c}); // WORD6
    m_cmd_q.push_back({m_cmd.mem_stride_d, m_cmd.dim_width_d, m_cmd.dim_offset_d}); // WORD7
    m_cmd_q.push_back({m_cmd.inner_length_d, m_cmd.inner_length_c, m_cmd.inner_length_b, m_cmd.inner_length_a}); // WORD8
    m_cmd_q.push_back({m_cmd.outer_length_d, m_cmd.outer_length_c, m_cmd.outer_length_b, m_cmd.outer_length_a}); // WORD9
    m_cmd_q.push_back({m_cmd.outer_stride_d, m_cmd.inner_stride_d, m_cmd.outer_stride_c, m_cmd.inner_stride_c, m_cmd.outer_stride_b, m_cmd.inner_stride_b, m_cmd.outer_stride_a, m_cmd.inner_stride_a});  // WORD10
  endfunction

  function void fill_defbased_memory();
    m_dim_def_q.push_back({m_cmd.mem_stride_a, m_cmd.dim_width_a, m_cmd.dim_offset_a}); // WORD0
    if (m_num_dim > 1) m_dim_def_q.push_back({m_cmd.mem_stride_b, m_cmd.dim_width_b, m_cmd.dim_offset_b}); // WORD1
    if (m_num_dim > 2) m_dim_def_q.push_back({m_cmd.mem_stride_c, m_cmd.dim_width_c, m_cmd.dim_offset_c}); // WORD2
    if (m_num_dim > 3) m_dim_def_q.push_back({m_cmd.mem_stride_d, m_cmd.dim_width_d, m_cmd.dim_offset_d}); // WORD3
    m_loop_def_q.push_back({m_rsrv_def_based_outer_a, m_cmd.outer_stride_a, m_cmd.outer_length_a, m_rsrv_def_based_inner_a, m_cmd.inner_stride_a, m_cmd.inner_length_a}); // WORD4
    if (m_num_dim > 1) m_loop_def_q.push_back({m_rsrv_def_based_outer_b, m_cmd.outer_stride_b, m_cmd.outer_length_b, m_rsrv_def_based_inner_b, m_cmd.inner_stride_b, m_cmd.inner_length_b}); // WORD5
    if (m_num_dim > 2) m_loop_def_q.push_back({m_rsrv_def_based_outer_c, m_cmd.outer_stride_c, m_cmd.outer_length_c, m_rsrv_def_based_inner_c, m_cmd.inner_stride_c, m_cmd.inner_length_c}); // WORD6
    if (m_num_dim > 3) m_loop_def_q.push_back({m_rsrv_def_based_outer_d, m_cmd.outer_stride_d, m_cmd.outer_length_d, m_rsrv_def_based_inner_d, m_cmd.inner_stride_d, m_cmd.inner_length_d}); // WORD7
  endfunction

  function void fill_offsetbased_memory();
    m_dim_def_q.push_back({m_mem_stride_a, m_dim_width_a, m_rsrv_dim_offset_a}); // WORD0
    if (m_num_dim > 1) m_dim_def_q.push_back({m_cmd.mem_stride_b, m_cmd.dim_width_b, m_rsrv_dim_offset_b}); // WORD1
    if (m_num_dim > 2) m_dim_def_q.push_back({m_cmd.mem_stride_c, m_cmd.dim_width_c, m_rsrv_dim_offset_c}); // WORD2
    if (m_num_dim > 3) m_dim_def_q.push_back({m_cmd.mem_stride_d, m_cmd.dim_width_d, m_rsrv_dim_offset_d}); // WORD3
    m_loop_def_q.push_back({m_rsrv_def_based_outer_a, m_cmd.outer_stride_a, m_cmd.outer_length_a, m_rsrv_def_based_inner_a, m_cmd.inner_stride_a, m_cmd.inner_length_a}); // WORD4
    if (m_num_dim > 1) m_loop_def_q.push_back({m_rsrv_def_based_outer_b, m_cmd.outer_stride_b, m_cmd.outer_length_b, m_rsrv_def_based_inner_b, m_cmd.inner_stride_b, m_cmd.inner_length_b}); // WORD5
    if (m_num_dim > 2) m_loop_def_q.push_back({m_rsrv_def_based_outer_c, m_cmd.outer_stride_c, m_cmd.outer_length_c, m_rsrv_def_based_inner_c, m_cmd.inner_stride_c, m_cmd.inner_length_c}); // WORD6
    if (m_num_dim > 3) m_loop_def_q.push_back({m_rsrv_def_based_outer_d, m_cmd.outer_stride_d, m_cmd.outer_length_d, m_rsrv_def_based_inner_d, m_cmd.inner_stride_d, m_cmd.inner_length_d}); // WORD7
  endfunction

  function void cmd_struct_to_array();
    // Definitiions
    m_cmd_q.delete();
    m_dim_def_q.delete();
    m_loop_def_q.delete();
    // prepare settings line to insert into the relevant commands.
    m_settings = {m_cmd.format, m_cmd.pad_mode, m_cmd.vtrsp_mode, m_cmd.vect_dim, m_num_dim_in_cmd};
    // CMD
    m_header = {header_reserved_b, header_vector_mode, header_cmd_format, header_token_consumer, header_token_producer, header_reserved_a, header_triggers};
    m_cmd_q.push_back(m_header); // WORD0

    case (m_cmd_format)
      CMDFORMAT_LINEAR: fill_linear_cmd();
      CMDFORMAT_3DIM_FALLBACK: fill_3dim_fallback_cmd();
      CMDFORMAT_4DIM_FALLBACK: fill_4dim_fallback_cmd();
      CMDFORMAT_DEF_BASED: begin
        fill_def_based_cmd();
        fill_defbased_memory();
      end
      CMDFORMAT_OFFSET_BASED: begin
        fill_offset_based_cmd();
        fill_offsetbased_memory();
      end
    endcase
  endfunction

  function int get_valid_dims();
    case (m_cmd_format)
      CMDFORMAT_LINEAR: return 1;
      CMDFORMAT_3DIM_FALLBACK: return 3;
      CMDFORMAT_3DIM_FALLBACK: return 4;
      default: return m_num_dim;
    endcase
  endfunction

  function mem_baseaddr_t get_mem_base_addr();
    mem_baseaddr_t effective_addr;
    effective_addr = m_cmd.mem_baseaddr;
    return effective_addr;
  endfunction

  function void set_fields_to_cmd();
     m_cmd.outer_stride_d =  m_outer_stride_d;
     m_cmd.outer_length_d =  m_outer_length_d;
     m_cmd.inner_stride_d =  m_inner_stride_d;
     m_cmd.inner_length_d =  m_inner_length_d;
     m_cmd.mem_stride_d   =  m_mem_stride_d;
     m_cmd.dim_width_d    =  m_dim_width_d;
     m_cmd.dim_offset_d   =  m_dim_offset_d;
     m_cmd.outer_stride_c =  m_outer_stride_c;
     m_cmd.inner_stride_c =  m_inner_stride_c;
     m_cmd.outer_stride_b =  m_outer_stride_b;
     m_cmd.inner_stride_b =  m_inner_stride_b;
     m_cmd.outer_length_b =  m_outer_length_b;
     m_cmd.inner_length_b =  m_inner_length_b;
     m_cmd.outer_length_c =  m_outer_length_c;
     m_cmd.outer_stride_a =  m_outer_stride_a;
     m_cmd.inner_stride_a =  m_inner_stride_a;
     m_cmd.outer_length_a =  m_outer_length_a;
     m_cmd.inner_length_a =  m_inner_length_a;
     m_cmd.mem_stride_c   =  m_mem_stride_c;
     m_cmd.dim_width_c    =  m_dim_width_c;
     m_cmd.dim_offset_c   =  m_dim_offset_c;
     m_cmd.mem_stride_b   =  m_mem_stride_b;
     m_cmd.dim_width_b    =  m_dim_width_b;
     m_cmd.dim_offset_b   =  m_dim_offset_b;
     m_cmd.mem_stride_a   =  m_mem_stride_a;
     m_cmd.dim_width_a    =  m_dim_width_a;
     m_cmd.dim_offset_a   =  m_dim_offset_a;
     m_cmd.mem_bsize      =  m_mem_bsize;
     m_cmd.decomp_en      =  m_decomp_en;
     m_cmd.pad_mode       =  m_pad_mode;
     m_cmd.format         =  m_format;
     m_cmd.vtrsp_mode     =  m_vtrsp_mode;
     m_cmd.vect_dim       =  m_vect_dim;
     m_cmd.inner_length_c =  m_inner_length_c;
     m_cmd.ring_buff_size =  m_ring_buff_size;
     m_cmd.mem_offset     =  m_mem_offset;
     m_cmd.mask_end       =  m_mask_end;
     m_cmd.mask_start     =  m_mask_start;
     m_cmd.pad_val        =  m_pad_val;
     m_cmd.intra_pad_val  =  m_intra_pad_val;
     m_cmd.mem_baseaddr   =  m_mem_baseaddr;
  endfunction

  function void set_cmd_to_fields();
    m_outer_stride_d  = m_cmd.outer_stride_d;
    m_outer_length_d  = m_cmd.outer_length_d;
    m_inner_stride_d  = m_cmd.inner_stride_d;
    m_inner_length_d  = m_cmd.inner_length_d;
    m_mem_stride_d    = m_cmd.mem_stride_d;
    m_dim_width_d     = m_cmd.dim_width_d;
    m_dim_offset_d    = m_cmd.dim_offset_d;
    m_outer_stride_c  = m_cmd.outer_stride_c;
    m_inner_stride_c  = m_cmd.inner_stride_c;
    m_outer_stride_b  = m_cmd.outer_stride_b;
    m_inner_stride_b  = m_cmd.inner_stride_b;
    m_outer_length_b  = m_cmd.outer_length_b;
    m_inner_length_b  = m_cmd.inner_length_b;
    m_outer_length_c  = m_cmd.outer_length_c;
    m_outer_stride_a  = m_cmd.outer_stride_a;
    m_inner_stride_a  = m_cmd.inner_stride_a;
    m_outer_length_a  = m_cmd.outer_length_a;
    m_inner_length_a  = m_cmd.inner_length_a;
    m_mem_stride_c    = m_cmd.mem_stride_c;
    m_dim_width_c     = m_cmd.dim_width_c;
    m_dim_offset_c    = m_cmd.dim_offset_c;
    m_mem_stride_b    = m_cmd.mem_stride_b;
    m_dim_width_b     = m_cmd.dim_width_b;
    m_dim_offset_b    = m_cmd.dim_offset_b;
    m_mem_stride_a    = m_cmd.mem_stride_a;
    m_dim_width_a     = m_cmd.dim_width_a;
    m_dim_offset_a    = m_cmd.dim_offset_a;
    m_mem_bsize       = m_cmd.mem_bsize;
    m_decomp_en       = m_cmd.decomp_en;
    m_pad_mode        = m_cmd.pad_mode;
    m_format          = m_cmd.format;
    m_vtrsp_mode      = m_cmd.vtrsp_mode;
    m_vect_dim        = m_cmd.vect_dim;
    m_inner_length_c  = m_cmd.inner_length_c;
    m_ring_buff_size  = m_cmd.ring_buff_size;
    m_mem_offset      = m_cmd.mem_offset;
    m_mask_end        = m_cmd.mask_end;
    m_mask_start      = m_cmd.mask_start;
    m_pad_val         = m_cmd.pad_val;
    m_intra_pad_val   = m_cmd.intra_pad_val;
    m_mem_baseaddr    = m_cmd.mem_baseaddr;
  endfunction

  // the comparing class should be the command, not the addr gen output
  function compare_cmd(dmc_addr_gen_seq_item itm, string src);
    bit success = 1;
    int valid_dims = get_valid_dims();
    string compare_msg = "";

    if (itm.m_cmd.mem_baseaddr != get_mem_base_addr()) begin
      success = 0;
      compare_msg = {compare_msg, $sformatf("\n mem_baseaddr: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_baseaddr, get_mem_base_addr)};
    end
    if (m_cmd_format != CMDFORMAT_LINEAR) begin
      if (itm.m_cmd.format != m_cmd.format) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n format: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.format, m_cmd.format)};
      end
      if (itm.m_cmd.pad_val != m_cmd.pad_val) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n pad_val: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.pad_val, m_cmd.pad_val)};
      end
      if (itm.m_cmd.intra_pad_val != m_cmd.intra_pad_val) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n intra_pad_val: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.intra_pad_val, m_cmd.intra_pad_val)};
      end
      if (itm.m_cmd.mem_bsize != m_cmd.mem_bsize) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_bsize: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_bsize, m_cmd.mem_bsize)};
      end
      if (itm.m_cmd.outer_length_a != m_cmd.outer_length_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_length_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_length_a, m_cmd.outer_length_a)};
      end
      if (itm.m_cmd.inner_length_a != m_cmd.inner_length_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_length_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_length_a, m_cmd.inner_length_a)};
      end
      if (itm.m_cmd.dim_width_a != m_cmd.dim_width_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_width_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_width_a, m_cmd.dim_width_a)};
      end
      if (itm.m_cmd.dim_offset_a != m_cmd.dim_offset_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_offset_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_offset_a, m_cmd.dim_offset_a)};
      end
      if (itm.m_cmd.mem_stride_a != m_cmd.mem_stride_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_stride_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_stride_a, m_cmd.mem_stride_a)};
      end
      if (itm.m_cmd.inner_stride_a != m_cmd.inner_stride_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_stride_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_stride_a, m_cmd.inner_stride_a)};
      end
      if (itm.m_cmd.outer_stride_a != m_cmd.outer_stride_a) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_stride_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_stride_a, m_cmd.outer_stride_a)};
      end
      if (itm.m_cmd.mask_start != m_cmd.mask_start) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mask_start: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mask_start, m_cmd.mask_start)};
      end
      if (itm.m_cmd.mask_end != m_cmd.mask_end) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mask_end: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mask_end, m_cmd.mask_end)};
      end
      if (itm.m_cmd.vect_dim != m_cmd.vect_dim) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n vect_dim: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.vect_dim, m_cmd.vect_dim)};
      end
      if (itm.m_cmd.pad_mode != m_cmd.pad_mode) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n pad_mode: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.pad_mode, m_cmd.pad_mode)};
      end
      if (itm.m_cmd.mem_offset != m_cmd.mem_offset) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_offset: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_offset, m_cmd.mem_offset)};
      end
      if (itm.m_cmd.ring_buff_size != m_cmd.ring_buff_size) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n ring_buff_size: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.ring_buff_size, m_cmd.ring_buff_size)};
      end
      if (itm.m_cmd.vtrsp_mode != m_cmd.vtrsp_mode) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n vtrsp_mode: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.vtrsp_mode, m_cmd.vtrsp_mode)};
      end
    end else begin
      if (itm.m_cmd.format != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n format: Act: 0x%0x Exp: 0x0", itm.m_cmd.format)};
      end
      if (itm.m_cmd.pad_val != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n pad_val: Act: 0x%0x Exp: 0x0", itm.m_cmd.pad_val)};
      end
      if (itm.m_cmd.intra_pad_val != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n intra_pad_val: Act: 0x%0x Exp: 0x0", itm.m_cmd.intra_pad_val)};
      end
      if (itm.m_cmd.mem_bsize != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_bsize: Act: 0x%0x Exp: 0x0", itm.m_cmd.mem_bsize)};
      end
      if (itm.m_cmd.outer_length_a != m_length) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_length_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_length_a, m_length)};
      end
      if (itm.m_cmd.inner_length_a != 1) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_length_a: Act: 0x%0x Exp: 0x1", itm.m_cmd.inner_length_a)};
      end
      if (itm.m_cmd.dim_width_a != m_length) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_width_a: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_width_a, m_length)};
      end
      if (itm.m_cmd.dim_offset_a != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_offset_a: Act: 0x%0x Exp: 0x0", itm.m_cmd.dim_offset_a)};
      end
      if (itm.m_cmd.mem_stride_a != 64) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_stride_a: Act: 0x%0x Exp: 0x40", itm.m_cmd.mem_stride_a)};
      end
      if (itm.m_cmd.inner_stride_a != 1) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_stride_a: Act: 0x%0x Exp: 0x1", itm.m_cmd.inner_stride_a)};
      end
      if (itm.m_cmd.outer_stride_a != 1) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_stride_a: Act: 0x%0x Exp: 0x1", itm.m_cmd.outer_stride_a)};
      end
      if (itm.m_cmd.mask_start != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mask_start: Act: 0x%0x Exp: 0x0", itm.m_cmd.mask_start)};
      end
      if (itm.m_cmd.mask_end != 64) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mask_end: Act: 0x%0x Exp: 0x64", itm.m_cmd.mask_end)};
      end
      if (itm.m_cmd.vect_dim != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n vect_dim: Act: 0x%0x Exp: 0x0", itm.m_cmd.vect_dim)};
      end
      if (itm.m_cmd.pad_mode != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n pad_mode: Act: 0x%0x Exp: 0x0", itm.m_cmd.pad_mode)};
      end
      if (itm.m_cmd.mem_offset != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_offset: Act: 0x%0x Exp: 0x0", itm.m_cmd.mem_offset)};
      end
      if (itm.m_cmd.ring_buff_size != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n ring_buff_size: Act: 0x%0x Exp: 0x0", itm.m_cmd.ring_buff_size)};
      end
      if (itm.m_cmd.vtrsp_mode != 0) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n vtrsp_mode: Act: 0x%0x Exp: 0x0", itm.m_cmd.vtrsp_mode)};
      end
      if (itm.m_cmd.decomp_en != m_cmd.decomp_en) begin // decompression is only for linear command
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n decomp_en: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.decomp_en, m_cmd.decomp_en)};
      end
      // Correct the fields for linear before sending to analysis ports
      m_cmd.pad_val = 0;
      m_cmd.mem_bsize = 0;
      m_cmd.outer_length_a = m_length;
      m_cmd.inner_length_a = 1;
      m_cmd.dim_width_a = m_length;
      m_cmd.dim_offset_a = 0;
      m_cmd.mem_stride_a = 64;
      m_cmd.inner_stride_a = 1;
      m_cmd.outer_stride_a = 1;
      m_cmd.mask_start = 0;
      m_cmd.mask_end = 64;
      m_cmd.vect_dim = 0;
      m_cmd.pad_mode = 0;
      m_cmd.mem_offset = 0;
      m_cmd.ring_buff_size = 0;
      m_cmd.vtrsp_mode = 0;
    end
    if (valid_dims > 1) begin
      if (itm.m_cmd.dim_offset_b != m_cmd.dim_offset_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_offset_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_offset_b, m_cmd.dim_offset_b)};
      end
      if (itm.m_cmd.dim_width_b != m_cmd.dim_width_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_width_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_width_b, m_cmd.dim_width_b)};
      end
      if (itm.m_cmd.mem_stride_b != m_cmd.mem_stride_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_stride_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_stride_b, m_cmd.mem_stride_b)};
      end
      if (itm.m_cmd.inner_length_b != m_cmd.inner_length_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_length_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_length_b, m_cmd.inner_length_b)};
      end
      if (itm.m_cmd.outer_length_b != m_cmd.outer_length_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_length_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_length_b, m_cmd.outer_length_b)};
      end
      if (itm.m_cmd.inner_stride_b != m_cmd.inner_stride_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_stride_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_stride_b, m_cmd.inner_stride_b)};
      end
      if (itm.m_cmd.outer_stride_b != m_cmd.outer_stride_b) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_stride_b: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_stride_b, m_cmd.outer_stride_b)};
      end
    end
    if (valid_dims > 2) begin
      if (itm.m_cmd.dim_offset_c != m_cmd.dim_offset_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_offset_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_offset_c, m_cmd.dim_offset_c)};
      end
      if (itm.m_cmd.dim_width_c != m_cmd.dim_width_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_width_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_width_c, m_cmd.dim_width_c)};
      end
      if (itm.m_cmd.mem_stride_c != m_cmd.mem_stride_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_stride_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_stride_c, m_cmd.mem_stride_c)};
      end
      if (itm.m_cmd.inner_length_c != m_cmd.inner_length_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_length_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_length_c, m_cmd.inner_length_c)};
      end
      if (itm.m_cmd.outer_length_c != m_cmd.outer_length_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_length_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_length_c, m_cmd.outer_length_c)};
      end
      if (itm.m_cmd.inner_stride_c != m_cmd.inner_stride_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_stride_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_stride_c, m_cmd.inner_stride_c)};
      end
      if (itm.m_cmd.outer_stride_c != m_cmd.outer_stride_c) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_stride_c: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_stride_c, m_cmd.outer_stride_c)};
      end
    end
    if (valid_dims > 3) begin
      if (itm.m_cmd.dim_offset_d != m_cmd.dim_offset_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_offset_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_offset_d, m_cmd.dim_offset_d)};
      end
      if (itm.m_cmd.dim_width_d != m_cmd.dim_width_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n dim_width_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.dim_width_d, m_cmd.dim_width_d)};
      end
      if (itm.m_cmd.mem_stride_d != m_cmd.mem_stride_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n mem_stride_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.mem_stride_d, m_cmd.mem_stride_d)};
      end
      if (itm.m_cmd.inner_length_d != m_cmd.inner_length_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_length_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_length_d, m_cmd.inner_length_d)};
      end
      if (itm.m_cmd.outer_length_d != m_cmd.outer_length_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_length_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_length_d, m_cmd.outer_length_d)};
      end
      if (itm.m_cmd.inner_stride_d != m_cmd.inner_stride_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n inner_stride_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.inner_stride_d, m_cmd.inner_stride_d)};
      end
      if (itm.m_cmd.outer_stride_d != m_cmd.outer_stride_d) begin
        success = 0;
        compare_msg = {compare_msg, $sformatf("\n outer_stride_d: Act: 0x%0x Exp: 0x%0x", itm.m_cmd.outer_stride_d, m_cmd.outer_stride_d)};
      end
    end

    if (success == 0) begin
      `uvm_error(get_name(), $sformatf("[%s] CMD mismatch! %s", src, compare_msg))
    end else begin
      `uvm_info(get_name(), $sformatf("[%s] CMD match! %s", src, convert2string()), UVM_FULL)
    end
  endfunction

  virtual function void set_high_mbsize();
    if (m_high_mbsize) begin
      for (int i=30; i >= 20; i--) begin // ICDF considers bit 31 to be the negative (i.e. the sign)
        m_mem_bsize[i] = bit'($urandom_range(0,1));
      end
    end
  endfunction

  function void post_randomize();
    if ($urandom_range(0,1)) m_dim_offset_a = m_dim_offset_a * (-1);
    if ($urandom_range(0,1)) m_dim_offset_b = m_dim_offset_b * (-1);
    if ($urandom_range(0,1)) m_dim_offset_c = m_dim_offset_c * (-1);
    if ($urandom_range(0,1)) m_dim_offset_d = m_dim_offset_d * (-1);
    if ($urandom_range(0,1)) m_outer_stride_a = m_outer_stride_a * (-1);
    if ($urandom_range(0,1)) m_outer_stride_b = m_outer_stride_b * (-1);
    if ($urandom_range(0,1)) m_outer_stride_c = m_outer_stride_c * (-1);
    if ($urandom_range(0,1)) m_outer_stride_d = m_outer_stride_d * (-1);
    if ($urandom_range(0,1)) m_inner_stride_a = m_inner_stride_a * (-1);
    if ($urandom_range(0,1)) m_inner_stride_b = m_inner_stride_b * (-1);
    if ($urandom_range(0,1)) m_inner_stride_c = m_inner_stride_c * (-1);
    if ($urandom_range(0,1)) m_inner_stride_d = m_inner_stride_d * (-1);
    set_high_mbsize();
    set_fields_to_cmd();
    cmd_struct_to_array();
    m_cmd_q[0][55:48] = m_cmd_format;
  endfunction
endclass

`endif

