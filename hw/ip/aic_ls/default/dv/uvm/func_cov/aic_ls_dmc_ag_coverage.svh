// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD-ODR Address
//   Generator Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

//address generator cmd received by dmc devices
covergroup dmc_ag_cg (string cg_name) with function sample( dmc_addr_gen_seq_item ag_item, string dev, aic_ls_seq_item ls_item);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_dim_width_a: coverpoint ag_item.m_cmd.dim_width_a {
    bins ZERO        = {0};
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_dim_width_b: coverpoint ag_item.m_cmd.dim_width_b iff (ag_item.m_num_dim >= 2) {
    bins ZERO        = {0};
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_dim_width_c: coverpoint ag_item.m_cmd.dim_width_c iff (ag_item.m_num_dim >= 3) {
    bins ZERO        = {0};
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_dim_width_d: coverpoint ag_item.m_cmd.dim_width_d iff (ag_item.m_num_dim == 4) {
    bins ZERO        = {0};
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_dim_offset_a: coverpoint ag_item.m_dim_offset_a {
    bins NEG_SIX_BELOW        = {[$:-6]};
    bins NEG_FIVE_TO_NEG_TWO  = {[-5:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_FIVE          = {[2:5]};
    bins SIX_ABOVE            = {[6:$]};
  }

  cp_dim_offset_b: coverpoint ag_item.m_dim_offset_b iff (ag_item.m_num_dim >= 2) {
    bins NEG_SIX_BELOW        = {[$:-6]};
    bins NEG_FIVE_TO_NEG_TWO  = {[-5:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_FIVE          = {[2:5]};
    bins SIX_ABOVE            = {[6:$]};
  }

  cp_dim_offset_c: coverpoint ag_item.m_dim_offset_c iff (ag_item.m_num_dim >= 3) {
    bins NEG_SIX_BELOW        = {[$:-6]};
    bins NEG_FIVE_TO_NEG_TWO  = {[-5:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_FIVE          = {[2:5]};
    bins SIX_ABOVE            = {[6:$]};
  }

  cp_dim_offset_d: coverpoint ag_item.m_dim_offset_d iff (ag_item.m_num_dim == 4) {
    bins NEG_SIX_BELOW        = {[$:-6]};
    bins NEG_FIVE_TO_NEG_TWO  = {[-5:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_FIVE          = {[2:5]};
    bins SIX_ABOVE            = {[6:$]};
  }

  cp_inner_len_a: coverpoint ag_item.m_cmd.inner_length_a {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_inner_len_b: coverpoint ag_item.m_cmd.inner_length_b iff (ag_item.m_num_dim >= 2) {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_inner_len_c: coverpoint ag_item.m_cmd.inner_length_c iff (ag_item.m_num_dim >= 3) {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_inner_len_d: coverpoint ag_item.m_cmd.inner_length_d iff (ag_item.m_num_dim == 4) {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_outer_len_a: coverpoint ag_item.m_cmd.outer_length_a {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_outer_len_b: coverpoint ag_item.m_cmd.outer_length_b iff (ag_item.m_num_dim >= 2){
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_outer_len_c: coverpoint ag_item.m_cmd.outer_length_c iff (ag_item.m_num_dim >= 3) {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_outer_len_d: coverpoint ag_item.m_cmd.outer_length_d iff (ag_item.m_num_dim == 4) {
    bins ONE         = {1};
    bins TWO_TO_FIVE = {[2:5]};
    bins SIX_ABOVE   = {[6:$]};
  }

  cp_inner_stride_a: coverpoint ag_item.m_inner_stride_a {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_inner_stride_b: coverpoint ag_item.m_inner_stride_b iff (ag_item.m_num_dim >= 2){
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_inner_stride_c: coverpoint ag_item.m_inner_stride_c iff (ag_item.m_num_dim >= 3) {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_inner_stride_d: coverpoint ag_item.m_inner_stride_d iff (ag_item.m_num_dim == 4) {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_outer_stride_a: coverpoint ag_item.m_outer_stride_a {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_outer_stride_b: coverpoint ag_item.m_outer_stride_b iff (ag_item.m_num_dim >= 2){
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_outer_stride_c: coverpoint ag_item.m_outer_stride_c iff (ag_item.m_num_dim >= 3) {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_outer_stride_d: coverpoint ag_item.m_outer_stride_d iff (ag_item.m_num_dim == 4) {
    bins NEG_FIVE_TO_NEG_FOUR = {[-5:-4]};
    bins NEG_THREE_TO_NEG_TWO = {[-3:-2]};
    bins NEG_ONE              = {-1};
    bins ZERO                 = {0};
    bins ONE                  = {1};
    bins TWO_TO_THREE         = {[2:3]};
    bins FOUR_TO_FIVE         = {[4:5]};
  }

  cp_mem_stride_a: coverpoint (ag_item.m_cmd.mem_stride_a/64) iff (ag_item.m_num_dim >= 1) {
    bins MEM_STR_0   = {0};
    bins MEM_STR_64  = {1};
    bins MEM_STR_128 = {2};
    bins MEM_STR_192 = {3};
    bins MEM_STR_256 = {4};
    bins MEM_STR_320 = {5};
  }

  cp_mem_stride_b: coverpoint (ag_item.m_cmd.mem_stride_b/64) iff (ag_item.m_num_dim >= 2) {
    bins MEM_STR_0   = {0};
    bins MEM_STR_64  = {1};
    bins MEM_STR_128 = {2};
    bins MEM_STR_192 = {3};
    bins MEM_STR_256 = {4};
    bins MEM_STR_320 = {5};
  }

  cp_mem_stride_c: coverpoint (ag_item.m_cmd.mem_stride_c/64) iff (ag_item.m_num_dim >= 3) {
    bins MEM_STR_0   = {0};
    bins MEM_STR_64  = {1};
    bins MEM_STR_128 = {2};
    bins MEM_STR_192 = {3};
    bins MEM_STR_256 = {4};
    bins MEM_STR_320 = {5};
  }

  cp_mem_stride_d: coverpoint (ag_item.m_cmd.mem_stride_d/64) iff (ag_item.m_num_dim == 4) {
    bins MEM_STR_0   = {0};
    bins MEM_STR_64  = {1};
    bins MEM_STR_128 = {2};
    bins MEM_STR_192 = {3};
    bins MEM_STR_256 = {4};
    bins MEM_STR_320 = {5};
  }

  cp_mem_bsize: coverpoint (ag_item.m_cmd.mem_bsize) {
    bins ZERO               = {0};
    bins BELOW_1K           = {[1:1023]};
    bins BETWEEN_1K_TO_4K   = {[1024:4096]};
    bins AFTER_4K_AND_ABOVE = {[4097:$]};
  }

  cp_decompression: coverpoint (ag_item.m_cmd.decomp_en) iff (dev == "m_ifdw") {
    bins DISABLED = {0};
    bins ENABLED  = {1};
  }

  cp_vtrsp_mode: coverpoint (ag_item.m_cmd.vtrsp_mode) iff (dev inside {"d_odr", "m_odr", "m_ifdw"}) {
    bins DISABLED = {0};
    bins FP8      = {1};
    bins FP16     = {2};
    bins FP32     = {3};
  }

  cp_vtrsp_len: coverpoint (ag_item.m_pword_len) iff (dev inside {"d_odr", "m_odr", "m_ifdw"}) {
    bins LEN_0              = {0};
    bins LEN_64             = {64};
    bins LEN_128            = {128};
    bins LEN_192            = {192};
    bins LEN_256_AND_ABOVE  = {[256:$]};
  }

  cp_vect_dim: coverpoint (ag_item.m_cmd.vect_dim) {
    bins DIM_1 = {0};
    bins DIM_2 = {1};
    bins DIM_3 = {2};
    bins DIM_4 = {3};
  }

  cp_vector_mode: coverpoint (ag_item.header_vector_mode) {
    bins INT8   = {0};
    bins INT16  = {1};
  }

  cp_format: coverpoint (ag_item.m_format) {
    bins INT8   = {0};
    bins INT16  = {1};
  }

  cp_pad_mode: coverpoint (ag_item.m_cmd.pad_mode) {
    bins REGULAR = {0};
    bins EDGE    = {1};
  }

  cp_pad_val: coverpoint (ag_item.m_pad_val) {
    bins NEGATIVE_16_BIT[8]   = {[-32768:-128]};
    bins NEGATIVE_8_BIT[4]    = {[-128:-1]};
    bins ZERO                 = {0};
    bins POSITIVE_8_BIT[4]    = {[1:127]};
    bins POSITIVE_16_BIT[8]   = {[128:32767]};
  }

  cp_intra_pad_val: coverpoint (ag_item.m_intra_pad_val) {
    bins NEGATIVE_16_BIT[8]  = {[-32768:-128]};
    bins NEGATIVE_8_BIT[4]   = {[-128:-1]};
    bins ZERO                = {0};
    bins POSITIVE_8_BIT[4]   = {[1:127]};
    bins POSITIVE_16_BIT[8]  = {[128:32767]};
  }

  cp_mask_start: coverpoint (ag_item.m_cmd.mask_start) {
    bins MASK_START[]  = {[0:63]};
  }

  cp_mask_end: coverpoint (ag_item.m_cmd.mask_end) {
    bins MASK_END[]  = {[0:64]};
  }

  cp_mem_offset: coverpoint (ag_item.m_cmd.mem_offset) {
    bins NO_OFFSET     = {0};
    bins SMALL_OFFSET  = {[1:'hFFFF]};
    bins LARGE_OFFSET  = {['h1_0000:$]};
  }

  cp_ringbuffsize: coverpoint (ag_item.m_cmd.ring_buff_size/AIC_DMC_COV_RINGBUFF_SIZE_GRANULARITY) {
    bins DISABLED             = {0};
    bins GRANULARITY_1        = {1};
    bins GRANULARITY_2_TO_8   = {[2:8]};
    bins GRANULARITY_9_TO_16  = {[9:16]};
    bins GRANULARITY_17_ABOVE = {[17:$]};
  }

  cp_length: coverpoint (ag_item.m_length) iff (ag_item.m_cmd_format == CMDFORMAT_LINEAR) {
    bins PW_1_to_100     = {[1:100]};
    bins PW_101_TO_1000  = {[101:1000]};
    bins PW_1001_ABOVE   = {[1001:$]};
  }

  cp_cid_target: coverpoint (ag_item.m_cmd.mem_baseaddr[31:28]) iff (ag_item.m_cmd.mem_baseaddr[31:28] == ls_item.cid) {
    bins AI_CORE_1 = {1};
    bins AI_CORE_2 = {2};
    bins AI_CORE_3 = {3};
    bins AI_CORE_4 = {4};
    bins AI_CORE_5 = {5};
    bins AI_CORE_6 = {6};
    bins AI_CORE_7 = {7};
    bins AI_CORE_8 = {8};
  }

  cp_l1_bank: coverpoint (ag_item.m_cmd.mem_baseaddr[AIC_DMC_COV_MMIO_ADDR_WIDTH-1:0]) iff (ag_item.m_cmd.mem_baseaddr[AIC_DMC_COV_MMIO_ADDR_WIDTH-1:0] inside {[AIC_DMC_COV_L1_ADDR_START:AIC_DMC_COV_L1_ADDR_END]})
  {
    bins BANK_NUM[AIC_DMC_COV_L1_NUM_BANKS] = {[AIC_DMC_COV_L1_ADDR_START:AIC_DMC_COV_L1_ADDR_END]};
  }

  cp_cmd_format: coverpoint ag_item.m_cmd_format {
    bins DEFBASED           = {0};
    bins LINEAR             = {1};
    bins THREE_DIM_FALLBACK = {2};
    bins OFFSET_DEF_BASED   = {3};
    bins FOUR_DIM_FALLBACK  = {4};
  }

  cp_cmd_format_transition: coverpoint ag_item.m_cmd_format {
    bins DEFBASED_TO_ANY              = (3'b000=> [1:4]);
    bins LINEAR_TO_ANY                = (3'b001=> 0, [2:4]);
    bins THREE_DIM_FALLBACK_TO_ANY    = (3'b010=> [0:1], [3:4]);
    bins OFFSET_DEF_BASED_TO_ANY      = (3'b011=> [0:2], 4);
    bins FOUR_DIM_FALLBACK_TO_ANY     = (3'b100=> [0:3]);
    bins DEFBASED_BACK2BACK           = (3'b000=> 3'b000);
    bins LINEAR_BACK2BACK             = (3'b001=> 3'b001);
    bins THREE_DIM_FALLBACK_BACK2BACK = (3'b010=> 3'b010);
    bins OFFSET_DEF_BASED_BACK2BACK   = (3'b011=> 3'b011);
    bins FOUR_DIM_FALLBACK_BACK2BACK  = (3'b100=> 3'b100);
  }

  cp_decompression_transition: coverpoint (ag_item.m_cmd.decomp_en) iff (dev == "m_ifdw" && ag_item.m_cmd_format== CMDFORMAT_LINEAR) {
    bins DISABLED_DISABLED = (0 => 0);
    bins DISABLED_ENABLED  = (0 => 1);
    bins ENABLED_DISABLED  = (1 => 0);
    bins ENABLED_ENABLED   = (1 => 1);
  }

  cp_num_dim: coverpoint ag_item.m_num_dim {
    bins DIM_1 = {1};
    bins DIM_2 = {2};
    bins DIM_3 = {3};
    bins DIM_4 = {4};
  }

  cp_dim_def_ptr: coverpoint ag_item.m_dim_def_ptr {
    bins PTR[] = {[0:127]};
  }

  cp_loop_def_ptr: coverpoint ag_item.m_loop_def_ptr {
    bins PTR[] = {[0:127]};
  }

  cross_format_vector_mode: cross cp_format, cp_vector_mode {
    bins VEC8_TO_MEM8   = binsof(cp_format.INT8) && binsof(cp_vector_mode.INT8);
    bins VEC16_TO_MEM16 = binsof(cp_format.INT16) && binsof(cp_vector_mode.INT16);
    bins VEC16_TO_MEM8  = binsof(cp_format.INT8) && binsof(cp_vector_mode.INT16);
    ignore_bins VEC8_TO_MEM16 = binsof(cp_format.INT16) && binsof(cp_vector_mode.INT8);
  }

  cross_vtrsp_int_format: cross cp_vtrsp_mode, cross_format_vector_mode;

  cross_decompression_int_format: cross cp_decompression, cross_format_vector_mode;

  cross_cmd_format__num_dim: cross cp_cmd_format, cp_num_dim {
    ignore_bins LINEAR_MULTIDIM = binsof(cp_cmd_format.LINEAR) && binsof(cp_num_dim) intersect {[2:$]};
    ignore_bins THREE_DIM_ONLY = binsof(cp_cmd_format.THREE_DIM_FALLBACK) && !binsof(cp_num_dim.DIM_3);
    ignore_bins FOUR_DIM_ONLY = binsof(cp_cmd_format.FOUR_DIM_FALLBACK) && !binsof(cp_num_dim.DIM_4);
  }

  cross_cmd_format__dim_def_ptr: cross cp_cmd_format, cp_dim_def_ptr {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
    ignore_bins THREE_DIM_FALLBACK = binsof(cp_cmd_format.THREE_DIM_FALLBACK);
    ignore_bins FOUR_DIM_FALLBACK = binsof(cp_cmd_format.FOUR_DIM_FALLBACK);
  }

  cross_cmd_format__loop_def_ptr: cross cp_cmd_format, cp_loop_def_ptr {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
    ignore_bins THREE_DIM_FALLBACK = binsof(cp_cmd_format.THREE_DIM_FALLBACK);
    ignore_bins FOUR_DIM_FALLBACK = binsof(cp_cmd_format.FOUR_DIM_FALLBACK);
  }

  cross_cmd_format__mem_bsize: cross cp_cmd_format, cp_mem_bsize {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_num_dim__vect_dim: cross cp_num_dim, cp_vect_dim {
    ignore_bins DIM_1_ON_NON_DIM_1   = binsof(cp_num_dim.DIM_1) && !binsof(cp_vect_dim.DIM_1);
    ignore_bins DIM_2_ON_DIM_2_ABOVE = binsof(cp_num_dim.DIM_2) && binsof(cp_vect_dim) intersect {[2:3]};
    ignore_bins DIM_3_ON_DIM_4       = binsof(cp_num_dim.DIM_3) && binsof(cp_vect_dim.DIM_4);
  }

  cross__vect_dim__mask_start: cross cp_vect_dim, cp_mask_start;

  cross__vect_dim__mask_end: cross cp_vect_dim, cp_mask_end;

  cross_cmd_format__mask_start: cross cp_cmd_format, cp_mask_start {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_cmd_format__mask_end: cross cp_cmd_format, cp_mask_end {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_cmd_format__pad_val: cross cp_cmd_format, cp_pad_val {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_cmd_format__intra_pad_val: cross cp_cmd_format, cp_intra_pad_val {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_cmd_format__pad_mode: cross cp_cmd_format, cp_pad_mode {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_cid_target__l1_bank: cross cp_cid_target, cp_l1_bank; // removed cross with cmdformat as l1_bank and cid have nothing to do w/ it

  cross_cmd_format__mem_offset__ringbuffersize: cross cp_cmd_format, cp_mem_offset, cp_ringbuffsize {
    ignore_bins LINEAR = binsof(cp_cmd_format.LINEAR);
  }

  cross_vtrsp_mode__vtrsp_len: cross cp_vtrsp_mode, cp_vtrsp_len {
    ignore_bins VTRSP_OFF = binsof(cp_vtrsp_mode.DISABLED);
  }

  // Dimension Parameters Cross Coverage
  // DIM_WIDTH X DIM_OFFSETS
  cross_num_dim__dim_width__dim_offset_A: cross cp_num_dim, cp_dim_width_a, cp_dim_offset_a;
  cross_num_dim__dim_width__dim_offset_B: cross cp_num_dim, cp_dim_width_b, cp_dim_offset_b {
    ignore_bins DIM_1_ON_B = binsof(cp_num_dim.DIM_1);
  }
  cross_num_dim__dim_width__dim_offset_C: cross cp_num_dim, cp_dim_width_c, cp_dim_offset_c {
    ignore_bins DIM_1_ON_C = binsof(cp_num_dim.DIM_1);
    ignore_bins DIM_2_ON_C = binsof(cp_num_dim.DIM_2);
  }
  cross_num_dim__dim_width__dim_offset_D: cross cp_num_dim, cp_dim_width_d, cp_dim_offset_d {
    ignore_bins DIM_1_ON_D = binsof(cp_num_dim.DIM_1);
    ignore_bins DIM_2_ON_D = binsof(cp_num_dim.DIM_2);
    ignore_bins DIM_3_ON_D = binsof(cp_num_dim.DIM_3);
  }
  // DIM_WIDTH x OUTER LEN X INNER LEN
  cross_num_dim__dim_width__outer_len__inner_len_A: cross cp_num_dim, cp_dim_width_a, cp_outer_len_a, cp_inner_len_a;
  cross_num_dim__dim_width__outer_len__inner_len_B: cross cp_num_dim, cp_dim_width_b, cp_outer_len_b, cp_inner_len_b {
    ignore_bins LEN_1_ON_B = binsof(cp_num_dim.DIM_1);
  }
  cross_num_dim__dim_width__outer_len__inner_len_C: cross cp_num_dim, cp_dim_width_c, cp_outer_len_c, cp_inner_len_c {
    ignore_bins LEN_1_ON_C = binsof(cp_num_dim.DIM_1);
    ignore_bins LEN_2_ON_C = binsof(cp_num_dim.DIM_2);
  }
  cross_num_dim__dim_width__outer_len__inner_len_D: cross cp_num_dim, cp_dim_width_d, cp_outer_len_d, cp_inner_len_d {
    ignore_bins LEN_1_ON_D = binsof(cp_num_dim.DIM_1);
    ignore_bins LEN_2_ON_D = binsof(cp_num_dim.DIM_2);
    ignore_bins LEN_3_ON_D = binsof(cp_num_dim.DIM_3);
  }
  // OUTER STRIDE X INNER STRIDE
  cross_num_dim__outer_stride__inner_stride_A: cross cp_num_dim, cp_outer_stride_a, cp_inner_stride_a;
  cross_num_dim__outer_stride__inner_stride_B: cross cp_num_dim, cp_outer_stride_b, cp_inner_stride_b {
    ignore_bins STRIDE_1_ON_B = binsof(cp_num_dim.DIM_1);
  }
  cross_num_dim__outer_stride__inner_stride_C: cross cp_num_dim, cp_outer_stride_c, cp_inner_stride_c {
    ignore_bins STRIDE_1_ON_C = binsof(cp_num_dim.DIM_1);
    ignore_bins STRIDE_2_ON_C = binsof(cp_num_dim.DIM_2);
  }
  cross_num_dim__outer_stride__inner_stride_D: cross cp_num_dim, cp_outer_stride_d, cp_inner_stride_d {
    ignore_bins STRIDE_1_ON_D = binsof(cp_num_dim.DIM_1);
    ignore_bins STRIDE_2_ON_D = binsof(cp_num_dim.DIM_2);
    ignore_bins STRIDE_3_ON_D = binsof(cp_num_dim.DIM_3);
  }

  // Same parameters Cross
  // Dim width cross Coverage
  cross_dim_width_AtoB: cross cp_dim_width_a, cp_dim_width_b iff (ag_item.m_num_dim >= 2);
  cross_dim_width_AtoC: cross cp_dim_width_a, cp_dim_width_b, cp_dim_width_c iff (ag_item.m_num_dim >= 3);
  cross_dim_width_AtoD: cross cp_dim_width_a, cp_dim_width_b, cp_dim_width_c, cp_dim_width_d iff (ag_item.m_num_dim == 4);
  
  // Dim offset cross Coverage
  cross_dim_offset_AtoB: cross cp_dim_offset_a, cp_dim_offset_b iff (ag_item.m_num_dim >= 2);
  cross_dim_offset_AtoC: cross cp_dim_offset_a, cp_dim_offset_b, cp_dim_offset_c iff (ag_item.m_num_dim >= 3);
  cross_dim_offset_AtoD: cross cp_dim_offset_a, cp_dim_offset_b, cp_dim_offset_c, cp_dim_offset_d iff (ag_item.m_num_dim == 4);

  // Inner Length cross Coverage
  cross_inner_len_AtoB: cross cp_inner_len_a, cp_inner_len_b iff (ag_item.m_num_dim >= 2);
  cross_inner_len_AtoC: cross cp_inner_len_a, cp_inner_len_b, cp_inner_len_c iff (ag_item.m_num_dim >= 3);
  cross_inner_len_AtoD: cross cp_inner_len_a, cp_inner_len_b, cp_inner_len_c, cp_inner_len_d iff (ag_item.m_num_dim == 4);

  // Outer Length cross Coverage
  cross_outer_len_AtoB: cross cp_outer_len_a, cp_outer_len_b iff (ag_item.m_num_dim >= 2);
  cross_outer_len_AtoC: cross cp_outer_len_a, cp_outer_len_b, cp_outer_len_c iff (ag_item.m_num_dim >= 3);
  cross_outer_len_AtoD: cross cp_outer_len_a, cp_outer_len_b, cp_outer_len_c, cp_outer_len_d iff (ag_item.m_num_dim == 4);

  // Inner Stride cross Coverage
  cross_inner_stride_AtoB: cross cp_inner_stride_a, cp_inner_stride_b iff (ag_item.m_num_dim >= 2);
  cross_inner_stride_AtoC: cross cp_inner_stride_a, cp_inner_stride_b, cp_inner_stride_c iff (ag_item.m_num_dim >= 3);
  cross_inner_stride_AtoD: cross cp_inner_stride_a, cp_inner_stride_b, cp_inner_stride_c, cp_inner_stride_d iff (ag_item.m_num_dim == 4);

  // Outer Stride cross Coverage
  cross_outer_stride_AtoB: cross cp_outer_stride_a, cp_outer_stride_b iff (ag_item.m_num_dim >= 2);
  cross_outer_stride_AtoC: cross cp_outer_stride_a, cp_outer_stride_b, cp_outer_stride_c iff (ag_item.m_num_dim >= 3);
  cross_outer_stride_AtoD: cross cp_outer_stride_a, cp_outer_stride_b, cp_outer_stride_c, cp_outer_stride_d iff (ag_item.m_num_dim == 4);

  // Mem Stride cross Coverage, cross mem stride with dim_width in relation to equation: m_mem_stride_x-1 == m_dim_width_x * m_mem_stride_x;
  cross_mem_stride_a__dim_width_b: cross cp_mem_stride_a, cp_dim_width_b iff (ag_item.m_num_dim >= 2);
  cross_mem_stride_b__dim_width_c: cross cp_mem_stride_b, cp_dim_width_c iff (ag_item.m_num_dim >= 3);
  cross_mem_stride_c__dim_width_d: cross cp_mem_stride_c, cp_dim_width_d iff (ag_item.m_num_dim == 4);

  // mask coverage wrt vect_dim and dim_width
  cp_mask_start_A_width_eq_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_a==1 && ag_item.m_cmd.vect_dim==0) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_start_A_width_grt_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_a > 1 && ag_item.m_cmd.vect_dim==0) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_end_A_width_eq_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_a==1 && ag_item.m_cmd.vect_dim==0) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_end_A_width_grt_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_a > 1 && ag_item.m_cmd.vect_dim==0) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_start_B_width_eq_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_b==1 && ag_item.m_cmd.vect_dim==1) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_start_B_width_grt_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_b > 1 && ag_item.m_cmd.vect_dim==1) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_end_B_width_eq_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_b==1 && ag_item.m_cmd.vect_dim==1) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_end_B_width_grt_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_b > 1 && ag_item.m_cmd.vect_dim==1) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_start_C_width_eq_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_c==1 && ag_item.m_cmd.vect_dim==2) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_start_C_width_grt_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_c > 1 && ag_item.m_cmd.vect_dim==2) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_end_C_width_eq_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_c==1 && ag_item.m_cmd.vect_dim==2) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_end_C_width_grt_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_c > 1 && ag_item.m_cmd.vect_dim==2) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_start_D_width_eq_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_d==1 && ag_item.m_cmd.vect_dim==3) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_start_D_width_grt_1: coverpoint (ag_item.m_cmd.mask_start) iff (ag_item.m_cmd.dim_width_d > 1 && ag_item.m_cmd.vect_dim==3) {
    bins MASK_START[]  = {[0:63]};
  }
  cp_mask_end_D_width_eq_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_d==1 && ag_item.m_cmd.vect_dim==3) {
    bins MASK_END[]  = {[0:64]};
  }
  cp_mask_end_D_width_grt_1: coverpoint (ag_item.m_cmd.mask_end) iff (ag_item.m_cmd.dim_width_d > 1 && ag_item.m_cmd.vect_dim==3) {
    bins MASK_END[]  = {[0:64]};
  }
endgroup
