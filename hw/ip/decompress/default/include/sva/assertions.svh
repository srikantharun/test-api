`ifndef DECOMPRESS_SVAS_SV
`define DECOMPRESS_SVAS_SV

  `include "prim_assert.sv"

  localparam MAX_TRANS_SIZE = 4096;

  // FSM valid state transition
  `ASSERT(fsm_valid_states, state_en |-> next_state inside {ST_IDLE,ST_HEADER,ST_SCHEME,ST_FVC_INIT,ST_FVC_DECOMP,ST_FVC_DRAIN,ST_ZRLE,ST_NO_COMP,ST_BYPASS,ST_INT4} , i_clk, !i_rst_n)
  `ASSERT(fsm_idle_valid_trans, (state == ST_IDLE) & state_en |=> state inside {ST_HEADER,ST_BYPASS} , i_clk, !i_rst_n)
  `ASSERT(fsm_header_valid_trans, (state == ST_HEADER) & state_en |=> state inside {ST_SCHEME} , i_clk, !i_rst_n)
  `ASSERT(fsm_scheme_valid_trans, (state == ST_SCHEME) & state_en |=> state inside {ST_FVC_INIT,ST_ZRLE,ST_NO_COMP,ST_INT4} , i_clk, !i_rst_n)
  `ASSERT(fsm_fvc_init_valid_trans, (state == ST_FVC_INIT) & state_en |=> state inside {ST_FVC_DECOMP} , i_clk, !i_rst_n)
  `ASSERT(fsm_fvc_decomp_valid_trans, (state == ST_FVC_DECOMP) & state_en |=> state inside {ST_FVC_DRAIN} , i_clk, !i_rst_n)
  `ASSERT(fsm_fvc_drain_valid_trans, (state == ST_FVC_DRAIN) & state_en |=> state inside {ST_SCHEME, ST_IDLE} , i_clk, !i_rst_n)
  `ASSERT(fsm_zrle_valid_trans, (state == ST_ZRLE) & state_en |=> state inside {ST_SCHEME, ST_IDLE} , i_clk, !i_rst_n)
  `ASSERT(fsm_int4_valid_trans, (state == ST_INT4) & state_en |=> state inside {ST_SCHEME, ST_IDLE} , i_clk, !i_rst_n)
  `ASSERT(fsm_no_comp_valid_trans, (state == ST_NO_COMP) & state_en |=> state inside {ST_SCHEME, ST_IDLE} , i_clk, !i_rst_n)
  `ASSERT(states_ready, (state == ST_IDLE) | (state==ST_ZRLE)  |-> ~axis_m_ready , i_clk, !i_rst_n)

   // The compression enable bit remains stable during the decompression
  `ASSERT(compression_en_stable, ~(state inside {ST_IDLE, ST_HEADER}) |=> $stable(compression_enable), i_clk, !i_rst_n)

  // The compression scheme has only allowed values
  //`ASSERT(valid_compression_scheme, state inside {ST_FVC_INIT,ST_FVC_DECOMP,ST_FVC_DRAIN,ST_ZRLE,ST_NO_COMP,ST_INT4} |-> (compression_scheme != INVALID), i_clk, !i_rst_n)

  // Stream transfer size
  // Max value
  `ASSERT(stream_transfer_size_max, state != ST_IDLE |-> (stream_transfer_size <= MAX_TRANS_SIZE)  & (stream_transfer_cnt < MAX_TRANS_SIZE ) , i_clk, !i_rst_n)
  // Stable
  `ASSERT(stream_transfer_size_stable, compression_enable & (state inside {ST_SCHEME,ST_FVC_INIT,ST_FVC_DECOMP,ST_FVC_DRAIN,ST_ZRLE,ST_NO_COMP,ST_INT4,ST_BYPASS}) |=> $stable(stream_transfer_size), i_clk, !i_rst_n)
  // state transition
  `ASSERT(stream_done_state, stream_done |=> (state == ST_IDLE) , i_clk, !i_rst_n)

  // Scheme transfer size
  // Max value
  `ASSERT(uncomp_scheme_transfer_size_max, ~(state inside  {ST_IDLE, ST_HEADER, ST_SCHEME}) |-> (uncomp_scheme_transfer_size <= MAX_TRANS_SIZE)  & (scheme_transfer_cnt < MAX_TRANS_SIZE ) , i_clk, !i_rst_n)
   // Stable
  `ASSERT(uncomp_scheme_transfer_size_stable, compression_enable & (state inside {ST_FVC_INIT,ST_FVC_DECOMP,ST_FVC_DRAIN,ST_ZRLE,ST_NO_COMP,ST_INT4,ST_BYPASS}) |=> $stable(uncomp_scheme_transfer_size), i_clk, !i_rst_n)
  // state transition
  `ASSERT(scheme_done_state, scheme_transfer_done & ~stream_done & (state inside  {ST_FVC_DRAIN,ST_ZRLE,ST_INT4,ST_NO_COMP}) |=> (state == ST_SCHEME) , i_clk, !i_rst_n)

  // FVC compression scheme
  // Set and clear buffer never asserted together
  for (genvar i = 0; i < DECOMP_NUM_BUF; i++) begin
    `ASSERT(set_clr_never_same_cycle,set_buf_en & clr_buf_en |->  ~(set_buf[i] & clr_buf[i]) , i_clk, !i_rst_n)
  end
  // Single victim buffer selected
  `ASSERT(set_buf_onehot, set_buf_en |-> $onehot(set_buf) , i_clk, !i_rst_n)

  // Buffers valid only in FVC states
  `ASSERT(buf_valid_states, |buf_valid |-> state inside {ST_FVC_INIT, ST_FVC_DECOMP, ST_FVC_DRAIN} , i_clk, !i_rst_n)

  //Mask calculation
  `ASSERT(mask_value, (state inside {ST_FVC_INIT, ST_FVC_DECOMP}) |->  $countones(mask) == mask_count_ones , i_clk, !i_rst_n)

  `endif  // DECOMPRESS_SVAS_SV
