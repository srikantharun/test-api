// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Weight decompression engine
// Owner: Spyridoula Koumousi <koumousi.spyridoula@axelera.ai>

`ifndef DECOMPRESS_SV
`define DECOMPRESS_SV

module decompress
  import decompress_pkg::*;
(
  // Clock and reset signals
  input wire i_clk,
  input wire i_rst_n,

  // =====================================================
  // Inteface to manager AXI-S port
  // =====================================================
  input  logic          axis_m_valid,
  output logic          axis_m_ready,
  input  logic [DECOMP_DW-1:0] axis_m_data,
  input  logic          axis_m_last,

  // =====================================================
  // Inteface to subordinate AXI-S port
  // =====================================================
  output logic          axis_s_valid,
  input  logic          axis_s_ready,
  output logic [DECOMP_DW-1:0] axis_s_data,
  output logic          axis_s_last,

  // =====================================================
  // Inteface to instruction commands
  // =====================================================
  input  logic cmd_valid,
  input  logic cmd_data,
  output logic cmd_ready,

  // =====================================================
  // State observation
  // =====================================================
  output ifd_csr_reg_pkg::ifd_csr_hw2reg_dp_status_reg_t decomp_status,
  output logic                                           decomp_invalid_stream_header,
  output logic                                           decomp_invalid_scheme_header,
  output logic                                           decomp_invalid_compressed_size,
  output logic                                           decomp_invalid_uncompressed_size,
  output logic                                           decomp_fvc_decomp_stuck
);

  // =====================================================
  // Signal declarations
  // =====================================================

  logic                                                     compression_enable;
  state_t                                                   state;
  logic       [                  DECOMP_NUM_BUF-1:0][      DECOMP_DW-1:0] buf_data;
  logic       [                  DECOMP_NUM_BUF-1:0][      DECOMP_DW-1:0] buf_data_q;
  logic       [                  DECOMP_NUM_BUF-1:0]               buf_valid;
  logic       [                  DECOMP_NUM_BUF-1:0]               buf_set_last;
  logic       [                  DECOMP_NUM_BUF-1:0]               lowest_invalid_buf;
  logic       [                  DECOMP_NUM_BUF-1:0]               next_invalid_buf;
  logic       [          $clog2(DECOMP_NUM_BUF)-1:0]               curr_buf;
  logic       [          $clog2(DECOMP_NUM_BUF)-1:0]               prev_buf;
  logic       [       $clog2(DECOMP_NUM_BUF*64)-1:0]               pre_byte_offset;
  logic       [       $clog2(DECOMP_NUM_BUF*64)-1:0]               byte_offset;

  scheme_t                                                  compression_scheme;

  logic                                                     cmd_ready_int;
  logic                                                     cmd_data_int;
  logic                                                     cmd_valid_int;
  logic                                                     compression_enable_en;
  logic                                                     next_compression_enable;

  logic                                                     state_en;
  state_t                                                   next_state;

  scheme_t                                                  next_compression_scheme;
  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               effective_buf;
  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               effective_buf_sel;
  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               effective_buf_q;

  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               pre_mask_shift;
  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               data_mask;
  logic       [           (DECOMP_NUM_BUF+2)*DECOMP_DW-1:0]               data_shift;

  logic                                                     clr_buf_en;
  logic       [                  DECOMP_NUM_BUF-1:0]               clr_buf;
  logic       [                  DECOMP_NUM_BUF-1:0]               clr_buf_sel;
  logic                                                     set_buf_en;
  logic       [                  DECOMP_NUM_BUF-1:0]               victim_sel_buf;
  logic       [                  DECOMP_NUM_BUF-1:0]               set_buf;
  logic       [                  DECOMP_NUM_BUF-1:0]               buf_valid_en;
  logic       [                  DECOMP_NUM_BUF-1:0]               next_buf_valid;


  logic       [                     DECOMP_DW/8-1:0]               pre_mask;
  logic       [                     DECOMP_DW/8-1:0]               mask;
  logic       [               DECOMP_NUM_SLICES-1:0][         2:0] pre_mask_cnt;
  logic       [$clog2($bits(pre_mask)+1)-1:0]               pre_mask_count_ones;
  logic       [    $clog2($bits(mask)+1)-1:0]               mask_count_ones;
  logic                                                     valid;
  logic                                                     ready;
  logic       [                       DECOMP_DW-1:0]               data;
  logic                                                     last;

  logic       [       $clog2(DECOMP_NUM_BUF*64)-1:0]               next_pre_byte_offset_calc;
  logic       [          $clog2(DECOMP_NUM_BUF)-1:0]               pre_buff_target_start;
  logic       [          $clog2(DECOMP_NUM_BUF)-1:0]               pre_buff_target_end;
  logic                                                     pre_byte_offset_en;
  logic       [       $clog2(DECOMP_NUM_BUF*64)-1:0]               next_pre_byte_offset;
  logic       [          $clog2(DECOMP_NUM_BUF)-1:0]               next_curr_buf;
  logic                                                     decompressed_transfer_cnt_set;
  logic                                                     decompressed_transfer_cnt_clr;
  logic       [                         15:0]               next_decompressed_transfer_cnt;
  logic                                                     decompressed_transfer_cnt_en;
  logic       [                         15:0]               decompressed_transfer_cnt;
  logic                                                     decompressed_transfer_done;


  logic                                                     compressed_transfer_cnt_set;
  logic                                                     compressed_transfer_cnt_clr;
  logic       [                         15:0]               next_compressed_transfer_cnt;
  logic                                                     compressed_transfer_cnt_en;
  logic       [                         15:0]               compressed_transfer_cnt;
  logic                                                     compressed_transfer_done;

  logic                                                     stream_done;

  axis_t                                                    zrle;
  axis_t                                                    no_comp;
  axis_t                                                    int4;
  axis_t                                                    mux_stream;

  axis_t                                                    decompressed;
  axis_t                                                    axis_stream;
  comp_axis_t                                               compressed;

  logic                                                     mask_valid;
  logic                                                     pre_valid;
  logic                                                     pre_ready;

  logic                                                     inter_s1_valid;
  logic                                                     inter_s1_ready;
  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_MW-1:0] inter_s1_mask_bin;
  logic       [               DECOMP_NUM_SLICES-1:0][         2:0] inter_s1_mask_dec;
  logic       [               DECOMP_NUM_SLICES-1:0]               inter_s1_data_ready;
  logic       [               DECOMP_NUM_SLICES-1:0]               inter_s1_mask_ready;
  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_DECOMP_DW-1:0] inter_s1_data;
  logic       [               DECOMP_NUM_SLICES-1:0][         6:0] inter_s1_shift;

  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_MW-1:0] inter_s2_mask_bin;
  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_DECOMP_DW-1:0] inter_s2_data;
  logic       [               DECOMP_NUM_SLICES-1:0]               inter_s2_data_valid;
  logic       [               DECOMP_NUM_SLICES-1:0]               inter_s2_mask_valid;
  logic                                                     inter_s2_ready;
  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_MW-1:0] inter_s2_data_idx;
  logic       [               DECOMP_NUM_SLICES-1:0][DECOMP_SLICE_DECOMP_DW-1:0] decomp_data_word;

  logic                                                     header_update;
  logic       [                         15:0]               stream_transfer_size;
  logic       [                         15:0]               next_stream_transfer_size;
  logic                                                     stream_transfer_cnt_set;
  logic                                                     stream_transfer_cnt_clr;
  logic                                                     stream_transfer_cnt_en;
  logic       [                         15:0]               next_stream_transfer_cnt;
  logic       [                         15:0]               stream_transfer_cnt;
  logic                                                     stream_transfer_done;

  logic                                                     scheme_update;
  logic       [                         15:0]               uncomp_scheme_transfer_size;
  logic       [                         15:0]               next_uncomp_scheme_transfer_size;
  logic       [                         15:0]               comp_scheme_transfer_size;
  logic       [                         15:0]               next_comp_scheme_transfer_size;
  logic                                                     scheme_transfer_cnt_set;
  logic                                                     scheme_transfer_cnt_clr;
  logic                                                     scheme_transfer_cnt_en;
  logic       [                         15:0]               next_scheme_transfer_cnt;
  logic       [                         15:0]               scheme_transfer_cnt;
  logic                                                     scheme_transfer_done;

  logic                                                     next_buf_fetch_disable;
  logic                                                     buf_fetch_disable;
  logic                                                     buf_fetch_disable_update;

  logic int4_upper_d, int4_upper_q, int4_upper_en;
  logic [(DECOMP_DW/2)-1:0] int4_pword_upper_d,  int4_pword_upper_q;
  logic int4_pword_upper_en;
  logic [(DECOMP_DW/2)-1:0] int4_compressed;
  logic [DECOMP_DW-1:0] int4_decompresed;


  // =====================================================
  // RTL
  // =====================================================

  // FIFO to sample the compression enable bit from the command line
  cc_stream_buffer #(
    .DEPTH(DECOMP_CMD_DEPTH),
    .DW(1)
  ) u_cmd_fifo (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    // interface to top
    .wr_vld(cmd_valid),
    .wr_data(cmd_data),
    .wr_rdy(cmd_ready),
    // interface to internal buffers
    .rd_rdy(cmd_ready_int),
    .rd_data(cmd_data_int),
    .rd_vld(cmd_valid_int)
  );

  assign compression_enable_en   = cmd_valid_int & cmd_ready_int;
  assign next_compression_enable = cmd_data_int;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      compression_enable <= 1'b0;
    end else if (compression_enable_en) begin
      compression_enable <= next_compression_enable;
    end
  end

  assign cmd_ready_int = (state == ST_IDLE);

  // Assert ready to accept new data when at least one buffer is invalid
  // Bypass in case that compression is not enabled
  assign axis_m_ready = ((state == ST_HEADER) | (state== ST_SCHEME) | (state == ST_FVC_INIT) |
                                ((state == ST_FVC_DECOMP) & ~buf_fetch_disable) & ~&buf_valid )  ? 1'b1 :
                        ((state == ST_BYPASS) | (state== ST_NO_COMP)) ? axis_stream.ready :
                        (state== ST_INT4) ? axis_stream.ready & ~int4_upper_q : 1'b0;

  // Effective  buffers. At all times the early mask calculation and the data selection
  // have visibility of an effective buffer
  assign effective_buf = {
    buf_data[1], buf_data[0], buf_data[4], buf_data[3], buf_data[2], buf_data[1], buf_data[0]
  };
  assign effective_buf_q = {
    buf_data_q[1],
    buf_data_q[0],
    buf_data_q[4],
    buf_data_q[3],
    buf_data_q[2],
    buf_data_q[1],
    buf_data_q[0]
  };

  // Keep track of changes of the current buffer.
  // As soon as the data from a buffer have been consumed
  // then the buffer can be cleared.
  assign next_curr_buf = (state == ST_FVC_DRAIN) ? '0 :
                         (pre_byte_offset > DECOMP_BYTE_CNT_WRAP-1) ?  ((DECOMP_BYTE_CNT_WRAP-1 - pre_byte_offset) / 64) : pre_byte_offset / 64;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      curr_buf <= 3'b000;
      prev_buf <= 3'b000;
    end else begin
      curr_buf <= next_curr_buf;
      prev_buf <= curr_buf;
    end
  end

  // Data buffer valid
  // Upon change of buffer invalidate the buffer(s) that has been used last
  assign clr_buf_en = (curr_buf != prev_buf) | (state == ST_FVC_DRAIN);

  // Decide which buffers to clear
  always_comb begin : _clr_buf_sel_
    // If only one buffer has been used.Default value.
    clr_buf_sel = (1'b1 << prev_buf);
    // Else if multiple buffers have been used.
    // Invalidate multiple.
    unique case ({
      curr_buf, prev_buf
    })
      6'b010000: clr_buf_sel = 5'b00011;
      6'b011001: clr_buf_sel = 5'b00110;
      6'b100010: clr_buf_sel = 5'b01100;
      6'b000011: clr_buf_sel = 5'b11000;
      6'b001100: clr_buf_sel = 5'b10001;
      default:   clr_buf_sel = (1'b1 << prev_buf);
    endcase
  end

  // Select the buffer to be cleared
  assign clr_buf = {DECOMP_NUM_BUF{clr_buf_en}} & clr_buf_sel;

  // Set the buffer if we are receiving new data
  // axis_m_ready is only asserted when we are in ST_FVC_INIT or ST_FVC_DECOMP and
  // there is an available buffer to be used.
  assign set_buf_en = (axis_m_valid & axis_m_ready) & ( (state == ST_FVC_INIT) | (state == ST_FVC_DECOMP) );

  //Select the lowest invalid buffer to be set in the next cycle
  assign lowest_invalid_buf = {
    ~buf_valid[4] & (&buf_valid[3:0]),
    ~buf_valid[3] & (&buf_valid[2:0]),
    ~buf_valid[2] & (&buf_valid[1:0]),
    ~buf_valid[1] & buf_valid[0],
    ~buf_valid[0]
  };

  always_comb begin : _set_buf_sel_
    // Default values
    next_invalid_buf = lowest_invalid_buf;
    unique case (buf_set_last)
      5'b00001: next_invalid_buf = 5'b00010;
      5'b00010: next_invalid_buf = 5'b00100;
      5'b00100: next_invalid_buf = 5'b01000;
      5'b01000: next_invalid_buf = 5'b10000;
      5'b10000: next_invalid_buf = 5'b00001;
      default:  next_invalid_buf = lowest_invalid_buf;
    endcase
  end

  // Buffer victim selection
  // If all buffers are invalid, select the lowest invalid buffer
  // else select the next invalid buffer after the last set buffer
  assign victim_sel_buf = (state == ST_FVC_INIT) ? lowest_invalid_buf : next_invalid_buf;

  assign set_buf = {DECOMP_NUM_BUF{set_buf_en}} & victim_sel_buf;

  // Buffers for the data, set and cleared
  for (genvar i = 0; unsigned'(i) < DECOMP_NUM_BUF; i++) begin : gen_buf_valid

    assign buf_valid_en[i]   = set_buf[i] | clr_buf[i];
    assign next_buf_valid[i] = set_buf[i] & ~clr_buf[i];

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n) begin
        buf_valid[i] <= 1'b0;
      end else if (buf_valid_en[i]) begin
        buf_valid[i] <= next_buf_valid[i];
      end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n) begin
        buf_set_last[i] <= 1'b0;
      end else if (|set_buf) begin
        buf_set_last[i] <= next_buf_valid[i];
      end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n) begin
        buf_data[i] <= '0;
      end else if (set_buf[i]) begin
        buf_data[i] <= axis_m_data;
      end
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n) begin
        buf_data_q[i] <= '0;
      end else if (buf_valid[i] & ready) begin
        buf_data_q[i] <= buf_data[i];
      end
    end

  end
  // ----------------------------------------------------------------------
  // FSM Implementation
  // ----------------------------------------------------------------------
  always_comb begin
    decomp_fvc_decomp_stuck = 1'b0;
    unique case (state)
      // ----------------------------------------------------------------------
      // ST_IDLE
      // ----------------------------------------------------------------------
      // In IDLE state we decode the command that has been received. The command
      // indicates whether compression is enabled for this stream or not.
      // If compression is disabled then go to the BYPASS mode and remain there until
      // the stream is completed (indicated via tlast)
      // If compression is enabled for this stream move to the HEAER state to register
      // the length of the stream
      ST_IDLE: begin
        state_en   = compression_enable_en;
        next_state = next_compression_enable ? ST_HEADER : ST_BYPASS;
      end
      // ----------------------------------------------------------------------
      // ST_HEADER
      // ----------------------------------------------------------------------
      // In this state we decode the HEADER of the compressed stream. The header
      // contains the stream transfer size. This info will be used to monitor the
      // length of the stream and its completion (tlast generation)
      ST_HEADER: begin
        state_en   = axis_m_valid & axis_m_ready;
        next_state = ST_SCHEME;
      end
      // ----------------------------------------------------------------------
      // ST_SCHEME
      // ----------------------------------------------------------------------
      // Each stream might be split into several different compression schemes.
      // In this state we decode the SCHEME of the compressed stream and the
      // length of the transfer size for this scheme. The length of the transfer will
      // be used to determine whether we can switch to a different state.
      ST_SCHEME: begin
        state_en = axis_m_valid & axis_m_ready;
        next_state = (next_compression_scheme == FVC)     ? ST_FVC_INIT :
                     (next_compression_scheme == INT4)    ? ST_INT4 :
                     (next_compression_scheme == ZRLE)    ? ST_ZRLE : ST_NO_COMP;
      end
      // ----------------------------------------------------------------------
      // ST_FVC_INIT
      // ----------------------------------------------------------------------
      // In case the decompression scheme is the FCV then in the first state we
      // fill up the buffers with data that will be later used to decomp the data.
      // If all four are filled then move to FVC decompress state
      ST_FVC_INIT: begin
        state_en   = &buf_valid[3:0] & |buf_valid_en;
        next_state = ST_FVC_DECOMP;
      end
      // ----------------------------------------------------------------------
      // ST_FVC_DECOMP
      // ----------------------------------------------------------------------
      // In this state we decompress the FVC stream.
      // Once all the mem transfer reads have completed then move to ST_FVC_DRAIN
      ST_FVC_DECOMP: begin
        state_en   = decompressed_transfer_done;
        next_state = ST_FVC_DRAIN;

        // Check for state: compressed part is done, but pipe is empty
        if (~(mask_valid | (|inter_s2_mask_valid) | compressed.valid) & compressed_transfer_done) begin
          state_en = 1'b1;
          next_state = ST_IDLE;
          decomp_fvc_decomp_stuck = 1'b1;
        end
      end
      // ----------------------------------------------------------------------
      // ST_FVC_DRAIN
      // ----------------------------------------------------------------------
      // Once the stream fifo is emptied then move to ST_IDLE to decode the next cmd
      ST_FVC_DRAIN: begin
        state_en   = stream_done | scheme_transfer_done;
        next_state = stream_done ? ST_IDLE : ST_SCHEME;
      end
      // ----------------------------------------------------------------------
      // ST_ZRLE
      // ----------------------------------------------------------------------
      // In this state the zero stream is sent to the intf fifo.
      // Once the stream is done move to ST_IDLE to decode the next cmd
      ST_ZRLE: begin
        state_en   = stream_done | scheme_transfer_done;
        next_state = stream_done ? ST_IDLE : ST_SCHEME;
      end
      // ----------------------------------------------------------------------
      // ST_INT4
      // ----------------------------------------------------------------------
      // In this state we decompress the INT4 stream.
      // Once the stream is done move to ST_IDLE to decode the next cmd
      ST_INT4: begin
        state_en   = stream_done | scheme_transfer_done;
        next_state = stream_done ? ST_IDLE : ST_SCHEME;
      end
      // ----------------------------------------------------------------------
      // ST_NO_COMP
      // ----------------------------------------------------------------------
      // In this state the uncompressed stream is routed from the intf to the output fifo.
      // Once the stream is done move to ST_IDLE to decode the next cmd
      ST_NO_COMP: begin
        state_en   = stream_done | scheme_transfer_done;
        next_state = stream_done ? ST_IDLE : ST_SCHEME;
      end
      // ----------------------------------------------------------------------
      // ST_BYPASS
      // ----------------------------------------------------------------------
      // In this state the uncompressed stream is routed from the intf to the output fifo.
      // Once the stream is done move to ST_IDLE to decode the next cmd
      ST_BYPASS: begin
        state_en   = stream_done;
        next_state = ST_IDLE;
      end
      // ----------------------------------------------------------------------
      // DEFAULT STATE
      // ----------------------------------------------------------------------
      default: begin
        state_en   = 1'b0;
        next_state = state;
      end
    endcase
  end

  // Update state of FSM
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      state <= ST_IDLE;
    end else if (state_en) begin
      state <= next_state;
    end
  end

  // Capture the full stream transfer size
  // This will be used to generate the last bit
  assign header_update = (state == ST_HEADER) & state_en;

  assign next_stream_transfer_size = axis_m_data[0+:16];
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      stream_transfer_size <= '0;
    end else if (header_update) begin
      stream_transfer_size <= next_stream_transfer_size;
    end
  end

  // Capture sub stream scheme transfer size
  assign scheme_update = (state == ST_SCHEME) & state_en;

  assign next_uncomp_scheme_transfer_size = axis_m_data[8+:16];

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      uncomp_scheme_transfer_size <= '0;
    end else if (scheme_update) begin
      uncomp_scheme_transfer_size <= next_uncomp_scheme_transfer_size;
    end
  end

  assign next_comp_scheme_transfer_size = axis_m_data[24+:16];

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      comp_scheme_transfer_size <= '0;
    end else if (scheme_update) begin
      comp_scheme_transfer_size <= next_comp_scheme_transfer_size;
    end
  end

  // Capture sub stream compression scheme
  assign next_compression_scheme = scheme_t'(axis_m_data[1:0]);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      compression_scheme <= NO_COMP;
    end else if (scheme_update) begin
      compression_scheme <= next_compression_scheme;
    end
  end

  // Preliminary mask and data count calculation
  // This is done on the previous cycle of the actual data decoding from the buffers
  assign pre_buff_target_start = ((pre_byte_offset + 8) > DECOMP_BYTE_CNT_WRAP-1) ?  ( (pre_byte_offset + 8) - DECOMP_BYTE_CNT_WRAP) / 64 :
                                                                                     (pre_byte_offset + 8) / 64;
  assign pre_buff_target_end = (next_pre_byte_offset  == '0 ) ?  3'd4 : ((next_pre_byte_offset-1) / 64);

  assign pre_byte_offset_en= (state == ST_FVC_DRAIN)  |
                             (((state==ST_FVC_INIT) & (&buf_valid[3:0]) & (|buf_valid_en)) |
                             ((state == ST_FVC_DECOMP) & ~decompressed_transfer_done) &
                             buf_valid[pre_buff_target_start] & ~clr_buf[pre_buff_target_start] &
                             buf_valid[pre_buff_target_end] & ~clr_buf[pre_buff_target_end]) & pre_ready & ready;

  assign next_pre_byte_offset_calc = pre_byte_offset + 8 + pre_mask_count_ones;
  assign next_pre_byte_offset = (state == ST_FVC_DRAIN) ? '0 :
                                 ((next_pre_byte_offset_calc> DECOMP_BYTE_CNT_WRAP-1) ? next_pre_byte_offset_calc - DECOMP_BYTE_CNT_WRAP  :
                                                                                        next_pre_byte_offset_calc);


  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      pre_byte_offset <= '0;
    end else if (pre_byte_offset_en) begin
      pre_byte_offset <= next_pre_byte_offset;
    end
  end

  // Decode mask
  always_comb begin : _pw_sel_
    // Default values
    effective_buf_sel = effective_buf;
    unique case (pre_byte_offset[8:6])
      3'b000: effective_buf_sel = effective_buf;
      3'b001:
      effective_buf_sel = {
        {DECOMP_DW{1'b0}}, buf_data[1], buf_data[0], buf_data[4], buf_data[3], buf_data[2], buf_data[1]
      };
      3'b010:
      effective_buf_sel = {
        {2 * DECOMP_DW{1'b0}}, buf_data[1], buf_data[0], buf_data[4], buf_data[3], buf_data[2]
      };
      3'b011:
      effective_buf_sel = {{3 * DECOMP_DW{1'b0}}, buf_data[1], buf_data[0], buf_data[4], buf_data[3]};
      3'b100: effective_buf_sel = {{4 * DECOMP_DW{1'b0}}, buf_data[1], buf_data[0], buf_data[4]};
      default: effective_buf_sel = effective_buf;
    endcase
  end

  assign pre_mask_shift = effective_buf_sel >> (pre_byte_offset[5:0] * 8);
  assign pre_mask = pre_mask_shift[DECOMP_DW/8-1:0];

  // Count the amount of non-zero data from the mask
  // Slice the mask and perform the calculation of zero count in separate
  // slices in  order to improve timing
  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_pre_mask
    assign pre_mask_cnt[i] = mask_bitcount(pre_mask[i*DECOMP_SLICE_MW+:DECOMP_SLICE_MW]);
  end

  always_comb begin
    automatic int unsigned count;
    count = '0;
    for (int i = 0; i < DECOMP_NUM_SLICES; i++) begin
      count += pre_mask_cnt[i];
    end
    pre_mask_count_ones = count;
  end

  assign pre_valid = pre_byte_offset_en;

  // Pipeline register to break timing
  cc_stream_spill_reg #(
    .data_t(logic [($clog2($bits(mask) + 1) + $bits(mask) + $bits(byte_offset))-1:0])
  ) u_mask_spill_reg (
    .i_clk  (i_clk),
    .i_rst_n (i_rst_n),
    .i_valid(pre_valid),
    .i_flush(1'b0),
    .o_ready(pre_ready),
    .i_data ({pre_mask, pre_mask_count_ones, pre_byte_offset}),
    .o_valid(mask_valid),
    .i_ready(ready),
    .o_data ({mask, mask_count_ones, byte_offset})
  );

  // Valid on every cycle we remain in decompress and
  // there is data in the mask fifo
  assign valid = (state == ST_FVC_DECOMP) & mask_valid;

  // Decode data
  always_comb data_mask = (1 << (8 * mask_count_ones)) - 1;

  assign data_shift = effective_buf_q >> (byte_offset * 8 + 64);
  assign data = data_shift[DECOMP_DW-1:0] & data_mask[DECOMP_DW-1:0];

  // Count decompressed transfer cycles
  assign decompressed_transfer_cnt_set = valid & ready;
  assign decompressed_transfer_cnt_clr = (state == ST_SCHEME);
  assign decompressed_transfer_cnt_en = decompressed_transfer_cnt_set | decompressed_transfer_cnt_clr;
  assign next_decompressed_transfer_cnt = {$bits(
      decompressed_transfer_cnt
  ) {~decompressed_transfer_cnt_clr}} & (decompressed_transfer_cnt + 1);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      decompressed_transfer_cnt <= '0;
    end else if (decompressed_transfer_cnt_en) begin
      decompressed_transfer_cnt <= next_decompressed_transfer_cnt;
    end
  end
  assign decompressed_transfer_done = decompressed_transfer_cnt_en & (decompressed_transfer_cnt == uncomp_scheme_transfer_size-1);

  // Count the compressed data read
  // This is only used to stop fetching data to the buffers when we have read all the data needed for the FVC decompression
  assign compressed_transfer_cnt_set = ((state == ST_FVC_INIT) | (state== ST_FVC_DECOMP)) & axis_m_valid & axis_m_ready;
  assign compressed_transfer_cnt_clr = (state == ST_SCHEME);
  assign compressed_transfer_cnt_en = compressed_transfer_cnt_set | compressed_transfer_cnt_clr;
  assign next_compressed_transfer_cnt = {$bits(
      compressed_transfer_cnt
  ) {~compressed_transfer_cnt_clr}} & (compressed_transfer_cnt + 1);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      compressed_transfer_cnt <= '0;
    end else if (compressed_transfer_cnt_en) begin
      compressed_transfer_cnt <= next_compressed_transfer_cnt;
    end
  end
  assign compressed_transfer_done = compressed_transfer_cnt_en & (compressed_transfer_cnt == comp_scheme_transfer_size-1);

  // After all the needed PWords for the FVC decompression scheme have been fetched into the data buffers
  // disable the fetching of new PWords in this state
  assign next_buf_fetch_disable = (state == ST_SCHEME) ? 1'b0 : 1'b1;
  assign buf_fetch_disable_update = (state== ST_SCHEME) | (state == ST_FVC_DECOMP) & compressed_transfer_done;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      buf_fetch_disable <= '0;
    end else if (buf_fetch_disable_update) begin
      buf_fetch_disable <= next_buf_fetch_disable;
    end
  end

  // Data and mask are streamed in a stream register
  // ============================================================================
  //                                        stream
  //                                  valid ---|--> compressed.valid
  //                                  ready <--|--- compressed.ready
  //                                           |
  //                              mask, data --|-- compressed.mask, compressed.data

  cc_stream_reg #(
    .data_t(logic[DECOMP_MASK_BIT_WIDTH + DECOMP_DW -1 : 0])
  ) u_comp_stream_stream_reg (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_flush(1'b0),
    .i_valid(valid),
    .o_ready(ready),
    .i_data({mask, data}),
    .o_valid(compressed.valid),
    .i_ready(compressed.ready),
    .o_data({compressed.mask, compressed.data})
  );

  assign inter_s1_valid   = compressed.valid;
  assign compressed.ready = inter_s1_valid & inter_s1_ready;
  assign inter_s1_ready   = (&inter_s1_data_ready) & (&inter_s1_mask_ready);

  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_inter_s1_mask
    assign inter_s1_mask_bin[i] = compressed.mask[i*DECOMP_SLICE_MW+:DECOMP_SLICE_MW];
    assign inter_s1_mask_dec[i] = mask_bitcount(inter_s1_mask_bin[i]);
  end

  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_inter_s1_shift
    if (i == 0) begin : gen_i_is_0
      assign inter_s1_shift[i] = '0;
    end else begin : gen_i_is_not_0
      assign inter_s1_shift[i] = inter_s1_shift[i-1] + inter_s1_mask_dec[i-1];
    end
  end

  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_inter_s1_data
    // slicing data, LHS is expected to be narrow compared to RHS
    assign inter_s1_data[i] = DECOMP_SLICE_DECOMP_DW'(compressed.data >> inter_s1_shift[i] * 8);
  end

  // Data and mask are streamed in a stream register
  // ============================================================================
  //                                                 stream_reg
  //                                  inter_s1_valid ---|--> inter_s2_*_valid
  //                                inter_s1_*_ready <--|--- inter_s2_ready
  //                                                    |
  //                 inter_s1_mask_bin, inter_s1_data --|-- inter_s2_mask_bin, inter_s2_data

  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_inter_spill

    cc_stream_reg #(
      .data_t(logic[3 : 0])
    ) u_inter_mask_stream_reg (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_flush(1'b0),
      .i_valid(inter_s1_valid),
      .o_ready(inter_s1_mask_ready[i]),
      .i_data(inter_s1_mask_bin[i]),
      .o_valid(inter_s2_mask_valid[i]),
      .i_ready(inter_s2_ready),
      .o_data(inter_s2_mask_bin[i])
    );

    cc_stream_reg #(
      .data_t(logic[31 : 0])
    ) u_inter_data_spill_reg (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_flush(1'b0),
      .i_valid(inter_s1_valid),
      .o_ready(inter_s1_data_ready[i]),
      .i_data(inter_s1_data[i]),
      .o_valid(inter_s2_data_valid[i]),
      .i_ready(inter_s2_ready),
      .o_data(inter_s2_data[i])
    );

  end

  assign inter_s2_ready = decompressed.valid & decompressed.ready;

  assign decompressed.valid = (&inter_s2_data_valid) & (&inter_s2_mask_valid);

  // Data are unrolled from the mask
  // ==================================
  for (genvar i = 0; i < DECOMP_NUM_SLICES; i++) begin : gen_decomp_data
    always_comb begin
      decomp_data_word[i]  = '0;
      inter_s2_data_idx[i] = '0;
      for (int idx = 0; idx < DECOMP_SLICE_MW; idx++) begin
        if (inter_s2_mask_bin[i][idx] == '0) begin
          decomp_data_word[i][idx*8+:8] = 8'd0;
        end else begin
          decomp_data_word[i][idx*8+:8] = inter_s2_data[i][inter_s2_data_idx[i]*8+:8];
          inter_s2_data_idx[i] += 1;
        end
      end
    end
  end

  assign decompressed.data = decomp_data_word;

  // Stream transfer counter - used to generate the `last`
  // The counter is cleared every time we go back to ST_IDLE to decode a new stream
  // The counter is set every time a PW is fed into the fifo
  assign stream_transfer_cnt_set = mux_stream.valid & mux_stream.ready;
  assign stream_transfer_cnt_clr = (state == ST_IDLE);
  assign stream_transfer_cnt_en = stream_transfer_cnt_set | stream_transfer_cnt_clr;
  assign next_stream_transfer_cnt = {$bits(
      stream_transfer_cnt
  ) {~stream_transfer_cnt_clr}} & (stream_transfer_cnt + 1);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      stream_transfer_cnt <= '0;
    end else if (stream_transfer_cnt_en) begin
      stream_transfer_cnt <= next_stream_transfer_cnt;
    end
  end
  assign stream_transfer_done = stream_transfer_cnt_en & (stream_transfer_cnt == stream_transfer_size-1);


  // Scheme transfer counter - used to finish the current scheme decompression
  assign scheme_transfer_cnt_set = mux_stream.valid & mux_stream.ready;
  assign scheme_transfer_cnt_clr = (state == ST_SCHEME);
  assign scheme_transfer_cnt_en = scheme_transfer_cnt_set | scheme_transfer_cnt_clr;
  assign next_scheme_transfer_cnt = {$bits(
      scheme_transfer_cnt
  ) {~scheme_transfer_cnt_clr}} & (scheme_transfer_cnt + 1);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      scheme_transfer_cnt <= '0;
    end else if (scheme_transfer_cnt_en) begin
      scheme_transfer_cnt <= next_scheme_transfer_cnt;
    end
  end
  assign scheme_transfer_done = scheme_transfer_cnt_en & (scheme_transfer_cnt == uncomp_scheme_transfer_size-1);

  ///////////////////
  // INT4 scheme
  always_comb int4_pword_upper_d = axis_m_data[DECOMP_DW-1:(DECOMP_DW/2)];
  always_comb int4_compressed = int4_upper_q ? int4_pword_upper_q : axis_m_data[(DECOMP_DW/2)-1:0];
  always_comb begin
    // decompress word by zero extending at LSB side
    for (int unsigned i=0; i<DECOMP_PWORD_SIZE; i++)
      int4_decompresed[(i*8)+:8] = {int4_compressed[(i*4)+:4], 4'h0};

    int4_upper_en = (state == ST_INT4) ? int4.ready & int4.valid : 1'b0;
    int4_upper_d = (~int4_upper_q) & (~scheme_transfer_done); // toggle upper, or set to zero in case done

    // store upper word for INT4 when valid and not upper
    int4_pword_upper_en = (state == ST_INT4) ? int4.ready & axis_m_valid & ~int4_upper_q : 1'b0;
  end

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      int4_upper_q <= 1'b0;
      int4_pword_upper_q <= (DECOMP_DW/2)'(0);
    end else begin
      if (int4_upper_en)
        int4_upper_q <= int4_upper_d;
      if (int4_pword_upper_en)
        int4_pword_upper_q <= int4_pword_upper_d;
    end
  end
  ///////////////////

  // ZRLE: expands the command to the required number of zeros
  assign zrle.valid = 1'b1;
  assign zrle.data = '0;

  // NO COMP: no compression in this part of the stream
  assign no_comp.valid = axis_m_valid;
  assign no_comp.data = axis_m_data;

  // INT4: int4 decompression in this part of the stream
  assign int4.valid = int4_upper_q | axis_m_valid; // try to push upper part, or input
  assign int4.data = int4_decompresed;

  // Multiplex the 4 different decompression scheme streams
  assign mux_stream.valid = (state == ST_INT4) ? int4.valid : (state == ST_ZRLE) ? zrle.valid : (state == ST_NO_COMP) ? no_comp.valid : decompressed.valid;
  assign mux_stream.data  = (state == ST_INT4) ? int4.data : (state == ST_ZRLE) ? zrle.data : (state == ST_NO_COMP) ?  no_comp.data : decompressed.data;
  assign mux_stream.last = stream_transfer_done;

  assign mux_stream.ready = axis_stream.ready;
  assign decompressed.ready = axis_stream.ready;
  // assign zrle.ready = axis_stream.ready;
  // assign no_comp.ready = axis_stream.ready;
  assign int4.ready = axis_stream.ready;

  // Decompressed data are streamed in an output fifo and streamed out to the MVM
  // ===================================================================================
  //                                    [FIFO]
  //                  axis_stream.valid ---|--> axis_s_valid
  //                  axis_stream.ready <--|--- axis_s_ready
  //                                       |
  //  axis_stream.data, axis_stream.last --|-- axis_s_data, axis_s_last

  // When compression is enabled select the decompressed stream, when decompression is disabled then stream out
  // the input stream
  assign axis_stream.valid = (compression_enable == 1'b1) ? mux_stream.valid : (state == ST_BYPASS) & axis_m_valid;
  assign axis_stream.data = (compression_enable == 1'b1) ? mux_stream.data : axis_m_data;
  assign axis_stream.last = (compression_enable == 1'b1) ? mux_stream.last : axis_m_last;

  assign stream_done = axis_stream.valid & axis_stream.ready & axis_stream.last;

  cc_stream_buffer #(
    .DEPTH    (DECOMP_STREAM_FIFO_DEPTH),
    .DW       (DECOMP_DW + 1),
    .USE_MACRO(0)
  ) u_out_stream_fifo (
    .i_clk    (i_clk),
    .i_rst_n  (i_rst_n),
    .wr_vld (axis_stream.valid),
    .wr_data({axis_stream.data, axis_stream.last}),
    .wr_rdy (axis_stream.ready),
    .rd_rdy (axis_s_ready),
    .rd_data({axis_s_data, axis_s_last}),
    .rd_vld (axis_s_valid)
  );


  // State observation
  assign decomp_status = '{
          decomp_stream_done: '{d: stream_done},
          decomp_scheme_done: '{d: scheme_transfer_done},
          decomp_scheme: '{d: compression_scheme},
          decomp_fsm_state: '{d: state},
          default: '0
      };

  // Error indication
  assign decomp_invalid_stream_header = header_update & ((next_stream_transfer_size > 16'd4096) | (next_stream_transfer_size == 16'd0) |
                                                             (|axis_m_data[511:16]) );
  assign decomp_invalid_scheme_header = scheme_update & (|axis_m_data[511:40]);
  assign decomp_invalid_compressed_size = scheme_update & ((next_comp_scheme_transfer_size > 16'd4096) |
                                                             ((next_compression_scheme != ZRLE) & (next_comp_scheme_transfer_size == 16'd0)));
  assign decomp_invalid_uncompressed_size = scheme_update & ((next_uncomp_scheme_transfer_size > 16'd4096) | (next_uncomp_scheme_transfer_size == 16'd0));

  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON
  `include "sva/assertions.svh"
  `endif  // ASSERTIONS_ON
  `endif

endmodule


`endif  // DECOMPRESS_SV
