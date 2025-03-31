// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger ext move, moves the data out
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module timestamp_logger_ext_move #(
    parameter int unsigned MemWidth = 64,
    parameter int unsigned MemDepth = 16,
    parameter int unsigned AxiAddrWidth = 40,
    parameter int unsigned AxiDataWidth = 64,

    localparam int unsigned MemAddrW = $clog2(MemDepth),
    localparam type axi_addr_t = logic[AxiAddrWidth    -1:0],
    localparam type axi_data_t = logic[AxiDataWidth    -1:0],
    localparam type axi_strb_t = logic[(AxiDataWidth/8)-1:0]
  ) (
  input  wire  i_clk,
  input  wire  i_rst_n,

  timestamp_logger_csr_reg_pkg::timestamp_logger_csr_reg2hw_t   i_csr_reg2hw,

  input  logic                i_capture_en,
  output logic                o_hit_end_log,
  input  logic                i_writing_to_buf, // still writing to buffer, don't drain just yet

  // info about the buffer fillness:
  input  logic [MemAddrW:0]   i_entries_in_mem,
  output logic                o_entries_in_mem_sub,
  output logic                o_entries_in_mem_rd,

  // local memory access:
  output logic                o_mem_req_valid,
  input  logic                i_mem_req_ready,
  output logic [MemAddrW-1:0] o_mem_req_addr_row,
  input  logic                i_mem_rsp_valid,
  output logic                o_mem_rsp_ready,
  input  logic [MemWidth-1:0] i_mem_rsp_data,

  // external access:
  output logic                o_axi_m_aw_valid,
  input  logic                i_axi_m_aw_ready,
  output axi_addr_t           o_axi_m_aw_addr,
  output axi_pkg::axi_len_t   o_axi_m_aw_len,
  output axi_pkg::axi_size_t  o_axi_m_aw_size,
  output axi_pkg::axi_burst_t o_axi_m_aw_burst,

  // Write  Data Channel
  output axi_data_t           o_axi_m_w_data,
  output axi_strb_t           o_axi_m_w_strb,
  output logic                o_axi_m_w_last,
  output logic                o_axi_m_w_valid,
  input  logic                i_axi_m_w_ready,
  // Write Response Channel
  input  axi_pkg::axi_resp_t  i_axi_m_b_resp,
  input  logic                i_axi_m_b_valid,
  output logic                o_axi_m_b_ready,

  // some sort of debug / irq:
  output logic                o_bus_error
);

  typedef enum logic[2:0] {
    s_idle = 0, // nothing happened yet, configuration will be fixed after capture_en
    s_wait = 1, // wait for enough items, if reached send address
    s_move = 2, // send out memory read requests. Returned data will be wired out
    s_stop = 3, // stop, end log reached and drop is enabled
    s_drain_chk  = 4, // check if there is something left to drain, of so send address
    s_drain_move = 5  // send out memory read requests. Return data will be wired out
  } ext_move_state_e;
  ext_move_state_e state, state_nxt;
  logic state_en;

  typedef struct packed {
    axi_addr_t  st_addr;
    axi_addr_t  size;
    logic [2:0] len_coded;
  } cfg_t;
  cfg_t cfg_d, cfg_q;
  logic cfg_en;

  axi_addr_t cur_addr_d, cur_addr_q, cur_addr_incr;
  logic cur_addr_en;

  axi_pkg::axi_len_t burst_len;
  axi_pkg::axi_len_t burst_len_drain;

  axi_pkg::axi_len_t rd_len_d, rd_len_q;
  logic rd_len_decr, rd_len_en;

  logic [MemAddrW-1:0] rd_addr_d, rd_addr_q;
  logic rd_addr_en;

  logic mem_req_snd;

  always_comb mem_req_snd = (o_mem_req_valid & i_mem_req_ready);

  always_comb cfg_d = cfg_t'{
                      st_addr: {i_csr_reg2hw.st_addr[AxiAddrWidth-1:timestamp_logger_pkg::TimeLogAlignWidth], timestamp_logger_pkg::TimeLogAlignWidth'(0)},
                      size   : {i_csr_reg2hw.log_size[AxiAddrWidth-1:timestamp_logger_pkg::TimeLogAlignWidth], timestamp_logger_pkg::TimeLogAlignWidth'(0)},
                      len_coded : i_csr_reg2hw.burst_size
                    };

  always_comb burst_len = axi_pkg::axi_len_t'(1) << cfg_q.len_coded;

  always_comb rd_len_d = (cur_addr_en ? burst_len_drain : rd_len_q) - axi_pkg::axi_len_t'(mem_req_snd);
  always_comb rd_len_en = cur_addr_en | mem_req_snd;
  always_comb o_entries_in_mem_rd = mem_req_snd;

  always_comb begin
    rd_addr_en = cfg_en | mem_req_snd;
    rd_addr_d = rd_addr_q + 1;
    if (cfg_en || (rd_addr_q == MemDepth-1)) // starting over, reset to 0
      rd_addr_d = MemAddrW'(0);
  end

  logic addr_hit_end, addr_hit_end_q;
  logic hit_end_log_pre;
  logic hit_end_log;
  always_comb cur_addr_incr = cur_addr_q + {burst_len, ($clog2(AxiDataWidth/8))'(0)};
  // Check if end address is reached:
  always_comb addr_hit_end     =  (cur_addr_incr == cfg_q.st_addr + cfg_q.size);
  always_comb hit_end_log     = i_csr_reg2hw.ctrl.trace_mode.q ? 1'b0 : addr_hit_end_q;
  always_comb hit_end_log_pre = i_csr_reg2hw.ctrl.trace_mode.q ? 1'b0 : addr_hit_end & cur_addr_en;
  always_comb o_hit_end_log = hit_end_log_pre | hit_end_log;

  always_comb begin
    state_nxt = state; // default
    cfg_en    = 1'b0;
    cur_addr_en = 1'b0;
    o_axi_m_aw_valid = 1'b0;
    cur_addr_d = addr_hit_end ? cfg_q.st_addr : cur_addr_incr; // default next address is current + burst_len in bytes
    burst_len_drain = burst_len; // only for last drain it should be overwritten
    o_mem_req_valid = 1'b0;

    unique case (state)
      s_idle: begin
        if (i_capture_en & i_csr_reg2hw.ctrl.external_mode.q) begin
          state_nxt = s_wait;
          cfg_en    = 1'b1;
          cur_addr_en = 1'b1;
          cur_addr_d  = cfg_d.st_addr;
        end
      end

      s_wait: begin
        if (hit_end_log)
          state_nxt = s_stop;
        if ((!i_capture_en) && (!i_writing_to_buf))
          state_nxt = s_drain_chk;
        else if (i_entries_in_mem >= burst_len) begin
          o_axi_m_aw_valid = 1'b1;
          if (i_axi_m_aw_ready) begin
            state_nxt = s_move;
            cur_addr_en = 1'b1;
            o_mem_req_valid = 1'b1;
          end
        end
      end

      s_move: begin
        if (rd_len_q == 0)
          state_nxt = s_wait;
        else begin
          o_mem_req_valid = 1'b1;
        end
      end

      s_drain_chk: begin
        if (i_entries_in_mem == 0)
          state_nxt = s_idle;
        else if (hit_end_log)
          state_nxt = s_stop;
        else begin
          o_axi_m_aw_valid = 1'b1;
          if (i_axi_m_aw_ready) begin
            state_nxt = s_drain_move;
            cur_addr_en = 1'b1;
            o_mem_req_valid = 1'b1;
          end
        end

        // if there is no full burst available then the len should be whatever is left
        if (i_entries_in_mem < burst_len)
          burst_len_drain = i_entries_in_mem;

      end

      s_drain_move: begin
        if (rd_len_q == 0)
          state_nxt = s_drain_chk;
        else begin
          o_mem_req_valid = 1'b1;
        end
      end

      s_stop: begin
        if (i_capture_en == 0)
          state_nxt = s_idle;
      end

      default: begin // should never happen
        state_nxt = s_idle;
        state_en  = 1'b1;
      end
    endcase
  end

  // Registers:
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      state       <= s_idle;
      cfg_q       <= '{default:0};
      cur_addr_q  <= '0;
      rd_len_q    <= '0;
      rd_addr_q   <= '0;
      addr_hit_end_q <= '0;
    end else begin
      if (state_nxt != state)
        state       <= state_nxt;
      if (cfg_en)
        cfg_q       <= cfg_d;
      if (cur_addr_en) begin
        cur_addr_q     <= cur_addr_d;
        addr_hit_end_q <= addr_hit_end & (~cfg_en); // clear when writing new config
      end
      if (rd_len_en)
        rd_len_q    <= rd_len_d;
      if (rd_addr_en)
        rd_addr_q   <= rd_addr_d;
    end
  end

  logic last_d;
  always_comb last_d = (rd_len_d == 0) ? 1'b1 : 1'b0;
  cc_stream_buffer #(
    .DEPTH(4),
    .DW(1)
  ) i_exp_resp_fifo (
    .i_clk  ,
    .i_rst_n,

    .wr_vld (mem_req_snd),
    .wr_data(last_d),
    .wr_rdy (), // ASO-UNUSED_OUTPUT: port not used

    .rd_rdy (i_axi_m_w_ready & o_axi_m_w_valid),
    .rd_data(o_axi_m_w_last),
    .rd_vld () // ASO-UNUSED_OUTPUT: port not used
  );

  always_comb o_entries_in_mem_sub = i_mem_rsp_valid & o_mem_rsp_ready;
  always_comb o_mem_req_addr_row   = rd_addr_q;

  always_comb o_axi_m_aw_burst = axi_pkg::AXI_BURST_INCR;
  always_comb o_axi_m_w_strb   = {$bits(axi_strb_t){1'b1}};
  always_comb o_axi_m_aw_addr  = cur_addr_q;
  always_comb o_axi_m_aw_size  = $clog2(AxiDataWidth/8);
  always_comb o_axi_m_aw_len   = ((state == s_drain_chk || state == s_drain_move) ? burst_len_drain : burst_len) - 1;

  // handle write response, only check for error:
  always_comb o_axi_m_b_ready  = 1'b1;
  always_comb o_bus_error      = i_axi_m_b_valid & |i_axi_m_b_resp;

  // wire through the memory response to AXI:
  always_comb o_axi_m_w_data   = i_mem_rsp_data;
  always_comb o_axi_m_w_valid  = i_mem_rsp_valid;
  always_comb o_mem_rsp_ready  = i_axi_m_w_ready;

endmodule

