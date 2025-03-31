// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Vectorized Transpose module that implements the function B=transpose(A),
//              where both A and B are square matrices containing PWord**2 8-bit elements/words
//
//              Added support for FP16 band FP32 modes where the element size is increased from
//              8bits to 16bits and 32 bits respectively.
//
//              Removed support for dual buffer setup since buffer size is VERY HIGH.

// Owner: Abhishek Maringanti <abhishek.maringanti@axelera.ai>
//        Sander Geursen <sander.geursen@axelera.ai>

`ifndef _VTRSP_SV_
`define _VTRSP_SV_

module vtrsp
#(
  parameter int unsigned PWORD_LEN = 64,
  parameter int unsigned DW = 512,
  parameter int unsigned CMD_DW = 2,
  parameter type status_t = logic
) (
  // Clocks and Reset Signals
  input wire i_clk,
  input wire i_rst_n,
  input logic i_scan_en,

  // AXI-Stream Subordinate Interface (incoming data intf)
  input logic axis_s_tvalid,
  input logic [DW-1:0] axis_s_tdata,
  input logic axis_s_tlast,

  output logic axis_s_tready,

  // AXI-S Subordinate Interface for command (incoming cmd intf)
  input logic cmd_valid,
  input logic [CMD_DW-1:0] cmd_data,

  output logic cmd_ready,

  // AXI-Stream Manager Interface (outgoing data intf)
  input logic axis_m_tready,

  output logic axis_m_tvalid,
  output logic [DW-1:0] axis_m_tdata,
  output logic axis_m_tlast,

  // Interrupts
  output logic vtrsp_irq,

  // Status bus from VTRSP module to be captured in a CSR
  output status_t vtrsp_status
);

  // **************** PARAMETER DEFINITONS *************** //

  localparam int unsigned VtrspCmdDepth = 4;
  // FSM paramters
  typedef enum logic [2:0] {
    Idle          = 3'd0,
    BypMode       = 3'd1,
    FillBuf       = 3'd2,
    WaitBufEmpty  = 3'd3,
    WaitCmd       = 3'd4,
    Error         = 3'd5
  } fill_states_e;
  localparam int unsigned CntrWidth = $clog2(PWORD_LEN);

  // **************** INTERNAL VARIABLES *************** //

  // FSMs to track the sampling of data into the two buffers.
  logic [2:0] curr_fill_state;
  logic [2:0] nxt_fill_state;

  // internal command signals
  logic cmd_valid_int;
  logic [CMD_DW-1:0] cmd_data_int;  // bit 0 - mode (byp/transpose),
                                    // bits [2:1] - 00 FP 8 (Default)
                                    // bits [2:1] - 01 FP 16
                                    // bits [2:1] - 10 FP 32
  logic cmd_ready_int;

  // Control signals to know the status of the buffers
  logic [CntrWidth:0] buf_cntr_wr_q, buf_cntr_wr_d;  // increments everytime the buffer is filled or drained
  logic [CntrWidth:0] buf_cntr_rd_q, buf_cntr_rd_d;  // increments everytime the buffer is filled or drained
  logic buf_almost_full; // Buffer almost full
  logic buf_almost_empty; // Buffer almost empty
  logic buf_can_fill; // Signal that indicates when the buffer can fill
  logic buf_can_drn; // Signal that indicates when the buffer can drain
  logic buf_empty;  // Signal to indicate when the buffer is empty

  logic axis_s_tvalid_buf; // internal valid signal that is asserted when data sent out on AXI-S from a buffer is valid
  logic [DW-1:0] axis_s_tdata_buf_int; // internal data from buffer that needs to be sent on the AXI-S interface
  logic [DW-1:0] axis_s_tdata_buf; // internal data from buffer that needs to be sent on the AXI-S interface
  logic [DW-1:0] axis_s_tdata_reg;  // storing input data to facilitate FP mode duplicate writes
  logic [DW-1:0] axis_s_tdata_fp;  // shifted data written into buffer when fp mode = 16/32.
  logic axis_s_tlast_buf; // internal last signal that is asserted for the last valid data from the buffer.
  logic axis_s_tready_buf; // internal ready signal from buffer that is asserted when a buffer can accept data.
  logic axis_m_tlast_buf; // This signal is used to track when tlast should be asserted for the output AXI Stream
  logic sample_inp_data;  // (vld & rdy) implying data should be sampled.
  logic sample_inp_data_fp_mode;  // duplicate data should be stored in the buffer.
  logic err_buf;
  logic sample_inp_cmd;  // (vld & rdy) implying cmd should be sampled.

  vtrsp_pkg::vtrsp_fill_drain_connection_e fill_connection;
  vtrsp_pkg::vtrsp_fill_drain_connection_e drain_connection;
  vtrsp_pkg::vtrsp_cmd_mode_e vtrsp_mode_fill_d, vtrsp_mode_fill_q;
  vtrsp_pkg::vtrsp_cmd_mode_e vtrsp_mode_drn_q;
  logic vtrsp_mode_drn_en;

  // **************** CODE *************** //

  if (VtrspCmdDepth == 0) begin : g_no_cmd_fifo
    always_comb cmd_valid_int = cmd_valid;
    always_comb cmd_data_int  = cmd_data;
    always_comb cmd_ready     = cmd_ready_int;
  end else begin : g_cmd_fifo
    // A fifo is used to store any incoming commands from the higher entity.
    cc_stream_buffer #(
      .DEPTH(VtrspCmdDepth),
      .DW(CMD_DW)
    ) u_vtrsp_cmd_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      // interface to top
      .wr_vld (cmd_valid),
      .wr_data(cmd_data),
      .wr_rdy (cmd_ready),

      // interface to internal buffers
      .rd_rdy (cmd_ready_int),
      .rd_data(cmd_data_int),
      .rd_vld (cmd_valid_int)
    );
  end
  always_comb vtrsp_mode_fill_d = vtrsp_pkg::vtrsp_cmd_mode_e'(cmd_data_int);

  // FSM state assignments
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      curr_fill_state <= Idle;
    end else begin
      curr_fill_state <= nxt_fill_state;
    end
  end

  always_comb sample_inp_cmd = cmd_valid_int & cmd_ready_int;
  // FP Mode (element size)
  // FP mode signals are used to do duplicate writes in FP 16/32 mode.
  // Sample and retain fp_mode signals when the cmd_data is valid.
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      vtrsp_mode_fill_q  <= vtrsp_pkg::bypass_mode;
      vtrsp_mode_drn_q   <= vtrsp_pkg::bypass_mode;
    end else begin
      if (sample_inp_cmd)
        vtrsp_mode_fill_q <= vtrsp_mode_fill_d;
      if (vtrsp_mode_drn_en)
        vtrsp_mode_drn_q <= vtrsp_mode_fill_q;
    end
  end
  // set vtrsp mode for the drain when filling up the last item of the buffer
  always_comb vtrsp_mode_drn_en = buf_almost_full & sample_inp_data;

  // assignment for the current states of the two state machines.
  // FSM for the filling of the buffers with data from the AXI-S in transpose mode
  // Idle state also represents a wait for command state. The command is checked in the idle state and
  // the FSM moves to either BypMode state or the FillBuf state.
  // WaitCmd state is used when waiting for the next command in transpose mode. If the new command is
  // transpose mode then move to the FillBufx state of the buffer that is empty. If the new command is
  // bypass mode then wait for the current transfer to complete (both buffers empty) before switching to BYP-MODE.
  // cmd_ready_int is generated such that it is active only when buffers can accept data or in Idle state.
  always_comb begin
    nxt_fill_state = curr_fill_state;
    cmd_ready_int = 1'b0;
    unique case (curr_fill_state)
      Idle: begin
        cmd_ready_int = 1'b1;
        if (sample_inp_cmd) begin
          if (|cmd_data_int)
            nxt_fill_state = FillBuf;
          else nxt_fill_state = WaitBufEmpty;
        end
      end

      BypMode: begin
        if (axis_s_tvalid & axis_s_tready & axis_s_tlast) nxt_fill_state = Idle;
      end

      FillBuf: begin
        if (buf_almost_full & axis_s_tlast & sample_inp_data)  // if buf is almost full (last data pending) and the last data is received
                                                                // then move to WaitCmd state
          nxt_fill_state = WaitCmd;
        else if (~buf_almost_full & axis_s_tlast & sample_inp_data) // if incoming data is not a "page" size
          nxt_fill_state = Error;  // if buf is not almost full (last data pending) and the last data is received implying that
                                      // the input is not a page size (fp8: 64 rows, fp16: 32 rows, fp32: 16 rows)
      end

      WaitCmd: begin  // Wait for the next command.
        cmd_ready_int = 1'b1;
        if (sample_inp_cmd) begin
          if (|cmd_data_int) // if transpose mode
            nxt_fill_state = FillBuf;
          else
            nxt_fill_state = WaitBufEmpty;
        end else if (buf_empty) nxt_fill_state = Idle; // buffer is empty => move to idlde
      end

      WaitBufEmpty: begin     // This state is to wait for the buffer to become empty before switching to BypMode to process the next cmd.
        if (buf_empty) nxt_fill_state = BypMode;
      end

      Error: begin  // Stay in Error state for 1 full cycle and proceed to WaitCmd state for next command
        nxt_fill_state = WaitCmd;
      end

      default: begin
        nxt_fill_state = Idle;
      end
    endcase
  end

  always_comb err_buf = ((curr_fill_state == FillBuf) & (nxt_fill_state == Error));

  always_comb fill_connection  = vtrsp_pkg::vtrsp_fill_drain_connection_e'(buf_cntr_wr_q[CntrWidth]);
  always_comb drain_connection = vtrsp_pkg::vtrsp_fill_drain_connection_e'(~buf_cntr_rd_q[CntrWidth]); // drain transposed way

  // The buffer can be drained when filling and draining is stated as the same.
  // That means the buffer is filled up and needs draining to be able to continue filling.
  // The buffer is empty when filling and draining are in same mode and counters are 0.
  always_comb begin
    buf_can_drn  = fill_connection == drain_connection;
    buf_empty    = (fill_connection ^ drain_connection) && (buf_cntr_rd_q[CntrWidth-1:0] == 0 && buf_cntr_wr_q[CntrWidth-1:0] == 0);

    unique case (vtrsp_mode_fill_q)
      vtrsp_pkg::fp8_mode: begin
        buf_almost_full   = buf_cntr_wr_q[CntrWidth-1:0] == (PWORD_LEN - 1);

        // can fill either when not in the draining mode, or when there is enough space:
        buf_can_fill      =  (~buf_can_drn) | ((buf_cntr_rd_q[CntrWidth-1:0] - buf_cntr_wr_q[CntrWidth-1:0]) > 0);
      end
      vtrsp_pkg::fp16_mode: begin
        buf_almost_full   = buf_cntr_wr_q[CntrWidth-1:0] == (PWORD_LEN - 2);

        // can fill either when not in the draining mode, or when there is enough space:
        buf_can_fill      =  (~buf_can_drn) | ((buf_cntr_rd_q[CntrWidth-1:0] - buf_cntr_wr_q[CntrWidth-1:0]) > 1);
      end
      vtrsp_pkg::fp32_mode: begin
        buf_almost_full   = buf_cntr_wr_q[CntrWidth-1:0] == (PWORD_LEN - 4);

        // can fill either when not in the draining mode, or when there is enough space:
        buf_can_fill      =  (~buf_can_drn) | ((buf_cntr_rd_q[CntrWidth-1:0] - buf_cntr_wr_q[CntrWidth-1:0]) > 3);
      end
      default: begin // bypass
        buf_almost_full   = 1'b0;
        buf_can_fill      = 1'b0;
      end
    endcase

    unique case (vtrsp_mode_drn_q)
      vtrsp_pkg::fp8_mode: begin
        buf_almost_empty  = buf_cntr_rd_q[CntrWidth-1:0] == (PWORD_LEN - 1);
      end
      vtrsp_pkg::fp16_mode: begin
        buf_almost_empty  = buf_cntr_rd_q[CntrWidth-1:0] == (PWORD_LEN - 2);
      end
      vtrsp_pkg::fp32_mode: begin
        buf_almost_empty  = buf_cntr_rd_q[CntrWidth-1:0] == (PWORD_LEN - 4);
      end
      default: begin // bypass
        buf_almost_empty  = 1'b0;
      end
    endcase
  end

  // counter increments when the buffer is being filled or drained.
  always_comb begin
    case (vtrsp_mode_fill_q)
      vtrsp_pkg::fp8_mode:  buf_cntr_wr_d = buf_cntr_wr_q + 1;
      vtrsp_pkg::fp16_mode: buf_cntr_wr_d = buf_cntr_wr_q + 2;
      vtrsp_pkg::fp32_mode: buf_cntr_wr_d = buf_cntr_wr_q + 4;
      default: buf_cntr_wr_d = buf_cntr_wr_q;
    endcase
  end
  always_comb begin
    case (vtrsp_mode_drn_q)
      vtrsp_pkg::fp8_mode:  buf_cntr_rd_d = buf_cntr_rd_q + 1;
      vtrsp_pkg::fp16_mode: buf_cntr_rd_d = buf_cntr_rd_q + 2;
      vtrsp_pkg::fp32_mode: buf_cntr_rd_d = buf_cntr_rd_q + 4;
      default: buf_cntr_rd_d = buf_cntr_rd_q;
    endcase
  end
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      buf_cntr_wr_q <= 'd0;
      buf_cntr_rd_q <= 'd0;
    end else begin
      if (err_buf) begin
        buf_cntr_wr_q <= '0;
        buf_cntr_rd_q <=  buf_cntr_wr_q;
      end else begin
        if (buf_can_fill & axis_s_tvalid & axis_s_tready)
          buf_cntr_wr_q <= buf_cntr_wr_d;

        if (buf_can_drn & axis_m_tvalid & axis_m_tready)
            buf_cntr_rd_q <= buf_cntr_rd_d;
      end
    end
  end

  // Accepting incoming AXI-S data into the buffers.
  // Determining if the system should be in transpose mode or bypass mode depends on the incoming command and the fill state of the buffers
  always_comb begin
    unique case (curr_fill_state)
      Idle: begin
        axis_m_tvalid = 1'b0;
        axis_m_tdata  = 'd0;
        axis_m_tlast  = 'd0;
        axis_s_tready = 1'b0;
      end

      BypMode: begin
        axis_m_tvalid = axis_s_tvalid;
        axis_m_tdata  = axis_s_tdata;
        axis_m_tlast  = axis_s_tlast;
        axis_s_tready = axis_m_tready;
      end

      FillBuf, WaitCmd, WaitBufEmpty, Error: begin
        axis_m_tvalid = axis_s_tvalid_buf;
        axis_m_tdata  = axis_s_tdata_buf_int;
        axis_m_tlast  = axis_s_tlast_buf;
        axis_s_tready = axis_s_tready_buf;
      end

      default: begin
        axis_m_tvalid = 1'b0;
        axis_m_tdata  = 'd0;
        axis_m_tlast  = 'd0;
        axis_s_tready = 1'b0;
      end

    endcase
  end

  logic [PWORD_LEN-1:0] inp_row_en_buf;
  logic [PWORD_LEN-1:0] outp_col_en_buf;
  always_comb sample_inp_data = axis_s_tvalid & axis_s_tready_buf;

  always_comb begin
    logic [3:0] row_en;
    unique case (vtrsp_mode_fill_q)
      vtrsp_pkg::fp8_mode:  row_en = 4'b0001;
      vtrsp_pkg::fp16_mode: row_en = 4'b0011;
      vtrsp_pkg::fp32_mode: row_en = 4'b1111;
      default: row_en = '0;
    endcase
    inp_row_en_buf = '0;
    if (((curr_fill_state == FillBuf) & buf_can_fill) & sample_inp_data)
      inp_row_en_buf = PWORD_LEN'(row_en << buf_cntr_wr_q[CntrWidth-1:0]);
    else
      inp_row_en_buf = 'd0;
  end

  // output draining is same in all FP modes.
  // Note: when draining the buffer, the counter increments are dependent on FP mode:
  // FP8: +1, FP16: +2, FP32: +4.
  always_comb begin
    logic [3:0] col_en;
    unique case (vtrsp_mode_drn_q)
      vtrsp_pkg::fp8_mode:  col_en = 4'b0001;
      vtrsp_pkg::fp16_mode: col_en = 4'b0011;
      vtrsp_pkg::fp32_mode: col_en = 4'b1111;
      default: col_en = '0;
    endcase
    outp_col_en_buf = '0;
    if (buf_can_drn)
      outp_col_en_buf = PWORD_LEN'(col_en << buf_cntr_rd_q[CntrWidth-1:0]);
    else
      outp_col_en_buf = '0;
  end

  always_comb begin
    if (vtrsp_mode_fill_q == vtrsp_pkg::bypass_mode)
      axis_s_tdata_fp = '0;
    else
      axis_s_tdata_fp = axis_s_tdata;
  end

  wire buffer_clk;
  logic buffer_clk_en;

  always_comb buffer_clk_en = ((curr_fill_state == Idle) || (curr_fill_state == BypMode)) ? 1'b0 : 1'b1;
  axe_tcl_clk_gating u_clk_gate (
    .i_clk,
    .i_en     (buffer_clk_en),
    .i_test_en(i_scan_en),
    .o_clk    (buffer_clk)
  );

  vtrsp_transpose_buffer #(
    .EL_SIZE(DW / PWORD_LEN),  // Element Size = data size
    .NR_EL  (PWORD_LEN)        // number of rows of elements = PWORD_LEN
  ) u_trsp_buf_data (
    .i_clk  (buffer_clk),
    .i_rst_n(i_rst_n),

    .i_fill_connection(fill_connection),
    .i_drain_connection(drain_connection),

    .i_fill_cmd_mode(vtrsp_mode_fill_q),
    .i_drain_cmd_mode(vtrsp_mode_drn_q),

    .i_inp_dat  (axis_s_tdata_fp),
    .i_inp_en   (inp_row_en_buf),

    .o_outp_dat (axis_s_tdata_buf),
    .i_outp_en  (outp_col_en_buf)

  );

  always_comb axis_s_tdata_buf_int = axis_s_tdata_buf;
  always_comb axis_s_tvalid_buf = buf_can_drn;

  // axis_m_tlast should be asserted only for the last packet of the stream and not every packet.
  // The tlast_bufx signals are used to track the tlast from the input stream.
  logic tlast_buf_en, tlast_buf_d;
  always_comb begin
    tlast_buf_d = 1'b1;
    tlast_buf_en = 1'b0;

    if (err_buf)
      tlast_buf_en = 1'b1;
    else begin
      if ((curr_fill_state == FillBuf) & axis_s_tlast)
        tlast_buf_en = 1'b1;

      if (buf_can_drn & axis_m_tlast & axis_m_tvalid & axis_m_tready) begin
        tlast_buf_en = 1'b1;
        tlast_buf_d  = 1'b0;
      end
    end
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n) begin
      axis_m_tlast_buf <= 1'b0;
    end else begin
      if (tlast_buf_en) axis_m_tlast_buf <= tlast_buf_d;
    end
  end

  always_comb axis_s_tlast_buf = axis_s_tvalid_buf & buf_almost_empty & axis_m_tlast_buf;

  // assert axis_s_tready_buf when the buffer can accept data from the incoming AXI-S stream.
  // axis_s_tready_buf is used only in transpose mode.
  always_comb axis_s_tready_buf = buf_can_fill && (curr_fill_state == FillBuf || curr_fill_state == BypMode);

  always_comb vtrsp_irq = (curr_fill_state == Error);

  // State observation
  always_comb vtrsp_status = '{
          vtrsp_fill_state: '{d: curr_fill_state},
          vtrsp_drain_state: '{d: 0},
          vtrsp_in_lst: '{d: axis_s_tlast},
          vtrsp_in_rdy: '{d: axis_s_tready},
          vtrsp_in_vld: '{d: axis_s_tvalid},
          vtrsp_out_lst: '{d: axis_m_tlast},
          vtrsp_out_rdy: '{d: axis_m_tready},
          vtrsp_out_vld: '{d: axis_m_tvalid},
          vtrsp_cmd_lst: '{d: 1'b0},
          vtrsp_cmd_rdy: '{d: cmd_ready_int},
          vtrsp_cmd_vld: '{d: cmd_valid_int},
          default: 'd0
      };
endmodule

`endif
