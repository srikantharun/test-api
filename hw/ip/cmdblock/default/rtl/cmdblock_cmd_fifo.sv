// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of CMDBlock
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_CMD_FIFO_SV_
`define _CMDBLOCK_CMD_FIFO_SV_

module cmdblock_cmd_fifo #(
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64,
  parameter int unsigned OUT_DW = 10,
  parameter int unsigned BW = 6,

  parameter int unsigned NR_FORMATS = 1,
  parameter int unsigned FORMAT_FIELD_IDX = 0,
  /// Number of bytes per format. This value reflects the size that will be written via the AXI port for all fields combined,
  /// not what is packed into the internal fifo or pushed out as command. Different sizes have an effect on the last field,
  /// others are assumed to be stable across the fields.
  parameter int unsigned FORMAT_NR_BYTES[NR_FORMATS] = {(OUT_DW + 7) / 8},

  /// Number of fields
  parameter int unsigned NR_FIELDS = 3,
  /// LSB of the field in the written data
  parameter int unsigned FIELD_LSB_IDX[NR_FIELDS] = {32'd0, 32'd32, 32'd64},
  /// Width of the field
  parameter int unsigned FIELD_SIZE[NR_FIELDS] = {32'd16, 32'd8, 32'd111},
  /// Depth of the FIFO
  parameter int unsigned CMD_FIFO_DEPTH = 4,
  /// Width of the FIFO. Default is the required width (OUT_DW + log2(formats)). When set smaller the CMD FIFO will pre and post pack.
  /// This allows to have more commands in the FIFO with a smaller format size, while still supporting wide formats
  parameter int unsigned CMD_FIFO_WIDTH = (OUT_DW + $clog2(NR_FORMATS)),
  parameter int unsigned USE_MACRO = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  ///// Sideband:
  input wire exec,
  input wire pointer_rst,
  output wire [7:0] cur_pointer,
  output wire [7:0] cur_fifo_count,
  output logic cmd_dropped,

  ///// AXI slave:
  // Write Address Channel
  input  wire [ IDW-1:0] awid,
  input  wire [  AW-1:0] awaddr,
  input  wire [  BW-1:0] awlen,
  input  wire [     2:0] awsize,
  input  wire [     1:0] awburst,
  // input  wire [  MT_LW-1:0] awlock,
  // input  wire [        3:0] awcache,
  // input  wire [       2:0] awprot,
  input  wire            awvalid,
  output wire            awready,
  // Read Address Channel
  input  wire [ IDW-1:0] arid,
  input  wire [  AW-1:0] araddr,
  input  wire [  BW-1:0] arlen,
  input  wire [     2:0] arsize,
  input  wire [     1:0] arburst,
  // input  wire [  MT_LW-1:0] arlock,
  // input  wire [        3:0] arcache,
  // input  wire [       2:0] arprot,
  input  wire            arvalid,
  output wire            arready,
  // Write  Data Channel
  input  wire [  DW-1:0] wdata,
  input  wire [DW/8-1:0] wstrb,
  input  wire            wlast,
  input  wire            wvalid,
  output wire            wready,
  // Read Data Channel
  output wire [ IDW-1:0] rid,
  output wire [  DW-1:0] rdata,
  output wire [     1:0] rresp,
  output wire            rlast,
  output wire            rvalid,
  input  wire            rready,
  // Write Response Channel
  output wire [ IDW-1:0] bid,
  output wire [     1:0] bresp,
  output wire            bvalid,
  input  wire            bready,

  ////// Output:
  output wire [OUT_DW-1:0] cmd_data,
  output wire [cc_math_pkg::index_width(NR_FORMATS)-1:0] cmd_format,
  output wire cmd_vld,
  input wire cmd_rdy
);

  ////////////////////////////////////////////////
  ///// supporting functions and parameters, expanding simple array into mappable settings
  typedef int unsigned int_da_fields_t[NR_FIELDS];

  // get the number of registers required per field:
  function automatic int_da_fields_t nr_regs_per_field();
    for (int unsigned f = 0; f < NR_FIELDS; f++) begin
      if (FIELD_SIZE[f] == 0) nr_regs_per_field[f] = 0;
      else nr_regs_per_field[f] = (FIELD_SIZE[f] + (FIELD_LSB_IDX[f] % DW) + (DW - 1)) / DW;
    end
  endfunction

  localparam int_da_fields_t NrRegsPField  = nr_regs_per_field();

  // get the first register idx of a required field:
  function automatic int unsigned field_reg0_idx(int unsigned field);
    int unsigned t;
    t = 0;
    for (int unsigned f = 0; f < field; f++) begin
      t = t + NrRegsPField [f];
    end
    field_reg0_idx = t;
  endfunction

  // get the total number of required registers:
  function automatic int unsigned nr_regs();
    int unsigned t;
    t = 0;
    foreach (NrRegsPField [f]) begin
      t = t + NrRegsPField [f];
    end
    nr_regs = t;
  endfunction

  localparam int unsigned NrRegs = nr_regs();

  // a function to get the width of a register:
  // spyglass disable_block ImproperRangeIndex-ML
  function automatic int unsigned reg_w(int unsigned field, int unsigned reg_idx);
    if (reg_idx == 0)
      reg_w = (FIELD_SIZE[field] < DW-(FIELD_LSB_IDX[field]%DW)) ? FIELD_SIZE[field] : (DW-(FIELD_LSB_IDX[field]%DW));
    else if (reg_idx == (NrRegsPField [field] - 1)) begin
      reg_w = (FIELD_SIZE[field] + FIELD_LSB_IDX[field]) % DW;
      if (reg_w == 0) reg_w = DW;
    end else reg_w = DW;
  endfunction
  // spyglass enable_block ImproperRangeIndex-ML

  typedef int unsigned int_da_regs_t[NrRegs];

  // get the width of each register:
  function automatic int_da_regs_t reg_widths();
    int unsigned r_i;
    r_i = 0;
    for (int unsigned f = 0; f < NR_FIELDS; f++) begin
      // spyglass disable_block STARC05-2.9.1.2b
      // it's a function and the end value is static as it's a parameter
      for (int unsigned r = 0; r < NrRegsPField [f]; r++) begin
        reg_widths[r_i] = reg_w(f, r);
        r_i++;
      end
      // spyglass enable_block STARC05-2.9.1.2b
    end
  endfunction
  localparam int_da_regs_t RegWidths = reg_widths();

  // tot reg width:
  function automatic int unsigned tot_reg_width();
    tot_reg_width = 0;
    for (int unsigned r = 0; r < NrRegs; r++) begin
      tot_reg_width += RegWidths[r];
    end
  endfunction
  // this should be same as the output width, else the config was wrong!
  localparam int unsigned TotRegWidth = tot_reg_width();

  // get the lsb index in an incoming data word of each register:
  function automatic int_da_regs_t reg_in_lsbs();
    int unsigned r_i;
    r_i = 0;
    for (int unsigned f = 0; f < NR_FIELDS; f++) begin
      // spyglass disable_block STARC05-2.9.1.2b
      // it's a function and the end value is static as it's a parameter
      for (int unsigned r = 0; r < NrRegsPField [f]; r++) begin
        reg_in_lsbs[r_i] = (r == 0) ? (FIELD_LSB_IDX[f] % DW) : 0;
        r_i++;
      end
      // spyglass enable_block STARC05-2.9.1.2b
    end
  endfunction

  // get the lsb index for the outgoing data word of each register:
  function automatic int_da_regs_t reg_out_lsbs();
    reg_out_lsbs[0] = 0;
    for (int unsigned r = 0; r < NrRegs - 1; r++) begin
      reg_out_lsbs[r+1] = reg_out_lsbs[r] + RegWidths[r];
    end
  endfunction

  // get the address per register:
  function automatic int_da_regs_t reg_addr();
    int unsigned r_i;
    r_i = 0;
    for (int unsigned f = 0; f < NR_FIELDS; f++) begin
      // spyglass disable_block STARC05-2.9.1.2b
      // it's a function and the end value is static as it's a parameter
      for (int unsigned r = 0; r < NrRegsPField [f]; r++) begin
        reg_addr[r_i] = (r == 0) ? (FIELD_LSB_IDX[f] / 8) : (FIELD_LSB_IDX[f] / 8) + r * (DW / 8);
        r_i++;
      end
      // spyglass enable_block STARC05-2.9.1.2b
    end
  endfunction

  localparam int_da_regs_t RegInLsbs = reg_in_lsbs();
  localparam int_da_regs_t RegOutLsbs = reg_out_lsbs();
  localparam int_da_regs_t RegAddr = reg_addr();
  localparam int unsigned LastAddr = RegAddr[$size(RegAddr)-1];

  localparam int unsigned MaxFillPtrVal = cc_math_pkg::ceil_div(cc_math_pkg::ceil_div(OUT_DW,8), (DW / 8));
  localparam int unsigned PtrValW = $clog2(MaxFillPtrVal + 1);

  localparam int unsigned FmtDw = cc_math_pkg::index_width(NR_FORMATS);
  localparam int unsigned FormatRegIdx = field_reg0_idx(FORMAT_FIELD_IDX);
  localparam int unsigned OutFmtDw = OUT_DW + unsigned'($clog2(NR_FORMATS));

  localparam int unsigned FifoWrdsPCmd = cc_math_pkg::ceil_div(OutFmtDw, CMD_FIFO_WIDTH);
  localparam int unsigned FifoWrdPtrW = cc_math_pkg::index_width(FifoWrdsPCmd);

  typedef int unsigned int_p_ptr_t[MaxFillPtrVal+1];
  typedef int unsigned int_p_wrd_t[FifoWrdsPCmd];
  typedef int unsigned int_p_fmt_t[NR_FORMATS];

  // get the pre-pack fill pointer what is required to start sending towards the FIFO:
  function automatic int_p_wrd_t ptr_val_p_wrd();
    for (int unsigned f = 1; f <= FifoWrdsPCmd; f++) begin
      ptr_val_p_wrd[f-1] = ((f * CMD_FIFO_WIDTH + DW - 1) / DW);
    end
  endfunction
  localparam int_p_wrd_t IntPtrPWrd = ptr_val_p_wrd();

  function automatic int_p_ptr_t wrd_p_ptr_val();
    for (int unsigned i = 0; i < NrRegs; i++) begin
      wrd_p_ptr_val[RegAddr[i]/(DW/8)] = RegOutLsbs[i] / CMD_FIFO_WIDTH;
    end
  endfunction
  localparam int_p_ptr_t WrdPIntPtr = wrd_p_ptr_val();

  // header width, non format dependent and is the same as the LSB of the last field
  localparam int unsigned HeaderWidthIn  = FIELD_LSB_IDX[NR_FIELDS-1];
  localparam int unsigned HeaderWidthOut = RegOutLsbs[field_reg0_idx(NR_FIELDS-1)];
  function automatic int_p_fmt_t get_payload_p_fmt();
    for (int unsigned fmt = 0; fmt < NR_FORMATS; fmt++) begin
      get_payload_p_fmt[fmt] = (FORMAT_NR_BYTES[fmt]*8) - HeaderWidthIn;
    end
  endfunction
  localparam int_p_fmt_t PayloadPerFmt = get_payload_p_fmt();

  // last fifo word per format: HeaderOut (as packed in FIFO) + payload in bits is total format size pushed into the FIFO. Div over FIFO width to get last word
  function automatic int_p_fmt_t last_wrd_p_fmt();
    for (int unsigned fmt = 0; fmt < NR_FORMATS; fmt++) begin
      last_wrd_p_fmt[fmt] = cc_math_pkg::ceil_div((HeaderWidthOut + PayloadPerFmt[fmt]), CMD_FIFO_WIDTH)-1;
    end
  endfunction
  localparam int_p_fmt_t LastWrdPFmt = last_wrd_p_fmt();
  ////////////////////////////////////////////////////////////////////////

  ////////////////////////////////////////////////////////////////////////
  ////// signal declerations:
  logic reg_en[NrRegs];
  logic [DW-1:0] reg_in[NrRegs]; // can't be variable declared per index, slice it in the logic to the required size
  logic [DW-1:0] reg_data[NrRegs]; // can't be variable declared per index, slice it in the logic to the required size
  logic [DW/8-1:0] reg_byte_en[NrRegs];
  logic [(cc_math_pkg::ceil_div(TotRegWidth,CMD_FIFO_WIDTH) * CMD_FIFO_WIDTH)-1:0] reg_q;

  /// AXI2REG:
  logic axi2reg_wvld, axi2reg_wrdy, axi2reg_wresp_vld, axi2reg_wresp_rdy;
  logic axi2reg_rvld, axi2reg_rrdy, axi2reg_rresp_vld, axi2reg_rresp_rdy;
  logic axi2reg_wresp_error, axi2reg_rresp_error;
  logic [DW-1:0] axi2reg_rresp_data;
  logic [DW-1:0] axi2reg_wdata;
  logic [AW-1:0] axi2reg_waddr;
  logic [DW/8-1:0] axi2reg_wstrb;
  logic [AW-1:0] axi2reg_raddr;

  /// CMD FIFO:
  reg cmd_fifo_wvld;
  logic cmd_fifo_wrdy;
  logic cmd_fifo_rvld, cmd_fifo_rrdy;
  logic [CMD_FIFO_WIDTH-1:0] cmd_fifo_wdata;
  logic [CMD_FIFO_WIDTH-1:0] cmd_fifo_rdata;

  // format:
  logic [FmtDw-1:0] cur_format;

  // control:
  // fill pointer: tracks the amount of AXI writes
  // wrd (cur_wrd/snd_wrd): tracks the FIFO word of the command after pre-packing
  logic [PtrValW-1:0] max_fill_ptr;
  logic [FifoWrdPtrW-1:0] last_wrd;
  reg [PtrValW-1:0] fill_pointer;  // steps of DW/8, size of total needed requirement
  logic fill_pointer_incr;
  logic block_axi2reg_wrdy;
  reg fill_pointer_wrp;
  reg [FifoWrdPtrW-1:0] snd_wrd;  // out of the FIFO, wrd ptr ready for sending (post_packing)
  logic [FifoWrdPtrW-1:0] cur_wrd;  // into the FIFO, wrd ptr ready for pushing into FIFO
  logic snd_wrd_incr;

  // post-packing ctrl
  logic [FmtDw-1:0] post_pack_format;
  logic [FmtDw-1:0] cur_cmd_format;
  reg [FmtDw-1:0] outp_format_q;
  reg [FifoWrdPtrW-1:0] outp_wrd_q;
  logic [FifoWrdPtrW-1:0] outp_wrd_nxt;
  logic [FifoWrdPtrW-1:0] outp_last_wrd;
  logic outp_last;
  logic [OutFmtDw-1:0] post_pack_data_in;
  reg [OutFmtDw-1:0] post_pack_data_q;

  // tracking counter:
  logic [cc_math_pkg::index_width(CMD_FIFO_DEPTH+1)-1:0] cur_fifo_count_q;

  logic not_connected;

  // spyglass disable_block W528
  assign not_connected = (|axi2reg_waddr);
  // spyglass enable_block W528

  ////////////////////////////////////////////////////////////
  ///// combinatorial logic:

  // assign the concatonated registers to the cmd fifo, and rdata based on the raddr
  logic [cc_math_pkg::ceil_div(TotRegWidth,CMD_FIFO_WIDTH)-1:0][CMD_FIFO_WIDTH-1:0] aligned_regs_out;
  always_comb aligned_regs_out = reg_q;
  // pre-pack mux:
  always_comb cmd_fifo_wdata = aligned_regs_out[snd_wrd];

  logic [cc_math_pkg::ceil_div(TotRegWidth,DW)-1:0][DW-1:0] dw_aligned_regs_out;
  always_comb dw_aligned_regs_out = reg_q;
    // error if address is above reg range
  always_comb axi2reg_rresp_error = axi2reg_raddr[AW-1:cc_math_pkg::index_width(DW/8)] < cc_math_pkg::ceil_div(TotRegWidth, DW) ? 1'b0 : 1'b1;
  always_comb axi2reg_rresp_data = axi2reg_rresp_error ? '1 : dw_aligned_regs_out[axi2reg_raddr[AW-1:cc_math_pkg::index_width(DW/8)]];

  // always accept read immediately, wire through the vld and ready from req to resp:
  assign axi2reg_rresp_vld = axi2reg_rvld;
  assign axi2reg_rrdy = axi2reg_rresp_rdy;

  // address check for input, enable register when pointer matches and axi2reg is valid and can be accepted:
  for (genvar i = 0; unsigned'(i) < NrRegs; i++) begin : g_reg_en
    assign reg_en[i] = (fill_pointer == RegAddr[i]/(DW/8)) ? axi2reg_wvld & ~block_axi2reg_wrdy : 1'b0;
  end

  // assign write to response, as long as it's not blocked:
  assign axi2reg_wrdy = ~block_axi2reg_wrdy;
  assign axi2reg_wresp_error = '0; // TBD: if address check needs to be done, now any address is allowed
  assign axi2reg_wresp_vld = axi2reg_wvld & ~block_axi2reg_wrdy;

  // control the fill pointer increase based on a write to the regs:
  assign block_axi2reg_wrdy = ~axi2reg_wresp_rdy;  // block access as long response is blocking
  assign fill_pointer_incr = axi2reg_wvld & axi2reg_wresp_rdy & (|axi2reg_wstrb); // mask also with strb, no strb active => no increase

  // Drop if FIFO can't accept:
  assign cmd_dropped = cmd_fifo_wvld & ~cmd_fifo_wrdy;

  // Check if word can be pushed into FIFO
  always_comb begin : cmd_ctrl
    snd_wrd_incr = 1'b0;
    // if ((fill_pointer == max_fill_ptr) && fill_pointer_incr) begin
    // snd_wrd_incr = 1'b1;
    // end else
    if (snd_wrd != cur_wrd) begin
      snd_wrd_incr = 1'b1;
    end
  end

  logic send_leftover;
  always_comb cur_wrd = WrdPIntPtr[fill_pointer] + send_leftover;
  //////////////////////////////////////////////////

  //////////////////////////////////////////////////
  // max fill pointer based on command format:
  if (NR_FORMATS > 1) begin : g_max_fill_ptr_sel
    always_comb begin : max_fill_ptr_sel
      max_fill_ptr = cc_math_pkg::ceil_div(FORMAT_NR_BYTES[cur_format], (DW / 8)) - 1; //-1 to compensate for checker at the moment pointer is not yet increased
      last_wrd = LastWrdPFmt[cur_format];
    end
  end else begin : g_max_fill_ptr_stat
    assign max_fill_ptr = cc_math_pkg::ceil_div(FORMAT_NR_BYTES[0], (DW / 8)) - 1;
    assign last_wrd = LastWrdPFmt[0];
  end
  //////////////////////////////////////////////////

  //////////////////////////////////////////////////
  // sequential:
  // fill pointer
  logic fill_pointer_wrp_en, fill_pointer_wrp_d;
  logic send_leftover_en, send_leftover_d;
  always_comb begin
    fill_pointer_wrp_d  = 1'b0;
    fill_pointer_wrp_en = 1'b0;
    send_leftover_d     = 1'b0;
    send_leftover_en    = 1'b0;

    if (fill_pointer_wrp) fill_pointer_wrp_en = 1'b1;
    if (send_leftover) send_leftover_en = 1'b1;

    if (pointer_rst == 1'b0 && fill_pointer_incr == 1'b1) begin
      if (fill_pointer == max_fill_ptr) begin
        if (cur_wrd != last_wrd) begin // Something left to send to the FIFO
          send_leftover_d  = 1'b1;
          send_leftover_en = 1'b1;
        end
        fill_pointer_wrp_d  = 1'b1;
        fill_pointer_wrp_en = 1'b1;
      end
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : ctrl_reg
    if (i_rst_n == 1'b0) begin
      fill_pointer <= '0;
      snd_wrd <= '0;
      fill_pointer_wrp <= '0;
      send_leftover <= '0;

    end else begin
      // fill pointer:
      if (fill_pointer_wrp_en) fill_pointer_wrp <= fill_pointer_wrp_d;
      if (send_leftover_en) send_leftover <= send_leftover_d;

      if (pointer_rst == 1'b1) begin  // synchronous software reset
        fill_pointer <= '0;
      end else if (fill_pointer_incr == 1'b1) begin
        if (fill_pointer == max_fill_ptr) begin
          fill_pointer <= '0;
        end else begin
          fill_pointer <= fill_pointer + 1;
        end
      end

      // cur wrd and write valid:
      // cmd_fifo_wvld <= 1'b0;
      if (pointer_rst == 1'b1) begin  // synchronous software reset
        snd_wrd <= '0;
      end else if (snd_wrd_incr == 1'b1) begin
        // cmd_fifo_wvld <= 1'b1;
        snd_wrd <= cur_wrd;
      end
    end
  end
  assign cur_pointer   = 8'(fill_pointer);
  assign cmd_fifo_wvld = snd_wrd_incr | fill_pointer_wrp | send_leftover;

  // status counter flops:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : stat_reg
    if (i_rst_n == 1'b0) begin
      cur_fifo_count_q <= '0;
    end else begin
      // cmd fifo tracking:
      if ((cmd_fifo_wvld & cmd_fifo_wrdy) &
          (~(cmd_fifo_rvld & cmd_fifo_rrdy))) begin // increase, unless also reading
        cur_fifo_count_q <= cur_fifo_count_q + 1;
      end else if ((~(cmd_fifo_wvld & cmd_fifo_wrdy)) &
          (cmd_fifo_rvld & cmd_fifo_rrdy)) begin // decrease, unless also writing
        cur_fifo_count_q <= cur_fifo_count_q - 1;
      end
    end
  end
  assign cur_fifo_count = 8'(cur_fifo_count_q + (cmd_fifo_wvld & cmd_fifo_wrdy));
  //////////////////////////////////////////////////

  ////////////////////////////////////////////////////////////////////
  //// Used modules
  // the registers for constructing the entire command
  for (genvar i = 0; unsigned'(i) < NrRegs; i++) begin : g_regs
    cmdblock_reg #(
      .REG_W(RegWidths[i])
    ) i_reg (
      .i_clk(i_clk),

      .en(reg_en[i]),
      .byte_en(reg_byte_en[i][(RegWidths[i]+7)/8-1:0]),
      .d(reg_in[i][RegWidths[i]-1:0]),
      .q(reg_data[i][RegWidths[i]-1:0])
    );
    assign reg_in[i][RegWidths[i]-1:0] = axi2reg_wdata[RegWidths[i] + RegInLsbs[i]-1:RegInLsbs[i]];
    assign reg_byte_en[i][(RegWidths[i]+7)/8-1:0] = axi2reg_wstrb[(RegWidths[i]+RegInLsbs[i]+7)/8-1:(RegInLsbs[i]+7)/8];
    assign reg_q[RegOutLsbs[i] + RegWidths[i]-1:RegOutLsbs[i]] = reg_data[i][RegWidths[i]-1:0];
  end
  if (TotRegWidth < unsigned'($bits(reg_q))) assign reg_q[$bits(reg_q)-1:TotRegWidth] = '0; // make sure all bits are driven

  // assign the one for the format:
  if (NR_FORMATS > 1) begin : g_fmt_assign
    // when fill pointer is zero the current header will be loaded via the axi2reg, use that to determin the current format
    // else the flopped version can be used
    assign cur_format = (fill_pointer==0) ? axi2reg_wdata[FIELD_LSB_IDX[FORMAT_FIELD_IDX]+:FmtDw] : reg_data[FormatRegIdx][RegWidths[FormatRegIdx]-1:0];
  end

  //////// AXI 2 REG, convert AXI to simple alligned single access
  axi2reg #(
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .NR_WR_REQS(4),
    .NR_RD_REQS(2),
    .WBUF(2),
    .OSR(4),
    .RD_RESP_DEPTH(2),
    .WR_RESP_DEPTH(4)
  ) i_axi_reg (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid),
    .awaddr(awaddr),
    .awlen(awlen),
    .awsize(awsize),
    .awburst(awburst),
    .awvalid(awvalid),
    .awready(awready),
    // Read Address Channel
    .arid(arid),
    .araddr(araddr),
    .arlen(arlen),
    .arsize(arsize),
    .arburst(arburst),
    .arvalid(arvalid),
    .arready(arready),
    // Write  Data Channel
    .wdata(wdata),
    .wstrb(wstrb),
    .wlast(wlast),
    .wvalid(wvalid),
    .wready(wready),
    // Read Data Channel
    .rid(rid),
    .rdata(rdata),
    .rresp(rresp),
    .rlast(rlast),
    .rvalid(rvalid),
    .rready(rready),
    // Write Response Channel
    .bid(bid),
    .bresp(bresp),
    .bvalid(bvalid),
    .bready(bready),

    ////// reg master:
    // Write path:
    .reg_wvld(axi2reg_wvld),
    .reg_wrdy(axi2reg_wrdy),
    .reg_waddr(axi2reg_waddr),
    .reg_wdata(axi2reg_wdata),
    .reg_wstrb(axi2reg_wstrb),
    .reg_wresp_vld(axi2reg_wresp_vld),
    .reg_wresp_rdy(axi2reg_wresp_rdy),
    .reg_wresp_error(axi2reg_wresp_error),

    // Read path:
    .reg_rvld(axi2reg_rvld),
    .reg_rrdy(axi2reg_rrdy),
    .reg_raddr(axi2reg_raddr),
    .reg_rresp_vld(axi2reg_rresp_vld),
    .reg_rresp_rdy(axi2reg_rresp_rdy),
    .reg_rresp_error(axi2reg_rresp_error),
    .reg_rresp_data(axi2reg_rresp_data)
  );

  /////// CMD fifo:
  cc_stream_buffer #(
    .DEPTH(CMD_FIFO_DEPTH),
    .DW(CMD_FIFO_WIDTH),
    .USE_MACRO(USE_MACRO)
  ) i_cmd_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (cmd_fifo_wvld),
    .wr_data(cmd_fifo_wdata),
    .wr_rdy (cmd_fifo_wrdy),

    .rd_rdy (cmd_fifo_rrdy),
    .rd_data(cmd_fifo_rdata),
    .rd_vld (cmd_fifo_rvld)
  );

  /////// str block for the output stream, only execute a command when exec is high:
  cmdblock_str_block i_str_block (
    .block (~exec),
    .sl_vld(cmd_fifo_rvld & outp_last),
    .sl_rdy(cmd_fifo_rrdy),
    .mt_vld(cmd_vld),
    .mt_rdy(cmd_rdy)
  );
  if (NR_FORMATS > 1) begin : g_cmd_format_outp
    // split out cmd format
    assign cmd_data = {
      post_pack_data_in[OutFmtDw-1:(RegOutLsbs[FormatRegIdx]+FmtDw)],
      post_pack_data_in[(RegOutLsbs[FormatRegIdx]-1):0]
    };
    assign post_pack_format = post_pack_data_in[RegOutLsbs[FormatRegIdx]+:FmtDw];
    assign cur_cmd_format = (outp_wrd_q == 0) ? post_pack_format : outp_format_q;
    assign cmd_format = cur_cmd_format;

    always_ff @(posedge i_clk, negedge i_rst_n) begin : post_pck_ctrl_fmt
      if (i_rst_n == 1'b0) begin
        outp_format_q <= '0;
      end else begin
        if (cmd_fifo_rvld & cmd_fifo_rrdy) begin
          if (outp_wrd_q == 0) outp_format_q <= cur_cmd_format;
        end
      end
    end
  end else begin : g_outp
    assign cmd_data = cmd_fifo_rdata;
    assign cmd_format = '0;
  end
  ////////////////////////////////////////////////////////////////////

  assign outp_wrd_nxt = (outp_wrd_q == outp_last_wrd) ? 0 : outp_wrd_q + 1;
  assign outp_last = (outp_wrd_q == outp_last_wrd) ? 1'b1 : 1'b0;

  // post packing ctrl:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : post_pck_ctrl_regs
    if (i_rst_n == 1'b0) begin
      outp_wrd_q  <= '0;
    end else begin
      if (cmd_fifo_rvld & cmd_fifo_rrdy) begin
        outp_wrd_q  <= outp_wrd_nxt;
      end
    end
  end

  // no reset needed for the post_pack_data:
  if (FifoWrdsPCmd > 1) begin: g_post_pack_data_flop
  always_ff @(posedge i_clk or negedge i_rst_n) begin : post_pck_data_regs
    if (i_rst_n == 1'b0)
      post_pack_data_q <= '0;
    else if (cmd_fifo_rvld & cmd_fifo_rrdy)
      post_pack_data_q <= post_pack_data_in;
  end
  end

  for (genvar w = 0; unsigned'(w) < FifoWrdsPCmd; w++) begin : g_post_pack
    if (w == FifoWrdsPCmd - 1)  // last one
      assign post_pack_data_in[OutFmtDw-1:(w*CMD_FIFO_WIDTH)] = cmd_fifo_rdata[OutFmtDw-(w*CMD_FIFO_WIDTH)-1:0];
    else
      assign post_pack_data_in[(w*CMD_FIFO_WIDTH) +: CMD_FIFO_WIDTH] = (w == outp_wrd_q) ? cmd_fifo_rdata :
                                                                                            post_pack_data_q[(w*CMD_FIFO_WIDTH) +: CMD_FIFO_WIDTH];
  end

  // last word pointer based on outp format:
  if (NR_FORMATS > 1) begin : g_outp_wrd_ptr_sel
    always_comb outp_last_wrd = unsigned'(LastWrdPFmt[cur_cmd_format]);
  end else begin : g_outp_wrd_ptr_stat
    // parameter set as int of 32b, LHS is not
    // spyglass disable_block W164a_a
    assign outp_last_wrd = unsigned'(LastWrdPFmt[0]);
    // spyglass enable_block W164a_a
  end

  // Status signals are fixed to 8 bit width for CSR alignment
  // following https://git.axelera.ai/ai-hw-team/triton/-/issues/229:
  //synopsys translate_off
  `ifndef TARGET_SIMULATION
  if ($bits(fill_pointer) > 8)
    $fatal(1, "cmdblock_cmd_fifo: fill_pointer exceeds max width of 8 bits!");
  if ($bits(cur_fifo_count_q) > 8)
    $fatal(1, "cmdblock_cmd_fifo: cur_fifo_count_q exceeds max width of 8 bits!");
  `endif
  //synopsys translate_on

endmodule

`endif  // _CMDBLOCK_CMD_FIFO_SV_
