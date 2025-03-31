// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of CMDBlock
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_SV_
`define _CMDBLOCK_SV_

module cmdblock #(
  parameter int IDW = 4,
  parameter int AW  = 36,
  parameter int DW  = 64,
  parameter int BW  = 6,

  parameter int DYNAMIC_CMD_SIZE = 10,
  parameter int NR_TOK_PROD = 3,
  parameter int NR_TOK_CONS = 3,
  parameter int NR_TOP_TOK_PROD = 0,
  parameter int NR_TOP_TOK_CONS = 0,
  parameter int MAX_OUTST_CMDS = 3,
  parameter int CMD_CONFIG_WIDTH = 1,

  parameter int DESC_MEM_ARB_SCHEME = 1,

  parameter int CMD_FIFO_DEPTH = 4,
  localparam int TotNrTokProd = NR_TOK_PROD + NR_TOP_TOK_PROD,
  localparam int TotNrTokCons = NR_TOK_CONS + NR_TOP_TOK_CONS,
  localparam int TotCmdFifoDw = DYNAMIC_CMD_SIZE + TotNrTokProd + TotNrTokCons + CMD_CONFIG_WIDTH + cmdblock_pkg::CMDB_TRIGGER_W,
  localparam int TotCmdDw = DYNAMIC_CMD_SIZE,

  parameter int NR_FORMATS = 1,
  parameter int FORMAT_NR_BYTES[NR_FORMATS] = '{
    (DYNAMIC_CMD_SIZE + 7) / 8
  },  // the number of AXI writes needed per format
  localparam int NrFormatsWd = $clog2(NR_FORMATS),
  parameter int CMD_FIFO_WIDTH = TotCmdFifoDw + $clog2(NR_FORMATS),
  parameter int USE_MACRO = 0,
  parameter int DEV_ADDR_CAP = 'h1000
) (
  input wire i_clk,
  input wire i_rst_n,

  ///// Sideband:
  input logic exec,
  input logic pointer_rst,

  output logic cmd_dropped,

  // status:
  output logic [7:0] stat_cur_pointer,
  output logic [7:0] stat_cur_fifo_count,
  output logic [7:0] stat_nr_outst_cmds,
  output logic stat_wait_token,
  output cmdblock_pkg::cmbd_state_e o_stat_state,
  output logic [TotNrTokCons-1:0] o_stat_pending_tokens,

  ///// AXI slave:
  // Write Address Channel
  input  logic [ IDW-1:0] awid,
  input  logic [  AW-1:0] awaddr,
  input  logic [  BW-1:0] awlen,
  input  logic [     2:0] awsize,
  input  logic [     1:0] awburst,
  // input  logic [  MT_LW-1:0] awlock,
  // input  logic [        3:0] awcache,
  // input  logic [       2:0] awprot,
  input  logic            awvalid,
  output logic            awready,
  // Read Address Channel
  input  logic [ IDW-1:0] arid,
  input  logic [  AW-1:0] araddr,
  input  logic [  BW-1:0] arlen,
  input  logic [     2:0] arsize,
  input  logic [     1:0] arburst,
  // input  logic [  MT_LW-1:0] arlock,
  // input  logic [        3:0] arcache,
  // input  logic [       2:0] arprot,
  input  logic            arvalid,
  output logic            arready,
  // Write  Data Channel
  input  logic [  DW-1:0] wdata,
  input  logic [DW/8-1:0] wstrb,
  input  logic            wlast,
  input  logic            wvalid,
  output logic            wready,
  // Read Data Channel
  output logic [ IDW-1:0] rid,
  output logic [  DW-1:0] rdata,
  output logic [     1:0] rresp,
  output logic            rlast,
  output logic            rvalid,
  input  logic            rready,
  // Write Response Channel
  output logic [ IDW-1:0] bid,
  output logic [     1:0] bresp,
  output logic            bvalid,
  input  logic            bready,

  ///// Tokens:
  output logic [TotNrTokProd-1:0] tok_prod_vld,
  input  logic [TotNrTokProd-1:0] tok_prod_rdy,
  input  logic [TotNrTokCons-1:0] tok_cons_vld,
  output logic [TotNrTokCons-1:0] tok_cons_rdy,

  ///// Timestamp:
  output logic o_ts_start,
  output logic o_ts_end,
  ///// ACD sync:
  output logic o_acd_sync,

  ///// Command:
  input logic cmd_done,
  output logic [TotCmdDw-1 : 0] cmd_data,
  output logic [cc_math_pkg::index_width(NR_FORMATS)-1:0] cmd_format,
  output logic [CMD_CONFIG_WIDTH-1:0] cmd_config,
  output logic cmd_vld,
  input logic cmd_rdy
);

  localparam int CmdFifoAddrMsb = $clog2(DEV_ADDR_CAP);

  // increase header to be 2x64b in case the number of tokens overflow their fields
  localparam bit ExtendedHeader = (NR_TOP_TOK_PROD > 0) || (NR_TOP_TOK_CONS > 0);
  localparam int HeaderSize = ExtendedHeader ? 16 : 8;

  // increase format size based on the header:
  typedef int int_fmt_size_t[NR_FORMATS];
  function automatic int_fmt_size_t set_format_sizes();
    for (int unsigned f = 0; f < NR_FORMATS; f++) begin
      set_format_sizes[f] = FORMAT_NR_BYTES[f] + HeaderSize;
    end
  endfunction
  localparam int_fmt_size_t FormatSizeWithHeader = set_format_sizes();

  //////////////////////////////////////////////////////////
  ////// Parameters for the header:
  localparam int unsigned NrFields = ExtendedHeader ? 8 : 6;
  typedef int unsigned int_field_nrm_param_t[6];
  typedef int unsigned int_field_ext_param_t[8];
  typedef int unsigned int_field_param_t[NrFields];

  // Field idx, in order of LSB->MSB
  typedef enum int {
    trigger_idx   = 'd0,
    tok_prod0_idx = 'd1,
    tok_cons0_idx = 'd2,
    fmt_idx       = 'd3,
    config_idx    = 'd4,
    dyn_cmd_idx   = 'd5
  } cmbd_field_idx_e;

  typedef enum int {
    ext_tok_prod1_idx = 'd5,
    ext_tok_cons1_idx = 'd6,
    ext_dyn_cmd_idx   = 'd7 // in case of extended header the dyn_cmd lies at a different location
  } cmbd_ext_fields_idx_e;

  // Field LSB:
  localparam int_field_nrm_param_t CmdbFieldLsbsNorm = '{
    0 /*trigger_idx*/   : 32'd0,
    1 /*tok_prod0_idx*/ : 32'd16,
    2 /*tok_cons0_idx*/ : 32'd32,
    3 /*fmt_idx*/       : 32'd48,
    4 /*config_idx*/    : 32'd56,
    5 /*dyn_cmd_idx*/   : 32'd64
  };
  localparam int_field_ext_param_t CmdbFieldLsbsExt = '{
    0 /*trigger_idx*/   : 32'd0,
    1 /*tok_prod0_idx*/ : 32'd16,
    2 /*tok_cons0_idx*/ : 32'd32,
    3 /*fmt_idx*/       : 32'd48,
    4 /*config_idx*/    : 32'd56,
    5 /*ext_tok_prod1_idx*/ : 32'd64,
    6 /*ext_tok_cons1_idx*/ : 32'd96,
    7 /*ext_dyn_cmd_idx*/   : 32'd128
  };

  // Field sizes:
  localparam int_field_nrm_param_t CmdbSizesNrm = '{
    0 /*trigger_idx*/:   cmdblock_pkg::CMDB_TRIGGER_W,
    1 /*tok_prod0_idx*/: NR_TOK_PROD,
    2 /*tok_cons0_idx*/: NR_TOK_CONS,
    3 /*fmt_idx*/:       NrFormatsWd,
    4 /*config_idx*/:    CMD_CONFIG_WIDTH,
    5 /*dyn_cmd_idx*/:   DYNAMIC_CMD_SIZE
  };
  localparam int_field_ext_param_t CmdbSizesExt = '{
    0 /*trigger_idx*/:   cmdblock_pkg::CMDB_TRIGGER_W,
    1 /*tok_prod0_idx*/: NR_TOK_PROD,
    2 /*tok_cons0_idx*/: NR_TOK_CONS,
    3 /*fmt_idx*/:       NrFormatsWd,
    4 /*config_idx*/:    CMD_CONFIG_WIDTH,
    5 /*ext_tok_prod1_idx*/: NR_TOP_TOK_PROD,
    6 /*ext_tok_cons1_idx*/: NR_TOP_TOK_CONS,
    7 /*ext_dyn_cmd_idx*/:   DYNAMIC_CMD_SIZE
  };

  function automatic int_field_param_t set_field_lsb();
    for (int unsigned i=0;i<NrFields; i++)
      set_field_lsb[i] = ExtendedHeader ? CmdbFieldLsbsExt[i] : CmdbFieldLsbsNorm[i];
  endfunction

  function automatic int_field_param_t set_field_size();
    for (int unsigned i=0;i<NrFields; i++)
      set_field_size[i] = ExtendedHeader ? CmdbSizesExt[i] : CmdbSizesNrm[i];
  endfunction
  localparam int unsigned FieldLsb[NrFields] = set_field_lsb();
  localparam int unsigned FieldSize[NrFields] = set_field_size();
  //////////////////////////////////////////

  logic block_outp_strm;
  logic cmd_fifo_vld;
  logic cmd_fifo_rdy;
  logic [TotCmdFifoDw-1:0] cmd_fifo_data;
  logic [cmdblock_pkg::CMDB_TRIGGER_W-1:0] cmd_triggers;
  logic [NR_TOK_PROD-1:0] cmd_loc_tok_prod;
  logic [NR_TOK_CONS-1:0] cmd_loc_tok_cons;
  logic [NR_TOP_TOK_PROD-1:0] cmd_top_tok_prod;
  logic [NR_TOP_TOK_CONS-1:0] cmd_top_tok_cons;
  logic [TotNrTokProd-1:0] cmd_all_tok_prod;
  logic [TotNrTokCons-1:0] cmd_all_tok_cons;
  logic [DYNAMIC_CMD_SIZE-1:0] cmd_payload;
  logic [TotCmdDw - 1 : 0] cmd_data_concat;
  logic [CMD_CONFIG_WIDTH-1:0] cmd_config_d, cmd_config_q;
  reg   cmd_ts_start_q;
  logic [cc_math_pkg::index_width(NR_FORMATS)-1:0] cmd_format_fifo;
  reg [cc_math_pkg::index_width(NR_FORMATS)-1:0] cmd_format_fifo_q;

  logic [3:0] cmd_fifo_vld_cast;
  logic [3:0] cmd_fifo_rdy_cast;

  reg snd_strm_vld;
  logic snd_strm_rdy;
  logic hold_cmd_fifo;
  logic cmd_send;

  reg [cc_math_pkg::index_width(MAX_OUTST_CMDS+1)-1:0] cur_nr_outst_cmds;

  // Since the cur_nr_outst_cmds only reflects the accepted cmds (cmd_vld & cmd_rdy has been asserted) it does not see any pending cmd_vld.
  // However, once a cmd becomes pending, it is removed from the cmd_fifo. At this point it becomes invisible to any of the status signals.
  // To avoid this, cmd_vld gets added to cur_nr_outst_cmds.
  // Upon acceptance (i.e. cmd_rdy asserted), the cmd is added to the cur_nr_outst_cmds and cmd_vld goes low.
  // As a result stat_nr_outst_cmds remains constant (unless a new cmd is immediatly avialable to set cmd_vld)
  always_comb stat_nr_outst_cmds = 8'(cur_nr_outst_cmds + cmd_vld);

  // status: current outstanding commands:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : i_cmd_cnt
    if (i_rst_n == '0) begin
      cur_nr_outst_cmds <= '0;
    end else begin
      if ((cmd_done == 1'b1) && (cmd_send == 1'b0))  // done and not send, -1
        cur_nr_outst_cmds <= cur_nr_outst_cmds - 1;
      else if ((cmd_done == 1'b0) && (cmd_send == 1'b1))  // not done and send, +1
        cur_nr_outst_cmds <= cur_nr_outst_cmds + 1;
    end
  end

  // Construct CMD Block state, based on the FIFO and oustanding command counts
  always_comb begin
    if ((stat_cur_fifo_count == 0) && (stat_nr_outst_cmds == 0)) begin // nothing in fifo or outstanding
      if (stat_cur_pointer == 0) // nothing in pre-packing
        o_stat_state = cmdblock_pkg::idle;
      else
        o_stat_state = cmdblock_pkg::fill;
    end else if (stat_nr_outst_cmds != 0) // something is being executed
      o_stat_state = cmdblock_pkg::exec;
    else
      o_stat_state = cmdblock_pkg::ready;  // nothing being executed, but fifo count is non zero
  end

  // hold cmd fifo as long outgoing command is being send
  always_comb hold_cmd_fifo = snd_strm_vld;  // & ~snd_strm_rdy;

  // Command fifo:
  cmdblock_cmd_fifo #(
    .IDW(IDW),
    .AW(CmdFifoAddrMsb+1),
    .DW(DW),
    .OUT_DW(TotCmdFifoDw),
    .BW(BW),

    .NR_FORMATS(NR_FORMATS),
    .FORMAT_NR_BYTES(FormatSizeWithHeader),
    .FORMAT_FIELD_IDX(fmt_idx),

    .NR_FIELDS(NrFields),
    .FIELD_LSB_IDX(FieldLsb),
    .FIELD_SIZE(FieldSize),
    .CMD_FIFO_DEPTH(CMD_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(CMD_FIFO_WIDTH)
  ) i_cmd_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .exec(exec & ~hold_cmd_fifo),
    .pointer_rst(pointer_rst),
    .cur_pointer(stat_cur_pointer),
    .cur_fifo_count(stat_cur_fifo_count),
    .cmd_dropped(cmd_dropped),

    .awid(awid),
    .awaddr(awaddr[CmdFifoAddrMsb:0]),
    .awlen(awlen),
    .awsize(awsize),
    .awburst(awburst),
    .awvalid(awvalid),
    .awready(awready),

    .arid(arid),
    .araddr(araddr[CmdFifoAddrMsb:0]),
    .arlen(arlen),
    .arsize(arsize),
    .arburst(arburst),
    .arvalid(arvalid),
    .arready(arready),

    .wdata (wdata),
    .wstrb (wstrb),
    .wlast (wlast),
    .wvalid(wvalid),
    .wready(wready),

    .rid(rid),
    .rdata(rdata),
    .rresp(rresp),
    .rlast(rlast),
    .rvalid(rvalid),
    .rready(rready),

    .bid(bid),
    .bresp(bresp),
    .bvalid(bvalid),
    .bready(bready),

    .cmd_data(cmd_fifo_data),
    .cmd_format(cmd_format_fifo),
    .cmd_vld(cmd_fifo_vld),
    .cmd_rdy(cmd_fifo_rdy & ~hold_cmd_fifo)
  );
  if (ExtendedHeader) begin : g_ext_header
    if (NR_TOK_CONS == 0 && NR_TOK_PROD == 0) begin : g_no_local_tokens
      always_comb {cmd_payload, cmd_all_tok_cons, cmd_all_tok_prod, cmd_config_d, cmd_triggers} = cmd_fifo_data;
    end else begin : g_all_tokens
      always_comb {cmd_payload, cmd_top_tok_cons, cmd_top_tok_prod, cmd_config_d, cmd_loc_tok_cons, cmd_loc_tok_prod, cmd_triggers} = cmd_fifo_data;
      always_comb cmd_all_tok_prod = {cmd_top_tok_prod, cmd_loc_tok_prod};
      always_comb cmd_all_tok_cons = {cmd_top_tok_cons, cmd_loc_tok_cons};
    end
  end else
    always_comb {cmd_payload, cmd_config_d, cmd_all_tok_cons, cmd_all_tok_prod, cmd_triggers} = cmd_fifo_data;

  // duplicate cmd vld/rdy with multicast for all other blocks:
  cmdblock_str_multicast #(
    .NR_OUTPUTS(4)
  ) i_str_multicast (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .s_vld(cmd_fifo_vld),
    .s_rdy(cmd_fifo_rdy),

    .m_vld(cmd_fifo_vld_cast),
    .m_rdy(cmd_fifo_rdy_cast)
  );

  // Token producer:
  if (TotNrTokProd > 0)
    cmdblock_tok_prod #(
      .NR_TOK(TotNrTokProd),
      .MAX_OUTST_CMDS(MAX_OUTST_CMDS)
    ) i_tok_prod (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .cmd_tok_vld(cmd_fifo_vld_cast[0]),
      .cmd_tok(cmd_all_tok_prod),
      .cmd_tok_rdy(cmd_fifo_rdy_cast[0]),

      .tok_vld(tok_prod_vld),
      .tok_rdy(tok_prod_rdy),

      .cmd_done(cmd_done)
    );
  else
    always_comb cmd_fifo_rdy_cast[0] = 'b1;

  // Token receiver:
  if (TotNrTokCons > 0)
    cmdblock_tok_cons #(
      .NR_TOK(TotNrTokCons)
    ) i_tok_cons (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .cmd_tok_vld(cmd_fifo_vld_cast[1]),
      .cmd_tok(cmd_all_tok_cons),
      .cmd_tok_rdy(cmd_fifo_rdy_cast[1]),

      .tok_vld(tok_cons_vld),
      .tok_rdy(tok_cons_rdy),

      .block_cmd(block_outp_strm),
      .cmd_snd  (cmd_send),

      .wait_token(stat_wait_token),
      .pending_tokens(o_stat_pending_tokens)
    );
  else begin : g_no_tok_cons
    always_comb cmd_fifo_rdy_cast[1] = 'b1;
    always_comb block_outp_strm = 'b0;
  end

  ////// triggers:
  logic ts_start_d;
  reg ts_start_q, ts_start_qq;

  logic fifo_acd_end, fifo_ts_end;
  logic acd_end_d, ts_end_d;
  logic acd_end_q, ts_end_q;
  logic end_triggers_vld;
  cc_stream_buffer #(
    .DEPTH(MAX_OUTST_CMDS),
    .DW(2)
  ) u_trigger_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (cmd_fifo_vld_cast[3]),
    .wr_data({cmd_triggers[cmdblock_pkg::acd_end_idx], cmd_triggers[cmdblock_pkg::ts_end_idx]}),
    .wr_rdy (cmd_fifo_rdy_cast[3]),

    .rd_rdy (cmd_done), // pulse
    .rd_data({fifo_acd_end, fifo_ts_end}),
    .rd_vld (end_triggers_vld)
  );
  always_comb ts_start_d = cmd_ts_start_q & cmd_send;
  always_comb ts_end_d    = fifo_ts_end  & end_triggers_vld & cmd_done;
  always_comb acd_end_d   = fifo_acd_end & end_triggers_vld & cmd_done;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      ts_start_q  <= '0;
      ts_end_q  <= '0;
      acd_end_q  <= '0;
    end else begin
      if (ts_start_q != ts_start_d)
        ts_start_q <= ts_start_d;
      if (ts_end_q != ts_end_d)
        ts_end_q <= ts_end_d;
      if (acd_end_q != acd_end_d)
        acd_end_q <= acd_end_d;
    end
  end

  always_comb o_ts_start = ts_start_q;
  always_comb o_ts_end   = ts_end_q;
  always_comb o_acd_sync = acd_end_q;
  //////////////////////

  always_comb cmd_fifo_rdy_cast[2] = 'b1;
  reg [DYNAMIC_CMD_SIZE-1:0] cmd_data_concat_q;
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      cmd_data_concat_q <= '0;
      cmd_format_fifo_q <= '0;
      cmd_config_q      <= '0;
      cmd_ts_start_q    <= '0;
    end else begin
      if (cmd_fifo_vld_cast[2]) begin
        cmd_data_concat_q <= cmd_payload;
        cmd_format_fifo_q <= cmd_format_fifo;
        cmd_config_q      <= cmd_config_d;
        cmd_ts_start_q    <= cmd_triggers[cmdblock_pkg::ts_start_idx];
      end
    end
  end

  /////// send stream once all rdy/vld's are resolved:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : snd_strm
    if (i_rst_n == 1'b0) begin
      snd_strm_vld <= '0;
    end else begin
      if (cmd_fifo_rdy & cmd_fifo_vld) snd_strm_vld <= '1;
      else if (snd_strm_vld & snd_strm_rdy) snd_strm_vld <= '0;
    end
  end
  always_comb cmd_send = snd_strm_rdy & snd_strm_vld;

  /////// str block for the output stream, only execute a command when block_stream is low:
  cmdblock_str_block i_str_block (
    .block (block_outp_strm),
    .sl_vld(snd_strm_vld),
    .sl_rdy(snd_strm_rdy),
    .mt_vld(cmd_vld),
    .mt_rdy(cmd_rdy)
  );
  always_comb cmd_data   = cmd_data_concat_q;
  always_comb cmd_format = cmd_format_fifo_q;
  always_comb cmd_config = cmd_config_q;

  // Status signals are fixed to 8 bit width for CSR alignment
  // following https://git.axelera.ai/ai-hw-team/triton/-/issues/229:
  //synopsys translate_off
  if ($bits(cur_nr_outst_cmds + cmd_vld) > 8)
    $fatal(1, "cmdblock: (cur_nr_outst_cmds + cmd_vld) exceeds max width of 8 bits!");
  //synopsys translate_on

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
  property p_vld_deassrtion_on_rdy(i_clk, i_rst_n, vld, rdy);
    @(posedge i_clk) disable iff (!i_rst_n) vld & ~rdy |=> vld;
  endproperty

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, cmd_vld, cmd_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, tok_prod_vld, tok_prod_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, tok_cons_vld, tok_cons_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

`endif  // ASSERTIONS_ON
  //synopsys translate_on
endmodule

`endif  // _CMDBLOCK_SV_
