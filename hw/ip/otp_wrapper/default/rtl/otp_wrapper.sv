// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***

// Description: OTP wrapper.

// Module declaration

module otp_wrapper
  import otp_wrapper_csr_reg_pkg::*;
  import otp_wrapper_pkg::*;
    (
      // Group: services
      /// OTP wrapper clock and APB clock. Free running, initially at 20MHz. Range 20MHz to 800MHz.
      input      wire                         i_clk,
      /// Asynchronous assert, synchronous deassert active low reset.
      input      wire                         i_rst_n,
      /// Clock to the OTP macro used for analog logic. This shall be within 1MHz and 5MHz.
      input      wire                         i_analog_clk,

      // Group: apb
      input      apb_h2d_t                    i_apb,
      output     apb_d2h_t                    o_apb,

      // Group: decommission
      // TODO(kluciani, Remove this interface and use the LCS OTP field instead.)
      /// OTP clear request from eSecure. Active high. Will sequence through and blow all fuses.
      input      logic                        i_otp_clear,
      /// OTP clear acknowledge. Held high once all efuse bits blown in response to a i_otp_clear request.
      output     logic                        o_otp_clear_ack,

      /// Indicate that lifecycle state has been read and output are valid.
      output     logic                        o_lcs_valid,
      // Group: lifecycle_state flags.
      output     logic                        o_lcs_is_chip_wafer_test,
      output     logic                        o_lcs_is_chip_perso,
      output     logic                        o_lcs_is_user_delivery,
      output     logic                        o_lcs_is_user_secured,
      output     logic                        o_lcs_is_user_decommissioned,
      output     logic                        o_lcs_is_chip_field_return,
      output     logic                        o_lcs_is_terminated,
      // Group: dft
      /// Test Scan Test Mode control input
      input      logic                        i_dft_scan_test_mode,
      /// OTP test mode input signal
      input      logic                        i_dft_otp_test_mode,

      // Group: dft_otp
      /// External DFT TAP control of OTP A (address) pins when FSM are bypassed
      input      logic  [OTP_BIT_ADDR_W-1:0]  i_dft_otp_tst_a,
      /// External DFT TAP control of OTP DIN (data in) pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_din,
      /// External DFT TAP control of OTP READEN pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_readen,
      /// External DFT TAP control of OTP CEB pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_ceb,
      /// External DFT TAP control of OTP CLE pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_cle,
      /// External DFT TAP control of OTP DLE pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_dle,
      /// External DFT TAP control of OTP WEB pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_web,
      /// External DFT TAP control of OTP RSTB pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_rstb,
      /// External DFT TAP control of OTP CPUMPEN pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_cpumpen,
      /// External DFT TAP control of OTP PGMEN pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_pgmen,
      /// External DFT TAP control of OTP SELTM pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_seltm,
      /// External DFT TAP control of OTP VDDRDY pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_vddrdy,
      /// External DFT TAP control of OTP CLKEN pin when FSM are bypassed
      input      logic                        i_dft_otp_tst_clken,
      /// External DFT TAP visibility of OTP D (data out) pins when FSM are bypassed
      output     logic  [OTP_DATA_W-1:0]      o_dft_otp_tst_d,
      /// External DFT TAP visibility of OTP lock pin when FSM are bypassed
      output     logic  [OTP_LOCK_DEPTH-1:0]  o_dft_otp_tst_lock,

      inout      wire                         io_otp_vtdo,
      inout      wire                         io_otp_vrefm,
      inout      wire                         io_otp_vpp

    );

// TODO(kluciani, refactor code using parameters for all signals width and similar.)

// Functions
// TODO - Investigate replacing this function with lzc cc_lib module.
function automatic logic [5:0] ffs32 (logic [31:0] ones);
  // find first set (32) - finds the lowest idx of a set bit in a 32b input vector.
  logic [ 5:0] ffs;
  begin
    unique case(ones) inside
      32'b10000000_00000000_00000000_00000000: ffs = 6'd31;
      32'b?1000000_00000000_00000000_00000000: ffs = 6'd30;
      32'b??100000_00000000_00000000_00000000: ffs = 6'd29;
      32'b???10000_00000000_00000000_00000000: ffs = 6'd28;
      32'b????1000_00000000_00000000_00000000: ffs = 6'd27;
      32'b?????100_00000000_00000000_00000000: ffs = 6'd26;
      32'b??????10_00000000_00000000_00000000: ffs = 6'd25;
      32'b???????1_00000000_00000000_00000000: ffs = 6'd24;
      32'b????????_10000000_00000000_00000000: ffs = 6'd23;
      32'b????????_?1000000_00000000_00000000: ffs = 6'd22;
      32'b????????_??100000_00000000_00000000: ffs = 6'd21;
      32'b????????_???10000_00000000_00000000: ffs = 6'd20;
      32'b????????_????1000_00000000_00000000: ffs = 6'd19;
      32'b????????_?????100_00000000_00000000: ffs = 6'd18;
      32'b????????_??????10_00000000_00000000: ffs = 6'd17;
      32'b????????_???????1_00000000_00000000: ffs = 6'd16;
      32'b????????_????????_10000000_00000000: ffs = 6'd15;
      32'b????????_????????_?1000000_00000000: ffs = 6'd14;
      32'b????????_????????_??100000_00000000: ffs = 6'd13;
      32'b????????_????????_???10000_00000000: ffs = 6'd12;
      32'b????????_????????_????1000_00000000: ffs = 6'd11;
      32'b????????_????????_?????100_00000000: ffs = 6'd10;
      32'b????????_????????_??????10_00000000: ffs = 6'd9;
      32'b????????_????????_???????1_00000000: ffs = 6'd8;
      32'b????????_????????_????????_10000000: ffs = 6'd7;
      32'b????????_????????_????????_?1000000: ffs = 6'd6;
      32'b????????_????????_????????_??100000: ffs = 6'd5;
      32'b????????_????????_????????_???10000: ffs = 6'd4;
      32'b????????_????????_????????_????1000: ffs = 6'd3;
      32'b????????_????????_????????_?????100: ffs = 6'd2;
      32'b????????_????????_????????_??????10: ffs = 6'd1;
      32'b????????_????????_????????_???????1: ffs = 6'd0;
      default                                : ffs = 6'd32;
    endcase
    return ffs;
  end
endfunction



logic otp_clear_sync;
axe_tcl_seq_sync i_otp_clear_sync
(
  .i_clk(i_clk),
  .i_rst_n(i_rst_n),
  .i_d (i_otp_clear),
  .o_q (otp_clear_sync)
);



// APB Register Block
// ------------------
// OTP memory window is accessed from register block through abp_otp_req/rsp interface.

  apb_h2d_t apb_otp_req;
  apb_d2h_t apb_otp_rsp;

  otp_wrapper_csr_hw2reg_t hw2reg;
  otp_wrapper_csr_reg2hw_t reg2hw;

  otp_wrapper_csr_reg_top #(
    .StageNum(3)
  ) i_sys_ctrl_otp_reg_top (
    .clk_i(i_clk),
    .rst_ni(i_rst_n),
    .apb_i(i_apb),
    .apb_o(o_apb),
    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .apb_win_o(apb_otp_req),
    .apb_win_i(apb_otp_rsp),
    .devmode_i(1'b1)
  );

// APB COMMAND FSM
// ---------------
// Takes APB commands or clear / decommission requests and breaks these into a series of
// OTP transactions: Read 8b, Writes 1b
// Initialises critical PO state by reading specific OTP bits at startup.

logic [ 3:0] cmd_state_q,     cmd_state_d;

localparam logic [3:0] OTP_CMD_RESET             = 4'b0000;
localparam logic [3:0] OTP_CMD_READ_LCS          = 4'b0001;
localparam logic [3:0] OTP_CMD_END               = 4'b1010;
localparam logic [3:0] OTP_CMD_WAIT_APB          = 4'b1000;
localparam logic [3:0] OTP_CMD_APB_WORD_READ     = 4'b1001;
localparam logic [3:0] OTP_CMD_APB_PRE_WRITE     = 4'b1100;
localparam logic [3:0] OTP_CMD_APB_WRITE         = 4'b1101;
localparam logic [3:0] OTP_CMD_APB_RESP          = 4'b1111;
localparam logic [3:0] OTP_CMD_CLR               = 4'b0111;

// These constants identify critical state bit locations
// TODO(kluciani, Temporary values, update these with real OTP addresses once defined.)
localparam logic [OTP_BIT_ADDR_W-1:0] OTP_CLR_LAST_ADDRESS      = 'h3EF8;
localparam logic [OTP_BIT_ADDR_W-1:0] OTP_LCS_ADDRESS           = 'h0000;

logic [OTP_BIT_ADDR_W-1:0]  cmd_addr_q,      cmd_addr_d;
logic                       cmd_last_q,      cmd_last_d;
logic [5:0]                 cmd_bit_idx_q,   cmd_bit_idx_d;
logic [OTP_DATA_W-1:0]      cmd_rd_data_q,   cmd_rd_data_d;
logic                       read_valid_q,    read_valid_d;
logic                       write_done_q,    write_done_d;
logic                       write_error_q,   write_error_d;
logic                       lock_error_d;
logic                       stky_write_error_q;
logic                       otp_lcs_read_q,  set_otp_lcs_read;
logic [OTP_DATA_W-1:0]      otp_data_q[3],   otp_data_d[3];
logic [OTP_DATA_W-1:0]      otp_data_majority;
logic [OTP_DATA_W-1:0]      otp_lcs_data_d;
logic [OTP_DATA_W-1:0]      otp_lcs_data_q;
logic                       otp_din_value;
logic                       clr_active_q,    clr_active_d;
logic                       clr_done_q,      clr_done_d;
logic [OTP_WORD_ADDR_W-1:0] clr_base_addr_q, clr_base_addr_d;
logic                       apb_sel_q,       apb_read_q;

logic                       otp_busy;           // Indicate that the OTP FSM is active, i.e. not IDLE
logic                       pop_cmd;
logic                       cmd_rd;
logic                       cmd_wr;
logic                       otp_write_error;
logic                       cmd_fsm_clk_en;

always_comb begin
  for (int I = 0; I < 32; I++) begin
    otp_data_majority[I]  = (otp_data_d[2][I] && otp_data_d[1][I]) || (otp_data_d[2][I] && otp_data_d[0][I]) || (otp_data_d[1][I] && otp_data_d[0][I]);
  end // for
end
// TODO(kluciani, This actually returns an APB error only if it occurs on the last written bit. Since we already have the sticky error flag, do we care about this?)
always_comb apb_otp_rsp = '{ pslverr : write_error_q && write_done_q,
                             prdata  : cmd_rd_data_q & {32{read_valid_q}} | {32{apb_read_q}},
                             pready  : read_valid_q || write_done_q || apb_sel_q };

  always_comb begin
    cmd_fsm_clk_en = (cmd_state_q != OTP_CMD_WAIT_APB) || (otp_clear_sync && !clr_done_q) || apb_otp_req.psel || read_valid_q || write_done_q || apb_sel_q;
  end

always_ff @ (posedge i_clk or negedge i_rst_n)
  if (!i_rst_n) begin
    cmd_state_q     <= OTP_CMD_RESET ;
    cmd_addr_q      <= '0;
    cmd_last_q      <= 1'b0;
    cmd_bit_idx_q   <= 6'b000000;
    cmd_rd_data_q   <= 32'h0;
    otp_lcs_data_q  <= 32'h0;
    // host-lock set to `1` after reset as this is the more conservative value
    // (in terms of security).
    otp_lcs_read_q  <= 1'b0;
    read_valid_q    <= 1'b0;
    write_done_q    <= 1'b0;
    write_error_q   <= 1'b0;
    clr_active_q    <= 1'b0;
    clr_done_q      <= 1'b0;
    clr_base_addr_q <= '0;
    apb_sel_q       <= 1'b0;
    apb_read_q      <= 1'b0;
    stky_write_error_q <= 1'b0;
  end
  else if (cmd_fsm_clk_en) begin
    cmd_state_q     <= cmd_state_d;
    cmd_addr_q      <= cmd_addr_d;
    cmd_last_q      <= cmd_last_d;
    cmd_bit_idx_q   <= cmd_bit_idx_d;
    cmd_rd_data_q   <= cmd_rd_data_d;
    otp_lcs_data_q  <= otp_lcs_data_d;
    otp_lcs_read_q  <= otp_lcs_read_q  || set_otp_lcs_read;
    read_valid_q    <= read_valid_d;
    write_done_q    <= write_done_d;
    write_error_q   <= write_error_d || lock_error_d;
    clr_active_q    <= clr_active_d;
    clr_done_q      <= clr_done_d;
    clr_base_addr_q <= clr_base_addr_d;
    apb_sel_q       <= apb_otp_req.psel  && !apb_sel_q && clr_active_q;
    apb_read_q      <= !apb_otp_req.pwrite && clr_active_q;
    stky_write_error_q <= stky_write_error_q || write_error_d;
  end

always_comb begin
  logic [31:0] mask;
  cmd_state_d      = cmd_state_q;
  cmd_addr_d       = cmd_addr_q;
  cmd_last_d       = cmd_last_q;
  set_otp_lcs_read = 1'b0;
  cmd_bit_idx_d    = cmd_bit_idx_q;
  read_valid_d     = 1'b0;
  write_done_d     = 1'b0;
  write_error_d    = 1'b0;
  clr_active_d     = clr_active_q;
  clr_done_d       = clr_done_q;
  clr_base_addr_d  = clr_base_addr_q;
  lock_error_d     = 1'b0;
  cmd_rd_data_d    = cmd_rd_data_q;
  otp_lcs_data_d   = otp_lcs_data_q;

  unique case(cmd_state_q)
    OTP_CMD_RESET :
      if(!otp_busy) begin
        cmd_state_d   = OTP_CMD_READ_LCS;
        cmd_addr_d    = OTP_LCS_ADDRESS;
        cmd_last_d    = 1'b1;
      end
    OTP_CMD_READ_LCS :
      if(pop_cmd) begin
        cmd_state_d      = OTP_CMD_WAIT_APB;
        cmd_addr_d       = '0;
        cmd_last_d       = 1'b1;
        set_otp_lcs_read = 1'b1;
        otp_lcs_data_d   = otp_data_majority;
    end
    OTP_CMD_END : begin
      cmd_state_d = OTP_CMD_WAIT_APB;
    end
    OTP_CMD_WAIT_APB :  begin
      read_valid_d     = 1'b0;
      if(otp_clear_sync && !clr_done_q) begin
        cmd_state_d    = OTP_CMD_CLR;
      end
      else if(apb_otp_req.psel) begin
        cmd_state_d    = OTP_CMD_APB_WORD_READ;
        cmd_addr_d     = {apb_otp_req.paddr[OTP_BYTE_ADDR_W-1:2], 5'b00000};
        cmd_last_d     = 1'b1;
      end
    end
    // Always perform a read, even before a write, to check if some bit is already set to 1.
    OTP_CMD_APB_WORD_READ :
      if(pop_cmd) begin
        cmd_rd_data_d = otp_data_majority;
        cmd_last_d   = 1'b1;
        if (!apb_otp_req.pwrite && !clr_active_q) begin
          cmd_state_d  = OTP_CMD_APB_RESP;
          read_valid_d = 1'b1;
        end
        else if (apb_otp_req.pwrite && reg2hw.control.softlock.q) begin
          write_done_d = 1'b1;
          lock_error_d = 1'b1;
          cmd_state_d  = OTP_CMD_APB_RESP;
        end
        else begin
          cmd_state_d  = OTP_CMD_APB_PRE_WRITE;
        end
      end

    OTP_CMD_APB_PRE_WRITE : begin
      // Don't program bits to 1 if they have already been set in the past.
      cmd_rd_data_d = (clr_active_q ? '1 : (apb_otp_req.pwdata & { {8{apb_otp_req.pstrb[3]}}, {8{apb_otp_req.pstrb[2]}},
                                                                   {8{apb_otp_req.pstrb[1]}}, {8{apb_otp_req.pstrb[0]}} })) & (~cmd_rd_data_q);
      cmd_bit_idx_d = ffs32(cmd_rd_data_d);
      if (cmd_bit_idx_d[5] && !clr_active_q) begin
        cmd_state_d = OTP_CMD_END;
        write_done_d = 1'b1;
      end
      else if (cmd_bit_idx_d[5]) begin
        cmd_state_d = OTP_CMD_CLR;
      end
      else begin
        mask        = 32'hfffffffe << cmd_bit_idx_d ; // clear bits set to 1 from LSbit to MSbit, one at a time
        cmd_last_d  = !(|(cmd_rd_data_d & mask));
        cmd_state_d = OTP_CMD_APB_WRITE;
        if (!clr_active_q) begin
          cmd_addr_d     = OTP_BIT_ADDR_W'({apb_otp_req.paddr[OTP_BYTE_ADDR_W-1:2], 5'b00000} + cmd_bit_idx_d);
        end
        else begin
          cmd_addr_d     = OTP_BIT_ADDR_W'({clr_base_addr_q, 5'b00000} + cmd_bit_idx_d);
        end
      end
    end

    OTP_CMD_APB_WRITE : begin
      if(pop_cmd) begin
        write_error_d = otp_write_error;
        cmd_rd_data_d = cmd_rd_data_q & ~{ 32'h00000001 << cmd_bit_idx_q};
        cmd_bit_idx_d = ffs32(cmd_rd_data_d);
        mask        = 32'hfffffffe << cmd_bit_idx_d ;
        cmd_last_d  = !(|(cmd_rd_data_d & mask));
        if (cmd_last_q && !clr_active_q) begin
          cmd_state_d = OTP_CMD_APB_RESP;
          write_done_d = 1'b1;
        end
        else if (cmd_last_q) begin
          cmd_state_d = OTP_CMD_CLR;
        end
        else begin
          cmd_state_d = OTP_CMD_APB_WRITE;
          if (clr_active_q)
            cmd_addr_d     = OTP_BIT_ADDR_W'({clr_base_addr_q, 5'b00000} + {9'h000, cmd_bit_idx_d});
          else
            cmd_addr_d     = OTP_BIT_ADDR_W'({apb_otp_req.paddr[OTP_BYTE_ADDR_W-1:2], 5'b00000} + cmd_bit_idx_d);
        end
      end
    end

    OTP_CMD_APB_RESP : begin
      cmd_state_d = OTP_CMD_END;
    end

    OTP_CMD_CLR : begin
      if (!clr_active_q) begin
        // Start of sequence
        clr_active_d = otp_clear_sync;             // Glitch check - this forces 2 cycles of i_otp_clear
        clr_base_addr_d = '0;
        cmd_addr_d = '0;
        if (otp_clear_sync)
          cmd_state_d = OTP_CMD_APB_WORD_READ;
        else
          cmd_state_d = OTP_CMD_END;
        cmd_last_d     = 1'b0;
      end
      else if ({clr_base_addr_q, 5'b00000} ==  (OTP_CLR_LAST_ADDRESS & 15'h7FE0)) begin
        // End of sequence
        clr_base_addr_d = '0;
        cmd_state_d  = OTP_CMD_END;
        clr_active_d = 1'b0;
        clr_done_d   = 1'b1;
      end
      else begin
        // Mid Sequence
        clr_base_addr_d = clr_base_addr_q + 'd1;
        cmd_addr_d      = {clr_base_addr_d, 5'b00000};
        cmd_state_d     = OTP_CMD_APB_WORD_READ;
        cmd_last_d      = 1'b0;
      end
    end
    default: begin
      cmd_state_d = OTP_CMD_RESET;
    end

    endcase
  end

  always_comb hw2reg.status.prgm_error.d = stky_write_error_q;
  always_comb hw2reg.status.clear_req.d = otp_clear_sync;
  always_comb hw2reg.status.clear_done.d = clr_done_q;
  always_comb hw2reg.status.clear_active.d = clr_active_q;

  always_comb o_otp_clear_ack = clr_done_q;

  always_comb cmd_rd = (cmd_state_q == OTP_CMD_READ_LCS) ||
                       (cmd_state_q == OTP_CMD_APB_WORD_READ);

  always_comb cmd_wr = (cmd_state_q == OTP_CMD_APB_WRITE);

  // LifeCycle State decoding
  always_comb begin
    o_lcs_is_chip_wafer_test      = 1'b0;
    o_lcs_is_chip_perso           = 1'b0;
    o_lcs_is_user_delivery        = 1'b0;
    o_lcs_is_user_secured         = 1'b0;
    o_lcs_is_user_decommissioned  = 1'b0;
    o_lcs_is_chip_field_return    = 1'b0;
    o_lcs_is_terminated           = 1'b0;

    // Don't check bits 15:8 as they are reserved.
    unique case ({otp_lcs_data_q[31:16], otp_lcs_data_q[7:0]})
      {LCS_CHIP_WAFER_TEST,     LCS_CHIP_WAFER_TEST,     OTP_MAGIC_WAFER_TEST} : o_lcs_is_chip_wafer_test     = 1'b1;
      {LCS_CHIP_PERSO,          LCS_CHIP_PERSO,          OTP_MAGIC}            : o_lcs_is_chip_perso          = 1'b1;
      {LCS_USER_DELIVERY,       LCS_USER_DELIVERY,       OTP_MAGIC}            : o_lcs_is_user_delivery       = 1'b1;
      {LCS_USER_SECURED,        LCS_USER_SECURED,        OTP_MAGIC}            : o_lcs_is_user_secured        = 1'b1;
      {LCS_USER_DECOMMISSIONED, LCS_USER_DECOMMISSIONED, OTP_MAGIC}            : o_lcs_is_user_decommissioned = 1'b1;
      {LCS_CHIP_FIELD_RETURN,   LCS_CHIP_FIELD_RETURN,   OTP_MAGIC}            : o_lcs_is_chip_field_return   = 1'b1;
      {LCS_TERMINATED,          LCS_TERMINATED,          OTP_MAGIC}            : o_lcs_is_terminated          = 1'b1;
      default                                                                  : /* Keep default: all flags are 0. */;
    endcase
  end

  always_comb o_lcs_valid = otp_lcs_read_q;

// OTP Memory FSM
// Takes requests from APB transaction FSM and sequences through state machines to drive OTP memory pins.

localparam int unsigned OTP_MEM_STATE_W = 11;
logic [OTP_MEM_STATE_W-1:0] state_q, state_d;

localparam integer STATE_CEB     = 10;
localparam integer STATE_RSTB    = 9;
localparam integer STATE_DLE     = 4;
localparam integer STATE_READEN  = 3;
localparam integer STATE_PGMEN   = 2;
localparam integer STATE_CPUMPEN = 1;
localparam integer STATE_WEB     = 0;

// TODO(kluciani, refactor this code, add a table as a comment and localparams for different fields (top, mid, low))
localparam logic [OTP_MEM_STATE_W-1:0] RESET   = 'b11_0000_00001;
localparam logic [OTP_MEM_STATE_W-1:0] INIT_P0 = 'b01_0000_00001;
localparam logic [OTP_MEM_STATE_W-1:0] INIT_P1 = 'b00_0000_00001;
localparam logic [OTP_MEM_STATE_W-1:0] INIT_P2 = 'b01_0010_00001;
localparam logic [OTP_MEM_STATE_W-1:0] IDLE    = 'b11_0100_00001;
localparam logic [OTP_MEM_STATE_W-1:0] RD_P0   = 'b01_0100_00001;
localparam logic [OTP_MEM_STATE_W-1:0] RD_P1   = 'b01_0000_01001;
localparam logic [OTP_MEM_STATE_W-1:0] RD_P2   = 'b01_0010_01001;
localparam logic [OTP_MEM_STATE_W-1:0] RD_P3   = 'b01_1000_00001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P0   = 'b01_0001_00001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P1   = 'b01_0101_00001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P2   = 'b01_0011_10001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P3   = 'b01_0011_10000;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P4   = 'b01_0101_10001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P5   = 'b01_0011_00001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P6   = 'b01_0001_00101;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P7   = 'b01_0001_00111;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P8   = 'b01_0001_00110;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P9   = 'b01_0011_00111;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P10  = 'b01_0011_00101;
localparam logic [OTP_MEM_STATE_W-1:0] WR_P11  = 'b01_0111_00001;
localparam logic [OTP_MEM_STATE_W-1:0] WR_V0   = 'b01_0110_00001;

logic [15:0]                count_q,       count_d;
logic [15:0]                rdhld_count_q, rdhld_count_d;
logic [15:0]                wrhld_count_q, wrhld_count_d;
logic                       timer_expired;
logic                       rdhld_expired;
logic                       wrhld_expired;
logic                       initialised_q, initialised_d;
logic [OTP_BIT_ADDR_W-1:0]  otp_addr_q,    otp_addr_d;
logic [ 4:0]                num_writes_q, num_writes_d;
logic [ 31:0]               otp_read_data;
logic                       wr_successful;
logic                       fsm_clk_en;
logic [ 1:0]                rd_stgs_q, rd_stgs_d;

localparam logic [4:0] MIN_WRITES = 'd2;
localparam logic [4:0] MAX_WRITES = 'd16;

always_comb otp_busy = state_q != IDLE;
always_comb otp_din_value = 1'b1; // TODO(kluciani, we might want to set this to 0 to prevent writes to specific address locations when clr_active_q = 1?)
always_comb timer_expired = !(|count_q);
always_comb rdhld_expired = !(|rdhld_count_q);
always_comb wrhld_expired = !(|wrhld_count_q);


always_comb fsm_clk_en = timer_expired || (state_q == IDLE && (cmd_rd || cmd_wr));

always_ff @ (posedge i_clk or negedge i_rst_n)
if (!i_rst_n) begin
  state_q <= RESET;
  count_q <= 'd200; // tCS+tPOR+tPU+TPOR = 2us = 200 cycles @ 100MHz
  rdhld_count_q <= '0;
  wrhld_count_q <= '0;
  otp_addr_q    <= '0;
  otp_data_q    <= {'0, '0, '0};
  initialised_q <= 1'b0;
  num_writes_q  <= '0;
  rd_stgs_q     <= '0;
end
else begin
  count_q <= count_d;
  rdhld_count_q <= rdhld_count_d;
  wrhld_count_q <= wrhld_count_d;
  if (fsm_clk_en) begin
    state_q <= state_d;
    otp_addr_q    <= otp_addr_d;
    otp_data_q    <= otp_data_d;
    initialised_q <= initialised_d;
    num_writes_q  <= num_writes_d;
    rd_stgs_q     <= rd_stgs_d;
  end
end


always_comb begin

  state_d       = state_q;
  initialised_d = initialised_q;
  pop_cmd       = 1'b0;
  otp_addr_d    = otp_addr_q;
  otp_data_d    = otp_data_q;
  otp_write_error = 1'b0;
  num_writes_d  = num_writes_q;
  wr_successful = 1'b0;
  rd_stgs_d     = rd_stgs_q;

  if(!timer_expired)
    count_d     = count_q - 'd1;
  else
    count_d     = '0;

  if(!rdhld_expired)
    rdhld_count_d = rdhld_count_q - 'd1;
  else
    rdhld_count_d = '0;

  if(!wrhld_expired)
    wrhld_count_d = wrhld_count_q - 'd1;
  else
    wrhld_count_d = '0;

  unique case(state_q)

    RESET   :
      if (timer_expired) begin
        state_d = INIT_P0;
        count_d = reg2hw.tinit_p0;
      end
    INIT_P0 :
      if (timer_expired) begin
        state_d = INIT_P1;
        count_d = reg2hw.tinit_p1;
      end
    INIT_P1 :
      if (timer_expired) begin
        if (!initialised_q) begin
          state_d = INIT_P2;
          count_d = reg2hw.tinit_p2;
        end
        else if (cmd_rd && rdhld_expired) begin // rdhld_expired used to satisfy minimum READEN LOW pulse width
          state_d = RD_P0;
          count_d = reg2hw.trd_p0;
          otp_addr_d = cmd_addr_q;
        end
        else if (cmd_wr && wrhld_expired) begin
          state_d = WR_P0;
          count_d = reg2hw.twr_p0;
        end
      end
    INIT_P2 : if (timer_expired) begin
                state_d = IDLE;
                initialised_d = 1'b1;
              end
    IDLE :    if (cmd_rd || cmd_wr) begin
                state_d = INIT_P0;
                count_d = reg2hw.tinit_p0;
                otp_addr_d = cmd_addr_q;
              end
    RD_P0 :   if (timer_expired) begin
                state_d = RD_P1;
                count_d = reg2hw.trd_p1;
              end
    RD_P1 :   if (timer_expired) begin
                state_d = RD_P2;
                count_d = reg2hw.trd_p2;
                rd_stgs_d = 2'b10;
              end
    RD_P2 :   if (timer_expired) begin
                otp_data_d[rd_stgs_q] = otp_read_data;
                rd_stgs_d = rd_stgs_q - 2'b01;
                if (rd_stgs_q == '0) begin
                  state_d = RD_P3;
                  count_d = reg2hw.trd_p3;
                end
              end
    RD_P3 :   if (timer_expired) begin
                // Read-verify part of write operation
                if (cmd_wr) begin
                  // Even though write address is bit-aligned, the read address is treated as word-aligned
                  // (bits 4 to 0 are always considered 0 by the OTP read circuitry) hence during
                  // verify-read we must extract the bit at the programmed index.
                  wr_successful = otp_data_majority[cmd_bit_idx_q[4:0]]; // TODO(kluciani, Do we really want to use majority voting here?)
                  // Move to WR_P6 (next couple of write pulses) if the write
                  // was unsuccessful and we can still apply write pulses, or
                  // if we still need to achieve the minimum number of write pulses.
                  if ((!wr_successful && (num_writes_q < MAX_WRITES)) || (num_writes_q < MIN_WRITES)) begin
                    state_d = WR_P6;
                    count_d = reg2hw.twr_p6;
                  // The write operation is over if either it is successful or we performed the maximum
                  // number of allowed write pulses.
                  end else if ((wr_successful || (num_writes_q >= MAX_WRITES))) begin
                    // Move to WR_P0 if there is another command to perform and smart programming is enabled.
                    if (!cmd_last_q && reg2hw.control.smart_en.q) begin
                      state_d = WR_P0;
                      count_d = reg2hw.twr_p0;
                      otp_write_error = !wr_successful;
                      otp_addr_d = cmd_addr_q;
                    // Move to INIT_P2 otherwise.
                    end else begin
                      state_d = INIT_P2;
                      count_d = reg2hw.tinit_p2;
                    end
                    pop_cmd = 1'b1;
                  end
                // End of read operation
                end else if (cmd_rd) begin
                  if(cmd_last_q) begin
                    state_d = INIT_P2;
                    count_d = reg2hw.tinit_p2;
                    // TODO(kluciani, Can we get rid of rdhld_count and wrhld_count?)
                    rdhld_count_d = reg2hw.trr_hld;
                    if (wrhld_count_q < reg2hw.trw_hld)
                      wrhld_count_d = reg2hw.trw_hld;
                  // back to back read operations
                  end else begin
                    state_d = RD_P0;
                    count_d = reg2hw.trd_p0;
                  end
                  pop_cmd = 1'b1;
                end
              end
    WR_P0 :   if (timer_expired) begin
                state_d = WR_P1;
                count_d = reg2hw.twr_p1;
                otp_addr_d = cmd_addr_q;
              end
    WR_P1:   if (timer_expired) begin
                state_d = WR_P2;
                count_d = reg2hw.twr_p2;
              end
    WR_P2 :   if (timer_expired) begin
                state_d = WR_P3;
                count_d = reg2hw.twr_p3;
              end
    WR_P3 :   if (timer_expired) begin
                state_d = WR_P4;
                count_d = reg2hw.twr_p4;
              end
    WR_P4 :   if (timer_expired) begin
                num_writes_d = '0;
                state_d = WR_P5;
                count_d = reg2hw.twr_p5;
              end
    WR_P5 :   if (timer_expired) begin
                state_d = WR_P6;
                count_d = reg2hw.twr_p6;
              end
    WR_P6 :   if (timer_expired) begin
                state_d = WR_P7;
                count_d = reg2hw.twr_p7;
              end
    WR_P7 :   if (timer_expired) begin
                state_d = WR_P8;
                count_d = reg2hw.twr_p8;
              end
    WR_P8 :   if (timer_expired) begin
                state_d = WR_P9;
                count_d = reg2hw.twr_p9;
              end
    WR_P9 :   if (timer_expired) begin
                state_d = WR_P10;
                count_d = reg2hw.twr_p10;
              end
    WR_P10:   if (timer_expired) begin
                  num_writes_d = num_writes_q + 'd1;
                  state_d = WR_P11;
                  count_d = reg2hw.twr_p11;
              end
    WR_P11:   if (timer_expired) begin
                // Number of write pulses must be multiple of 2
                if (num_writes_q[0]) begin
                  state_d = WR_P6;
                  count_d = reg2hw.twr_p6;
                end
                // 2 write pulses performed, move to first write-verify state
                else begin
                  state_d = WR_V0;
                  count_d = reg2hw.twr_v0;
                end
              end
      WR_V0:  if (timer_expired) begin
                  state_d = RD_P1;
                  count_d = reg2hw.trd_p1;
              end
    default:  begin
              end
    endcase
  end


  logic                           otp_ceb;
  logic                           otp_cle;
  logic [OTP_BIT_ADDR_W-1:0]      otp_addr;
  logic                           otp_dle;
  logic                           otp_pgmen;
  logic                           otp_readen;
  logic                           otp_rstb;
  logic                           otp_web;
  logic                           otp_cpumpen;
  logic                           otp_seltm;
  logic                           otp_din;
  logic [OTP_DATA_W-1:0]          otp_d;
  logic                           otp_vddrdy;
  logic                           otp_clken;

  always_comb begin
    if (i_dft_otp_test_mode && !i_dft_scan_test_mode ) begin
      otp_addr           = i_dft_otp_tst_a;
      otp_ceb            = i_dft_otp_tst_ceb;
      otp_cle            = i_dft_otp_tst_cle;
      otp_dle            = i_dft_otp_tst_dle;
      otp_pgmen          = i_dft_otp_tst_pgmen;
      otp_readen         = i_dft_otp_tst_readen;
      otp_rstb           = i_dft_otp_tst_rstb;
      otp_web            = i_dft_otp_tst_web;
      otp_cpumpen        = i_dft_otp_tst_cpumpen;
      otp_seltm          = i_dft_otp_tst_seltm;
      o_dft_otp_tst_d    = otp_d;
      otp_din            = i_dft_otp_tst_din;
      o_dft_otp_tst_lock = hw2reg.lock.d;
      otp_read_data      = '1;
      otp_vddrdy         = i_dft_otp_tst_vddrdy;
      otp_clken          = i_dft_otp_tst_clken;
    end
    else begin
      otp_addr           = otp_addr_q;
      otp_ceb            = state_q[STATE_CEB];
      otp_cle            = 1'b0;
      otp_dle            = state_q[STATE_DLE];
      otp_pgmen          = state_q[STATE_PGMEN];
      otp_readen         = state_q[STATE_READEN];
      otp_rstb           = state_q[STATE_RSTB];
      otp_web            = state_q[STATE_WEB];
      otp_cpumpen        = state_q[STATE_CPUMPEN];
      otp_seltm          = 1'b0;
      o_dft_otp_tst_d    = 32'h00000000;
      otp_din            = otp_din_value;
      o_dft_otp_tst_lock = OTP_LOCK_DEPTH'('1);
      otp_read_data      = otp_d;
      otp_vddrdy         = 1'b0;  // Test input , must be 0 in functional mode.
      otp_clken          = 1'b1;  // Always use chopper in reference voltage.
    end
  end

wire vdd = 1'b1;
wire vddio = 1'b1;
wire gnd = 1'b0;

// spyglass disable_block AsyncPinsOfLibraryCells-ML
  sf_otp_wrapper
  `ifndef SYNTHESIS
  #(
    //.MEM_FILE1("OTP_memory.din"),
    //.MEM_FILE2("OTP_memory.din"),
    .OTP_ADDR_W (OTP_BIT_ADDR_W),
    .OTP_DATA_W (OTP_DATA_W),
    .OTP_LOCK_DEPTH (OTP_LOCK_DEPTH)
  )
  `endif
  u_otp_wrapper (
    //.VDD(vdd),
    //.VDDIO(vddio),
    //.GND(gnd),
    .i_otp_clk(i_analog_clk),
    .i_otp_rstb(otp_rstb),
    .i_otp_addr(otp_addr),
    .i_otp_ceb(otp_ceb),
    .i_otp_cle(otp_cle),
    .i_otp_cpumpen(otp_cpumpen),
    .i_otp_pgmen(otp_pgmen),
    .i_otp_dle(otp_dle),
    .i_otp_din(otp_din),
    .i_otp_readen(otp_readen),
    .i_otp_web(otp_web),
    .i_otp_vddrdy(otp_vddrdy),
    .i_otp_clken(otp_clken),
    .o_otp_dout(otp_d),
    .o_otp_lock(hw2reg.lock.d),
    .io_otp_vtdo(io_otp_vtdo),
    .io_otp_vrefm(io_otp_vrefm),
    .io_otp_vpp(io_otp_vpp)
  );
// spyglass enable_block AsyncPinsOfLibraryCells-ML

endmodule
