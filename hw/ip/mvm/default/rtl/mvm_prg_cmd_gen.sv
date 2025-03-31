// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DP CMD generation for the programming (weight loading) side of the mvm dp.
// Translates CMDs from PRG cmdBlock into an address stream which determines where the data from the IFDW stream goes inside the IMC_banks
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_PRG_CMD_AIC_GEN_SV
`define MVM_PRG_CMD_AIC_GEN_SV

module mvm_prg_cmd_gen
  import imc_bank_pkg::*;
  import mvm_pkg::*;
(
  input wire i_clk,
  input logic i_rst_n,

  // Command from CMDBlock
  output logic cmd_done,
  input mvm_prg_cmd_t cmd_data,
  input logic cmd_vld,
  output logic cmd_rdy,

  // DP-CMD stream
  output mvm_prg_dp_cmd_t prg_dp_cmd_tdata,
  output logic            prg_dp_cmd_tvalid,
  input  logic            prg_dp_cmd_tready,
  output logic            prg_dp_cmd_tlast,
  input  logic            prg_dp_done,

  // Err sig
  output logic err_prg_illegal_cmd_opcode,
  output logic err_prg_illegal_weight_set,
  output logic err_prg_row_offset_size_overflow,
  output logic err_prg_col_offset_size_overflow,

  // State observation
  output mvmprg_csr_reg_pkg::mvmprg_csr_hw2reg_cmdgen_status_reg_t cmdgen_status
);

  logic [$clog2(MVM_NR_OUTPUT_PW)-1 : 0] col_offset_pw, col_size_pw, col_target;
  logic [$clog2(MVM_NR_INPUT_PW)-1:0] row_offset_pw, row_size_pw;
  logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] prg_weight_set;
  logic count_enable;
  logic state, next_state;
  logic col_end, row_end, block_end;
  prog_counter_t prog_counter_q, prog_counter_d;

  // Reg to sample incoming cmd data from cmd block
  mvm_prg_cmd_t cmd_data_reg;

  localparam bit Idle = 0;
  localparam bit Write = 1;

  always_comb cmd_done = prg_dp_done;

  // Extract cmdBlock cmd_data to useful signals. Not that fields are bytes, but useful data is not the full byte of each field
  always_comb prg_weight_set = cmd_data_reg.a_s;
  always_comb row_offset_pw = cmd_data_reg.a_u_pw;
  always_comb col_offset_pw = cmd_data_reg.a_t_pw;
  always_comb row_size_pw = cmd_data_reg.wb_u_pw;
  always_comb col_size_pw = cmd_data_reg.wb_t_pw;

  // Check that prog fiels is correct
  always_comb err_prg_illegal_cmd_opcode = (state == Write) &&
    ((cmd_data_reg.prog.rsvd != 4'd0) || !(cmd_data_reg.prog.prog_mode inside {UuT, TUu, UTu}));

  // Check that weight set byte is legal
  always_comb err_prg_illegal_weight_set = (state == Write) &&
    (cmd_data_reg.a_s >= IMC_NB_WEIGHT_SETS);
  // Detect overflow caused by infeasible offset and size combinations
  always_comb err_prg_row_offset_size_overflow = (state == Write) &&
    ((row_size_pw + row_offset_pw) >= MVM_NR_INPUT_PW);
  always_comb err_prg_col_offset_size_overflow = (state == Write) &&
    ((col_size_pw + col_offset_pw) >= MVM_NR_OUTPUT_PW);

  localparam int unsigned RowEnableExpansion = PW_LEN / IMC_NB_COLS_PER_BANK;
  logic [RowEnableExpansion-1:0] we_bits;
  logic [MVM_NB_IMC_BANKS-1:0] imc_prg_we;
  always_comb we_bits = {RowEnableExpansion{count_enable}};

  // Fill prg_dp_cmd_tdata struct
  always_comb col_target = col_offset_pw + prog_counter_q.col;
  // col_value to RowEnableExpansion(2)-hot write_enable
  always_comb imc_prg_we = we_bits << (RowEnableExpansion*(col_target)) | '0;
  always_comb prg_dp_cmd_tdata.imc_prg_we = imc_prg_we | (cmd_data.prog.broadcast ?
                                                         (imc_prg_we << (MVM_NB_IMC_BANKS/2)) :
                                                         ({MVM_NB_IMC_BANKS{1'b0}})
                                                         );
  always_comb prg_dp_cmd_tdata.imc_prg_row = row_offset_pw * PW_LEN + prog_counter_q.row;
  always_comb prg_dp_cmd_tdata.imc_prg_weight_set = prg_weight_set;

  always_comb begin : prg_cmd_gen_fsm

    next_state = state;
    cmd_rdy = 1'b0;
    prg_dp_cmd_tlast = 1'b0;
    count_enable = 1'b0;
    prg_dp_cmd_tvalid = 1'b0;
    unique case (state)
      // Wait for new cmd
      Idle: begin
        // Valid cmd indicates new cmd
        if (cmd_vld) begin
          next_state = Write;
        end
        // When in Idle, we can always immediatly accept a cmd
        cmd_rdy = 1'b1;
      end
      Write: begin
        count_enable = prg_dp_cmd_tready;
        prg_dp_cmd_tvalid = 1'b1;
        if (row_end && col_end) begin
          prg_dp_cmd_tlast = 1'b1;
          if (prg_dp_cmd_tready) begin
            cmd_rdy = 1'b1;
            if (!cmd_vld) next_state = Idle;
          end
        end
      end
      default: begin
        next_state = Idle;
      end
    endcase
  end

  // End flags
  always_comb col_end = prog_counter_q.col == col_size_pw;
  always_comb row_end = prog_counter_q.row == row_size_pw * PW_LEN + (PW_LEN - 1);
  always_comb block_end = prog_counter_q.row.block_row == (PW_LEN - 1);

  always_comb begin : addr_counter_comb_proc
    prog_counter_d = prog_counter_q;
    unique case (cmd_data_reg.prog.prog_mode)
      default: // UuT
      begin
        if (col_end) begin
          prog_counter_d.col = '0;
          if (row_end) begin
            prog_counter_d.row = '0;
          end else begin
            prog_counter_d.row = prog_counter_q.row + 1;
          end
        end else begin
          prog_counter_d.col = prog_counter_q.col + 1;
        end
      end
      TUu:
      begin
        if (row_end) begin
          prog_counter_d.row = '0;
          if (col_end) begin
            prog_counter_d.col = '0;
          end else begin
            prog_counter_d.col = prog_counter_q.col + 1;
          end
        end else begin
          prog_counter_d.row = prog_counter_q.row + 1;
        end
      end
      UTu:
      begin
        if (block_end) begin
          prog_counter_d.row.block_row = '0;
          if (col_end) begin
            prog_counter_d.col = '0;
            if (row_end) begin
              prog_counter_d.row.block_index = '0;
            end else begin
              // Equivalent to prog_counter_d.row.block_row = prog_counter_q.row.block_row + 'd64
              prog_counter_d.row.block_index = prog_counter_q.row.block_index + 1;
            end
          end else begin
            prog_counter_d.col = prog_counter_q.col + 1;
          end
        end else begin
          prog_counter_d.row.block_row = prog_counter_q.row.block_row + 1;
        end
      end
    endcase
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : addr_counter_seq_proc
    if (!i_rst_n)          prog_counter_q <= '0;
    else if (count_enable) prog_counter_q <= prog_counter_d;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : cmd_data_sampling
    if (!i_rst_n) begin
      cmd_data_reg <= 0;
    end else begin
      if (cmd_vld && cmd_rdy) begin
        cmd_data_reg <= cmd_data;
      end
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      state <= Idle;
    end else begin
      state <= next_state;
    end
  end

  /////////////
  // State observation
  always_comb cmdgen_status = '{
          row_counter: '{d: prog_counter_q.row},
          col_counter_pw: '{d: prog_counter_q.col},
          prog_write_ena: '{d: prg_dp_cmd_tdata.imc_prg_we},
          prog_row: '{d: prg_dp_cmd_tdata.imc_prg_row},
          prog_wset: '{d: prg_dp_cmd_tdata.imc_prg_weight_set},
          fsm_state: '{d: state}
      };

  /////////////
  // Assertions
`ifdef ASSERTIONS_ON

  property prg_illegal_cmd_opcode;
    @(posedge i_clk) disable iff (!i_rst_n) not err_prg_illegal_cmd_opcode;
  endproperty
  property prg_illegal_weight_set;
    @(posedge i_clk) disable iff (!i_rst_n) not err_prg_illegal_weight_set;
  endproperty
  property prg_row_offset_size_overflow;
    @(posedge i_clk) disable iff (!i_rst_n) not err_prg_row_offset_size_overflow;
  endproperty
  property prg_col_offset_size_overflow;
    @(posedge i_clk) disable iff (!i_rst_n) not err_prg_col_offset_size_overflow;
  endproperty
  // verilog_lint: waive-start numeric-format-string-style
  // verilog_lint: waive-start line-length
  assert property (prg_illegal_cmd_opcode)
  else
    $error(
        "The received cmd opcode = %0h is illegal, only 0 is supported. This is only fatal if the lsb bit is not 0. As internal opcode is only 1b, lsb of given opcode is used.",
        cmd_data.prog.rsvd);

  assert property (prg_illegal_weight_set)
  else
    $error(
        "The received weight sets = %0h is larger than the actual number of weight sets in the imc banks = %0h. This is not fatal. Only the 2 lsb bits from the weight set byte are used.",
        cmd_data.a_s, IMC_NB_WEIGHT_SETS);

  assert property (prg_row_offset_size_overflow)
  else
    $error(
        "row offset and size add up to a value larger than NR_INPUT_PWs which causes an unsupported overlfow");
  assert property (prg_col_offset_size_overflow)
  else
    $error(
        "col offset and size add up to a value larger than NR_OUTPUT_PWs which causes an unsupported overlfow");
  // verilog_lint: waive-stop line-length
  // verilog_lint: waive-stop numeric-format-string-style
`endif  // ASSERTIONS_ON
endmodule

`endif  // MVM_PRG_CMD_AIC_GEN_SV
