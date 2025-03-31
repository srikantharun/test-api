// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Yannick Casamatta - Thales
// Date: 09/01/2024


module cva6v_cva6_rvfi
  import cva6v_ariane_pkg::*;
#(
    parameter cva6v_config_pkg::cva6_cfg_t CVA6Cfg = cva6v_config_pkg::cva6_cfg_empty,
    parameter type rvfi_instr_t = logic,
    parameter type rvfi_csr_t = logic,
    parameter type rvfi_probes_instr_t = logic,
    parameter type rvfi_probes_csr_t = logic,
    parameter type rvfi_probes_t = logic

) (

    input logic clk_i,
    input logic rst_ni,

    input rvfi_probes_t rvfi_probes_i,
    output rvfi_instr_t [CVA6Cfg.NrCommitPorts-1:0] rvfi_instr_o,
    output rvfi_csr_t rvfi_csr_o

);

  localparam logic [CVA6Cfg.XLEN-1:0] IsaCode =
    (CVA6Cfg.XLEN'(CVA6Cfg.RVA) << 0)   // A - Atomic Instructions extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVB) << 1)  // C - Bitmanip extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVC) << 2)  // C - Compressed extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVD) << 3)  // D - Double precision floating-point extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVF) << 5)  // F - Single precision floating-point extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVH) << 7)  // H - Hypervisor extension
  | (CVA6Cfg.XLEN'(1) << 8)  // I - RV32I/64I/128I base ISA
  | (CVA6Cfg.XLEN'(1) << 12)  // M - Integer Multiply/Divide extension
  | (CVA6Cfg.XLEN'(0) << 13)  // N - User level interrupts supported
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVS) << 18)  // S - Supervisor mode implemented
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVU) << 20)  // U - User mode implemented
  | (CVA6Cfg.XLEN'(CVA6Cfg.RVV) << 21)  // V - Vector extension
  | (CVA6Cfg.XLEN'(CVA6Cfg.NSX) << 23)  // X - Non-standard extensions present
  | ((CVA6Cfg.XLEN == 64 ? 2 : 1) << CVA6Cfg.XLEN - 2);  // MXL

  localparam logic [CVA6Cfg.XLEN-1:0] hart_id_i = '0;

  localparam logic [63:0] SMODE_STATUS_READ_MASK = cva6v_ariane_pkg::smode_status_read_mask(CVA6Cfg);

  logic flush;
  logic issue_instr_ack;
  logic fetch_entry_valid;
  logic [31:0] instruction;
  logic is_compressed;

  logic [CVA6Cfg.TRANS_ID_BITS-1:0] issue_pointer;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0] commit_pointer;

  logic flush_unissued_instr;
  logic decoded_instr_valid;
  logic decoded_instr_ack;

  logic [CVA6Cfg.XLEN-1:0] rs1_forwarding;
  logic [CVA6Cfg.XLEN-1:0] rs2_forwarding;

  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] commit_instr_pc;
  fu_op [CVA6Cfg.NrCommitPorts-1:0] commit_instr_op;
  logic [CVA6Cfg.NrCommitPorts-1:0][REG_ADDR_SIZE-1:0] commit_instr_rs1;
  logic [CVA6Cfg.NrCommitPorts-1:0][REG_ADDR_SIZE-1:0] commit_instr_rs2;
  logic [CVA6Cfg.NrCommitPorts-1:0][REG_ADDR_SIZE-1:0] commit_instr_rd;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] commit_instr_result;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] commit_instr_valid;

  logic [CVA6Cfg.XLEN-1:0] ex_commit_cause;
  logic ex_commit_valid;

  cva6v_riscv::priv_lvl_t priv_lvl;

  logic [CVA6Cfg.XLEN-1:0] lsu_ctrl_vaddr;
  fu_t lsu_ctrl_fu;
  logic [(CVA6Cfg.XLEN/8)-1:0] lsu_ctrl_be;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] lsu_ctrl_trans_id;

  logic [((CVA6Cfg.CvxifEn || CVA6Cfg.RVV) ? 5 : 4)-1:0][CVA6Cfg.XLEN-1:0] wbdata;
  logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack;
  logic [CVA6Cfg.PLEN-1:0] mem_paddr;
  logic debug_mode;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] wdata;

  logic [CVA6Cfg.XLEN-1:0] lsu_addr;
  logic [(CVA6Cfg.XLEN/8)-1:0] lsu_rmask;
  logic [(CVA6Cfg.XLEN/8)-1:0] lsu_wmask;
  logic [CVA6Cfg.TRANS_ID_BITS-1:0] lsu_addr_trans_id;

  cva6v_riscv::pmpcfg_t [15:0] pmpcfg_q, pmpcfg_d;

  rvfi_probes_csr_t   csr;
  rvfi_probes_instr_t instr;

  always_comb begin
    csr   = '0;
    instr = '0;

    if ($bits(rvfi_probes_i.instr) == $bits(instr)) begin
      instr = rvfi_probes_i.instr;
    end

    if ($bits(rvfi_probes_i.csr) == $bits(csr)) begin
      csr = rvfi_probes_i.csr;
    end

  end


  assign flush = instr.flush;
  assign issue_instr_ack = instr.issue_instr_ack;
  assign fetch_entry_valid = instr.fetch_entry_valid;
  assign instruction = instr.instruction;
  assign is_compressed = instr.is_compressed;

  assign issue_pointer = instr.issue_pointer;
  assign commit_pointer = instr.commit_pointer;

  assign flush_unissued_instr = instr.flush_unissued_instr;
  assign decoded_instr_valid = instr.decoded_instr_valid;
  assign decoded_instr_ack = instr.decoded_instr_ack;

  assign rs1_forwarding = instr.rs1_forwarding;
  assign rs2_forwarding = instr.rs2_forwarding;

  assign commit_instr_pc = instr.commit_instr_pc;
  assign commit_instr_op = instr.commit_instr_op;
  assign commit_instr_rs1 = instr.commit_instr_rs1;
  assign commit_instr_rs2 = instr.commit_instr_rs2;
  assign commit_instr_rd = instr.commit_instr_rd;
  assign commit_instr_result = instr.commit_instr_result;
  assign commit_instr_valid = instr.commit_instr_valid;

  assign ex_commit_cause = instr.ex_commit_cause;
  assign ex_commit_valid = instr.ex_commit_valid;

  assign priv_lvl = instr.priv_lvl;

  assign wbdata = instr.wbdata;
  assign commit_ack = instr.commit_ack;
  assign mem_paddr = instr.mem_paddr;
  assign debug_mode = instr.debug_mode;
  assign wdata = instr.wdata;

  assign lsu_addr = instr.lsu_ctrl_vaddr;
  assign lsu_rmask = instr.lsu_ctrl_fu == LOAD ? instr.lsu_ctrl_be : '0;
  assign lsu_wmask = instr.lsu_ctrl_fu == STORE ? instr.lsu_ctrl_be : '0;
  assign lsu_addr_trans_id = instr.lsu_ctrl_trans_id;


  //ID STAGE

  typedef struct packed {
    logic        valid;
    logic [31:0] instr;
  } issue_struct_t;
  issue_struct_t issue_n, issue_q;

  always_comb begin
    issue_n = issue_q;

    if (issue_instr_ack) issue_n.valid = 1'b0;

    if ((!issue_q.valid || issue_instr_ack) && fetch_entry_valid) begin
      issue_n.valid = 1'b1;
      issue_n.instr = (is_compressed) ? {{16{1'b0}}, instruction[15:0]} : instruction;
    end

    if (flush) issue_n.valid = 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      issue_q <= '0;
    end else begin
      issue_q <= issue_n;
    end
  end

  //ISSUE STAGE

  // this is the FIFO struct of the issue queue
  typedef struct packed {
    logic [CVA6Cfg.XLEN-1:0] rs1_rdata;
    logic [CVA6Cfg.XLEN-1:0] rs2_rdata;
    logic [CVA6Cfg.XLEN-1:0] lsu_addr;
    logic [(CVA6Cfg.XLEN/8)-1:0] lsu_rmask;
    logic [(CVA6Cfg.XLEN/8)-1:0] lsu_wmask;
    logic [CVA6Cfg.XLEN-1:0] lsu_wdata;
    logic [31:0] instr;
  } sb_mem_t;
  sb_mem_t [CVA6Cfg.NR_SB_ENTRIES-1:0] mem_q, mem_n;

  always_comb begin : issue_fifo
    mem_n = mem_q;

    if (decoded_instr_valid && decoded_instr_ack && !flush_unissued_instr) begin
      mem_n[issue_pointer] = '{
          rs1_rdata: rs1_forwarding,
          rs2_rdata: rs2_forwarding,
          lsu_addr: '0,
          lsu_rmask: '0,
          lsu_wmask: '0,
          lsu_wdata: '0,
          instr: issue_q.instr
      };
    end

    if (lsu_rmask != 0) begin
      mem_n[lsu_addr_trans_id].lsu_addr  = lsu_addr;
      mem_n[lsu_addr_trans_id].lsu_rmask = lsu_rmask;
    end else if (lsu_wmask != 0) begin
      mem_n[lsu_addr_trans_id].lsu_addr  = lsu_addr;
      mem_n[lsu_addr_trans_id].lsu_wmask = lsu_wmask;
      mem_n[lsu_addr_trans_id].lsu_wdata = wbdata[1];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : regs
    if (!rst_ni) begin
      mem_q <= '{default: sb_mem_t'(0)};
    end else begin
      mem_q <= mem_n;
    end
  end

  //----------------------------------------------------------------------------------------------------------
  // PACK
  //----------------------------------------------------------------------------------------------------------

  always_ff @(posedge clk_i) begin
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      logic exception;
      exception = commit_instr_valid[i][0] && ex_commit_valid;
      rvfi_instr_o[i].valid    <= (commit_ack[i] && !ex_commit_valid) ||
        (exception && (ex_commit_cause == cva6v_riscv::ENV_CALL_MMODE ||
                  ex_commit_cause == cva6v_riscv::ENV_CALL_SMODE ||
                  ex_commit_cause == cva6v_riscv::ENV_CALL_UMODE));
      rvfi_instr_o[i].insn <= mem_q[commit_pointer[i]].instr;
      // when trap, the instruction is not executed
      rvfi_instr_o[i].trap <= exception;
      rvfi_instr_o[i].cause <= ex_commit_cause;
      rvfi_instr_o[i].mode <= (CVA6Cfg.DebugEn && debug_mode) ? 2'b10 : priv_lvl;
      rvfi_instr_o[i].ixl <= CVA6Cfg.XLEN == 64 ? 2 : 1;
      rvfi_instr_o[i].rs1_addr <= commit_instr_rs1[i][4:0];
      rvfi_instr_o[i].rs2_addr <= commit_instr_rs2[i][4:0];
      rvfi_instr_o[i].rd_addr <= commit_instr_rd[i][4:0];
      rvfi_instr_o[i].rd_wdata <= (CVA6Cfg.FpPresent && is_rd_fpr(
          commit_instr_op[i]
      )) ? commit_instr_result[i] : wdata[i];
      rvfi_instr_o[i].pc_rdata <= commit_instr_pc[i];
      rvfi_instr_o[i].mem_addr <= mem_q[commit_pointer[i]].lsu_addr;
      // So far, only write paddr is reported. TODO: read paddr
      rvfi_instr_o[i].mem_paddr <= mem_paddr;
      rvfi_instr_o[i].mem_wmask <= mem_q[commit_pointer[i]].lsu_wmask;
      rvfi_instr_o[i].mem_wdata <= mem_q[commit_pointer[i]].lsu_wdata;
      rvfi_instr_o[i].mem_rmask <= mem_q[commit_pointer[i]].lsu_rmask;
      rvfi_instr_o[i].mem_rdata <= commit_instr_result[i];
      rvfi_instr_o[i].rs1_rdata <= mem_q[commit_pointer[i]].rs1_rdata;
      rvfi_instr_o[i].rs2_rdata <= mem_q[commit_pointer[i]].rs2_rdata;
    end
  end

endmodule
