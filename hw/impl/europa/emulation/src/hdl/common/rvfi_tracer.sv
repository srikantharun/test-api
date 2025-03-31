// Copyright 2020 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales

module rvfi_tracer #(
  parameter cva6v_config_pkg::cva6_cfg_t CVA6Cfg = cva6v_config_pkg::cva6_cfg_empty,
  parameter type rvfi_instr_t = logic,
  parameter type rvfi_csr_t = logic,
  //
  parameter int unsigned DEBUG_START = 0,
  parameter int unsigned DEBUG_STOP  = 0
)(
  input logic [CVA6Cfg.XLEN-1:0]        hart_id_i,
  input logic                           enable,
  input logic                           new_file,
  input logic                           clk_i,
  input logic                           rst_ni,
  input rvfi_instr_t[CVA6Cfg.NrCommitPorts-1:0] rvfi_i,
  input rvfi_csr_t                      rvfi_csr_i,
  output logic[31:0]                    end_of_test_o
);

  wire gated_clk = enable ? clk_i : 0;

  longint unsigned TOHOST_ADDR;
  string binary;
  int f = 0;
  int unsigned SIM_FINISH;
  string filename;
  initial begin
    if (!$value$plusargs("time_out=%d", SIM_FINISH)) SIM_FINISH = 32'hffffffff;
    if (!$value$plusargs("tohost_addr=%h", TOHOST_ADDR)) TOHOST_ADDR = '0;
  end

  bit new_file_prev = 0;

  always @(posedge clk_i) begin
    new_file_prev <= new_file;

    if (new_file && !new_file_prev) begin
      filename = $sformatf("./instruction_dump_cva6v_id%0d.log", hart_id_i);
      if (f) begin
        $display("closing file %0s", filename);
        $fflush(f);
        $fclose(f);
      end
      $display("opening file %0s", filename);
      f = $fopen(filename, "w");
    end
  end

  final $fclose(f);

  logic [31:0] cycles;
  // Generate the trace based on RVFI
  logic [63:0] pc64;
  string cause;
  logic[31:0] end_of_test_q;
  logic[31:0] end_of_test_d;

  assign end_of_test_o = end_of_test_d;
  always_ff @(posedge gated_clk) begin
    end_of_test_q = (rst_ni && (end_of_test_d[0] == 1'b1)) ? end_of_test_d : 0;
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      pc64 = {{CVA6Cfg.XLEN-CVA6Cfg.XLEN{rvfi_i[i].pc_rdata[CVA6Cfg.XLEN-1]}}, rvfi_i[i].pc_rdata};
      // print the instruction information if the instruction is valid or a trap is taken
      if (rvfi_i[i].valid) begin
        // Instruction information
        $fwrite(f, "core   0: 0x%h (0x%h) DASM(%h) [t=%0t]\n",
          pc64, rvfi_i[i].insn, rvfi_i[i].insn, $time);
        $fflush(f);
        // Destination register information
        if (rvfi_i[i].insn[1:0] != 2'b11) begin
          $fwrite(f, "%h 0x%h (0x%h)",
            rvfi_i[i].mode, pc64, rvfi_i[i].insn[15:0]);
          $fflush(f);
        end else begin
          $fwrite(f, "%h 0x%h (0x%h)",
            rvfi_i[i].mode, pc64, rvfi_i[i].insn);
          $fflush(f);
        end
        // Decode instruction to know if destination register is FP register.
        // Handle both uncompressed and compressed instructions.
        if ( rvfi_i[i].insn[6:0] == 7'b1001111 ||
             rvfi_i[i].insn[6:0] == 7'b1001011 ||
             rvfi_i[i].insn[6:0] == 7'b1000111 ||
             rvfi_i[i].insn[6:0] == 7'b1000011 ||
             rvfi_i[i].insn[6:0] == 7'b0000111 ||
            (rvfi_i[i].insn[6:0] == 7'b1010011 && rvfi_i[i].insn[31:26] != 6'b111000
                                               && rvfi_i[i].insn[31:26] != 6'b101000
                                               && rvfi_i[i].insn[31:26] != 6'b110000) ||
            (rvfi_i[i].insn[0] == 1'b0 && ((rvfi_i[i].insn[15:13] == 3'b001 && CVA6Cfg.XLEN == 64) ||
                                           (rvfi_i[i].insn[15:13] == 3'b011 && CVA6Cfg.XLEN == 32) ))) begin
          $fwrite(f, " f%d 0x%h", rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
          $fflush(f);
        end else if (rvfi_i[i].rd_addr != 0) begin
          $fwrite(f, " x%d 0x%h", rvfi_i[i].rd_addr, rvfi_i[i].rd_wdata);
          $fflush(f);
          if (rvfi_i[i].mem_rmask != 0) begin
            $fwrite(f, " mem 0x%h", rvfi_i[i].mem_addr);
            $fflush(f);
          end
        end else begin
          if (rvfi_i[i].mem_wmask != 0) begin
            $fwrite(f, " mem 0x%h 0x%h", rvfi_i[i].mem_addr, rvfi_i[i].mem_wdata);
            $fflush(f);
            if (TOHOST_ADDR != '0 &&
                rvfi_i[i].mem_paddr == TOHOST_ADDR &&
                rvfi_i[i].mem_wdata[0] == 1'b1) begin
              end_of_test_q = rvfi_i[i].mem_wdata[31:0];
            end
          end
        end
        $fwrite(f, "\n");
        $fflush(f);
      end else begin
        if (rvfi_i[i].trap) begin
          case (rvfi_i[i].cause)
            32'h0: cause = "INSTR_ADDR_MISALIGNED";
            32'h1: cause = "INSTR_ACCESS_FAULT";
            32'h2: cause = "ILLEGAL_INSTR";
            32'h3: cause = "BREAKPOINT";
            32'h4: cause = "LD_ADDR_MISALIGNED";
            32'h5: cause = "LD_ACCESS_FAULT";
            32'h6: cause = "ST_ADDR_MISALIGNED";
            32'h7: cause = "ST_ACCESS_FAULT";
          endcase;
          $fwrite(f, "%s exception @ 0x%h\n", cause, pc64);
          $fflush(f);
        end
      end
    end

    if (~rst_ni)
      cycles <= 0;
    else
      cycles <= cycles+1;
    if (cycles > SIM_FINISH)
      end_of_test_q = 32'hffff_ffff;

    end_of_test_d <= end_of_test_q;
  end


endmodule // rvfi_tracer
