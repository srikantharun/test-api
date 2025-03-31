// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: RVVI End of Test Interface
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef __CVA6V_RVVI_EOT_IF_SV__
`define __CVA6V_RVVI_EOT_IF_SV__


interface cva6v_rvvi_eot_if #(
  parameter type rvvi_instr_t = logic
)(
  input  logic                clk_i,
  input  logic                rst_ni,
  input  rvvi_instr_t         rvvi_i,
  input  logic                hart_is_wfi_i,
  output logic        [31:0]  tb_exit_o
);

  localparam [31:0] EXIT_INSTR  = 32'h10500073;   // WFI opcode

  reg [31:0] last_instr_0;
  reg [31:0] last_instr_1;
  int num_exit_instr = 1; // number of exit instructions, in this case, WFI
  int exit_counter=0;

  // Reset and initialization
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tb_exit_o    <= 1'b0;
      exit_counter <= '0;
    end else begin
      // Check if the input signal has changed
      if ( (rvvi_i.insn[0] ==  EXIT_INSTR && rvvi_i.valid[0] == 1'b1)  ||
           (rvvi_i.insn[1] ==  EXIT_INSTR && rvvi_i.valid[1] == 1'b1)
      ) begin
        exit_counter += 1;
        if (exit_counter >= num_exit_instr) begin
          tb_exit_o = 1'b1;
        end
      end
    end
  end

  initial begin
    void'($value$plusargs("num_exit_instr=%0d", num_exit_instr));
  end

  task wait_end_of_test(int unsigned drain_cyc);
    fork
      begin
        $display("[%t] Waiting for tb_exit_o ==1 started!", $time);
        wait (tb_exit_o==32'h0000_0001);
        wait (hart_is_wfi_i== 1'b1);
        $display("[%t] End-of-test done!", $time);
        repeat (drain_cyc) @ (posedge clk_i);  // drain time to finish instructions
        $display("[%t] Drain cycles of %0d done!", $time, drain_cyc);
      end
      begin
        #10ms; // increased from 6ms absolute timeout. Vcompress/vgather takes longer
        $error("[%t] End-of-test timeout!", $time);
      end
    join_any
    disable fork;
  endtask
endinterface

`endif // __CVA6V_RVVI_EOT_IF_SV__
