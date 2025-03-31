// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi_riscv_atomics/blob/master/src/axi_riscv_amos_alu.sv
// Original Authors:
//   - Samuel Riedel <sriedel@iis.ee.ethz.ch>
//   - Andreas Kurth <akurth@iis.ee.ethz.ch>

// AXI RISC-V Atomic Operations (AMOs) ALU
//
module axe_axi_riscv_amos_alu # (
  parameter int unsigned DataWidth = 0
)(
  input  axi_pkg::axi_atop_t   i_amo_op,
  input  logic [DataWidth-1:0] i_amo_operand_a,
  input  logic [DataWidth-1:0] i_amo_operand_b,
  output logic [DataWidth-1:0] o_amo_result
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' Must be larger than 0;");

  ////////////////////
  // Implementation //
  ////////////////////
  logic [DataWidth:0] adder_sum;
  logic [DataWidth:0] adder_operand_a, adder_operand_b;

  always_comb adder_sum = adder_operand_a + adder_operand_b;

  // Determine the sign of operand a and a
  always_comb begin
    unique case (i_amo_op[2:0])
      axi_pkg::AXI_ATOP_SMAX,
      axi_pkg::AXI_ATOP_SMIN: begin
        adder_operand_a =  $signed(i_amo_operand_a);
        adder_operand_b = -$signed(i_amo_operand_b);
      end
      axi_pkg::AXI_ATOP_UMAX,
      axi_pkg::AXI_ATOP_UMIN: begin
        adder_operand_a =  $unsigned(i_amo_operand_a);
        adder_operand_b = -$unsigned(i_amo_operand_b);
      end
      default: begin
        adder_operand_a =  $signed(i_amo_operand_a);
        adder_operand_b =  $signed(i_amo_operand_b);
      end
    endcase
  end

  // The actual calculations
  always_comb begin
    o_amo_result = i_amo_operand_a;

    if (i_amo_op == axi_pkg::AXI_ATOP_ATOMICSWAP) begin
      // Swap operation
      o_amo_result = i_amo_operand_b;
    end else if (
         (i_amo_op[5:4] == axi_pkg::AXI_ATOP_ATOMICLOAD)
      || (i_amo_op[5:4] == axi_pkg::AXI_ATOP_ATOMICSTORE)
    ) begin
      // Load operation
      unique case (i_amo_op[2:0])
        // the default is to output operand_a
        axi_pkg::AXI_ATOP_ADD:  o_amo_result = adder_sum[DataWidth-1:0];
        axi_pkg::AXI_ATOP_CLR:  o_amo_result = i_amo_operand_a & (~i_amo_operand_b);
        axi_pkg::AXI_ATOP_SET:  o_amo_result = i_amo_operand_a | i_amo_operand_b;
        axi_pkg::AXI_ATOP_EOR:  o_amo_result = i_amo_operand_a ^ i_amo_operand_b;
        axi_pkg::AXI_ATOP_SMAX: o_amo_result = adder_sum[DataWidth] ? i_amo_operand_b : i_amo_operand_a;
        axi_pkg::AXI_ATOP_SMIN: o_amo_result = adder_sum[DataWidth] ? i_amo_operand_a : i_amo_operand_b;
        axi_pkg::AXI_ATOP_UMAX: o_amo_result = adder_sum[DataWidth] ? i_amo_operand_b : i_amo_operand_a;
        axi_pkg::AXI_ATOP_UMIN: o_amo_result = adder_sum[DataWidth] ? i_amo_operand_a : i_amo_operand_b;
        default:                o_amo_result = '0;
      endcase
    end
  end
endmodule
