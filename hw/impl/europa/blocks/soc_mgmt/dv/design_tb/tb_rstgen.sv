// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@aelera.ai>


// Simple clock generator for testbenches
module tb_rstgen #(
  parameter int unsigned ResetCycles = 5
)
(
  input  wire  i_clk    ,
  input  logic i_drv_rst,
  output wire  o_rst_n
);

//=============================================================================
logic rst;

initial begin
  rst = 1;
  do_reset();

  forever begin
    @(posedge i_drv_rst) begin
      do_reset();
    end
  end
end

assign o_rst_n = rst;

//=============================================================================
// Assert and clear the generated reset
task do_reset();
  rst = 0;
  repeat(1) begin
    repeat(ResetCycles) @ (negedge i_clk);
  end
  rst = 1;
endtask

endmodule
