//    Copyright 2006 Andes Technology Corp. - All Rights Reserved.    //


module gck (clk_out, clk_en, clk_in, test_en);

  parameter BYPASS_CLKEN_IN_FPGA = 0;
  `ifdef NDS_FPGA
  (* gated_clock = "true" *) input clk_in;
  `else
  input clk_in;
  `endif
  input clk_en;
  input test_en;

  output clk_out;

  logic bypass;

  if (BYPASS_CLKEN_IN_FPGA) begin
`ifdef NDS_FPGA
    always_comb bypass = 1;
`else
    always_comb bypass = test_en;
`endif
  end
  else begin
    always_comb bypass = test_en;
  end

  axe_tcl_clk_gating u_clk_gating (
    .i_clk(clk_in),
    .i_en(clk_en),
    .i_test_en(bypass),
    .o_clk(clk_out)
  );
endmodule
