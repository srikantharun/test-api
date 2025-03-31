// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Testbench file for the reset_gen module
// Owner: Abhishek Maringanti <Abhishek.Maringanti@axelera.ai>

`ifndef RESET_GEN_BASIC_TB_SV
`define RESET_GEN_BASIC_TB_SV

module reset_gen_tb_basic;

  logic tb_clk;
  logic tb_por_rst_ni;
  logic tb_hw_rst_ni;
  logic tb_rst_ni_s0;
  logic tb_rst_ni_s1;
  logic [1:0] tb_rst_ip_sw_ni_s0;
  logic [2:0] tb_rst_ip_sw_ni_s1;
  logic [1:0] tb_rst_ip_ack_i_s0;
  logic [2:0] tb_rst_ip_ack_i_s1;
  logic tb_rst_req_ni_s0;
  logic tb_rst_req_ni_s1;

  logic tb_rst_no_s0;
  logic tb_rst_no_s1;


  logic [1:0] tb_rst_src_ni;

  // clock generation:
  initial begin
    tb_clk = 0;
    forever #((1.250) / 2) tb_clk = ~tb_clk;
  end

  // Driving the reset signals
  initial
  begin
    tb_por_rst_ni = 0;
    tb_hw_rst_ni = 0;
    tb_rst_ni_s0 = 0;
    tb_rst_ip_sw_ni_s0 = 2'b11;
    tb_rst_ip_sw_ni_s1 = 3'b111;
    tb_rst_ip_ack_i_s0 = 2'b00;
    tb_rst_ip_ack_i_s1 = 3'b000;
    tb_rst_req_ni_s0 = 1;
    tb_rst_req_ni_s1 = 1;

    fork 
      begin
        repeat (20) @(posedge tb_clk);
        #0.1;
        tb_por_rst_ni = 1;
        $display("RESET_GEN_TB: POR Reset sequence completed.");

        repeat (130) @(posedge tb_clk);
        #0.1;
        tb_por_rst_ni = 0;
        $display("RESET_GEN_TB: POR Reset sequence completed.");

        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_por_rst_ni = 1;
        $display("RESET_GEN_TB: POR Reset sequence completed.");

      end
      begin
        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_hw_rst_ni = 1;
        $display("RESET_GEN_TB: HW_RST sequence completed.");
      end
      begin
        repeat (50) @(posedge tb_clk);
        #0.1;
        tb_rst_ni_s0 = 1;
        $display("RESET_GEN_TB: Input Stage Reset sequence completed.");
        repeat (5) @(posedge tb_clk);
        #0.1;
        tb_rst_ip_ack_i_s0[0] = 0;
      end
      begin
        repeat (100) @(posedge tb_clk);
        #0.1;
        tb_rst_ip_sw_ni_s0[0] = 0;
        $display("RESET_GEN_TB: SW Reset sequence initiated.");
        
        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_rst_ip_sw_ni_s0[0] = 1;
        $display("RESET_GEN_TB: SW Reset sequence completed.");
      end
      begin
        repeat (130) @(posedge tb_clk);
        #0.1;
        tb_rst_ip_sw_ni_s1[1] = 0;
        $display("RESET_GEN_TB: SW Reset sequence initiated.");
        
        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_rst_ip_sw_ni_s1[1] = 1;
        $display("RESET_GEN_TB: SW Reset sequence completed.");
      end
      begin
        repeat (200) @(posedge tb_clk);
        #0.1;
        tb_rst_req_ni_s0 = 0;
        $display("RESET_GEN_TB: SW Reset sequence initiated.");
        
        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_rst_req_ni_s0 = 1;
        $display("RESET_GEN_TB: SW Reset sequence completed.");
      end
      begin
        repeat (300) @(posedge tb_clk);
        #0.1;
        tb_rst_req_ni_s1 = 0;
        $display("RESET_GEN_TB: SW Reset sequence initiated.");
        
        repeat (10) @(posedge tb_clk);
        #0.1;
        tb_rst_req_ni_s1 = 1;
        $display("RESET_GEN_TB: SW Reset sequence completed.");
      end
    join
  end
  
  initial
  begin
    repeat (600) @(posedge tb_clk);
    #1;
    $finish;
  end

  assign tb_sys_periph_clk_i = tb_clk;
  assign tb_rst_src_ni = {tb_por_rst_ni, tb_hw_rst_ni};

  // ***************** DUT INSTANTIATION ******************* //
  reset_gen_basic_block #(
    .RST_SRC_NUM (2),
    .RST_IP_NUM (2),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_stage0 (
    .test_i (1'b1),
    .clk_i (tb_clk),
    .rst_stretch_i ('d10),
    .rst_ni (tb_rst_ni_s0),
    .rst_no (tb_rst_no_s0),
    .rst_req_ni (tb_rst_req_ni_s0),
    .rst_ack_no (),
    .rst_src_ni (tb_rst_src_ni),
    .rst_src_mask_i (2'b00),
    .rst_ip_sw_ni (tb_rst_ip_sw_ni_s0),
    .rst_ip_no (),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (tb_rst_ip_ack_i_s0)
);

  assign tb_rst_ni_s1 = &{tb_rst_no_s0};

  reset_gen_basic_block #(
    .RST_SRC_NUM (2),
    .RST_IP_NUM (3),
    .RST_STRETCH_USE (1)
  ) i_reset_gen_basic_block_stage1 (
    .test_i (1'b1),
    .clk_i (tb_clk),
    .rst_stretch_i ('d10),
    .rst_ni (tb_rst_ni_s1),
    .rst_no (tb_rst_no_s1),
    .rst_req_ni (tb_rst_req_ni_s1),
    .rst_ack_no (),
    .rst_src_ni (tb_rst_src_ni),
    .rst_src_mask_i (2'b00),
    .rst_ip_sw_ni (tb_rst_ip_sw_ni_s1),
    .rst_ip_no (),
    .rst_ip_force_i ('0),
    .rst_ip_ack_i (tb_rst_ip_ack_i_s1)
);

`ifdef VCD_ENABLE
  initial begin
    $dumpfile("reset_gen.vcd");
    $dumpvars(0, reset_gen_tb_basic);
  end
`endif


endmodule

`endif  // RESET_GEN_BASIC_TB_SV

