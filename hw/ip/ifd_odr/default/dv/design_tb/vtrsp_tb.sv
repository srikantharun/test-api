// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Testbench file for the vtrsp module
// Owner: Abhishek Maringanti <Abhishek.Maringanti@axelera.ai>

`ifndef VTRSP_TB_SV
`define VTRSP_TB_SV

module vtrsp_tb;
  import ifd_odr_pkg::*;

  // Clocks and Reset Signals
  logic tb_clk;
  logic tb_rst_n;

  // AXI-Stream Subordinate Interface 
  logic tb_axis_s_tvalid;  // input 
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_axis_s_tdata;  // input 
  logic tb_axis_s_tlast;  //  input 

  logic tb_axis_s_tready;  // output 

  // AXI-S Subordinate Interface for command
  logic tb_cmd_valid;  //  input  
  logic tb_cmd_ready;  //  output 
  logic [1:0] tb_cmd_data;  // input

  // AXI-Stream Manager Interface
  logic tb_axis_m_tready;  // input 

  logic tb_axis_m_tvalid;  // output 
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_axis_m_tdata;  // output 
  logic tb_axis_m_tlast;  //  output 

  // Control Signals
  logic tb_transpose_en;   // FIXME -- This is being generated internally based on the input cmd_* interface.   //  //  input 

  // Interrupts
  logic tb_vtrsp_irq;  //  output

  logic error_enable;

  logic [1:0] cmd_mode = 2'b00;
  logic [1:0] stored_cmd_mode = 2'b00;
  mailbox bp_length_mb = new();
  mailbox rcv_cmd_mode_mb = new();
  mailbox check_cmd_mode_mb = new();
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] inp_data_matrix_bp[int][int];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] inp_data_matrix_fp8[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] inp_data_matrix_fp16[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/2-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] inp_data_matrix_fp32[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/4-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_inp_data_tmatrix_bp[int][int];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_inp_data_tmatrix_fp8[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_inp_data_tmatrix_fp16[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/2-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] tb_inp_data_tmatrix_fp32[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/4-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] out_data_tmatrix_bp[int][int];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] out_data_tmatrix_fp8[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] out_data_tmatrix_fp16[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/2-1:0];
  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] out_data_tmatrix_fp32[int][aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES/4-1:0];

  int check_pkt = 0;
  int pkt_send = 0;
  int pkt_rcvd = 0;

  `include "simple_vtrsp.sv"

  // clock generation:
  initial begin
    tb_clk = 0;
    forever #((1.250) / 2) tb_clk = ~tb_clk;
  end

  // reset generation:
  initial begin
    tb_rst_n = 0;

    //initialize the inputs to DUT from TB:
    tb_axis_s_tvalid = '0;
    tb_axis_s_tlast = '0;
    tb_axis_s_tdata = '0;
    tb_cmd_valid = '0;
    tb_cmd_data = '0;

    repeat (20) @(posedge tb_clk);
    #1;
    tb_rst_n = 1;
    $display("VTRSP_TB: Reset sequence completed.");
  end

  //******************* DUT *******************//
  vtrsp #(
    .status_t(ifd_csr_reg_pkg::ifd_csr_hw2reg_dp_status_reg_t)
  ) u_vtrsp (
    // Clocks and Reset Signals
    .i_clk  (tb_clk),   //  input logic 
    .i_rst_n(tb_rst_n), //  input logic 

    // AXI-Stream Subordinate Interface 
    .axis_s_tvalid(tb_axis_s_tvalid),  //  input logic 
    .axis_s_tdata (tb_axis_s_tdata),   //  input logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0]
    .axis_s_tlast (tb_axis_s_tlast),   //  input logic 

    .axis_s_tready(tb_axis_s_tready),  //  output logic 

    // AXI-S Subordinate Interface for command
    .cmd_valid(tb_cmd_valid),  //  input  logic 
    .cmd_ready(tb_cmd_ready),  //  output logic 
    .cmd_data (tb_cmd_data),   //  input  logic 

    // AXI-Stream Manager Interface
    .axis_m_tready(tb_axis_m_tready),  //  input logic 

    .axis_m_tvalid(tb_axis_m_tvalid),  //  output logic 
    .axis_m_tdata (tb_axis_m_tdata),   //  output logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0]
    .axis_m_tlast (tb_axis_m_tlast),   //  output logic 

    // Interrupts
    .vtrsp_irq(tb_vtrsp_irq),  //  output logic

    .vtrsp_status()  // status bus from vtrsp
  );

  // Running the simple_vtrsp test
  initial begin
    //    vtrsp_test;
    vtrsp_test_mixed;
    #1000;
    $finish;
  end

  int data_counter = '0;
  int rcv_count = '0;
  //  always @(posedge tb_clk) #1 tb_axis_m_tready = $random();
  always @(posedge tb_clk) #0.1 tb_axis_m_tready = 1;// $random();
  always @(negedge tb_clk) begin
    //    #1;
    if (tb_axis_m_tvalid & tb_axis_m_tready) begin
      if (data_counter == 0)
        rcv_cmd_mode_mb.get(stored_cmd_mode);
      // if (stored_cmd_mode==2'b00)
      //   $display(
      //     "VTRSP_DUT: Output data stream. pkt %0d (length %0d) PW no: %0d with Data = 0x%0h at %0t. ",
      //       pkt_rcvd, rcv_count, data_counter, tb_axis_m_tdata, $time());

      data_counter = data_counter + 1;
      case (stored_cmd_mode[1:0])
        2'b01: begin
          out_data_tmatrix_fp8[pkt_rcvd][data_counter-1] = tb_axis_m_tdata;
          if (data_counter == aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES) begin
            data_counter = 0;
            pkt_rcvd = pkt_rcvd + 1;
          end
        end
        2'b10: begin
          out_data_tmatrix_fp16[pkt_rcvd][data_counter-1] = tb_axis_m_tdata;
          if (data_counter == aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 2) begin
            data_counter = 0;
            pkt_rcvd = pkt_rcvd + 1;
          end
        end
        2'b11: begin
          out_data_tmatrix_fp32[pkt_rcvd][data_counter-1] = tb_axis_m_tdata;
          if (data_counter == aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES / 4) begin
            data_counter = 0;
            pkt_rcvd = pkt_rcvd + 1;
          end
        end
        default: begin
          out_data_tmatrix_bp[pkt_rcvd][data_counter-1] = tb_axis_m_tdata;
          if (data_counter == aic_common_pkg::AIC_PWORD_I8_WIDTH_BYTES) begin
            data_counter = 0;
            pkt_rcvd = pkt_rcvd + 1;
          end
        end
      endcase
      if (tb_axis_m_tlast) begin
        $display("VTRSP_DUT: Last Data of the Stream.");
        data_counter = '0;
      end
    end
  end

  always begin
    @(pkt_rcvd); // new packet received
    repeat(2) @(posedge tb_clk);
    $display("Calling verify_transposed_data task for pkt %0d %0t\n", check_pkt, $time());
    verify_transposed_data(check_pkt);
    check_pkt = check_pkt + 1;
  end

`ifdef VCD_ENABLE
  initial begin
    $dumpfile("vtrsp_sim.vcd");
    $dumpvars(0, vtrsp_tb);
  end
`endif

endmodule

`endif  // VTRSP_TB_SV

