// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple ODR test
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _SIMPLE_ODR_SV_
`define _SIMPLE_ODR_SV_

task odr_test;
  t_req wr_req, rd_req;

  logic [AXI_DW-1:0] rddata;

  odr_tok_prod_rdy <= '1;
  odr_tok_cons_vld <= '0;

  wait (tb_rst_n);
  repeat (20) @(posedge tb_clk);

  //   $display("ODR: Write out of bounds... @ %0t", $time());
  //   wr_req.burst = 2'b00;
  //   wr_req.len = 0;
  //   wr_req.size = $clog2(DW / 8);
  //   wr_req.id = 3;
  //   wr_req.addr = 'h4000;
  //   odr_axi_drv.push_write_data('hb1a);
  //   odr_axi_drv.write(wr_req);

  repeat (20) @(posedge tb_clk);
  $display("ODR: Send addr gen command @ %0t", $time());
  odr_cmd_drv.snd_cmd(1, 1, 0,
                      ('h1a000 << ifd_odr_pkg::IFD_ODR_AG_MEM_BASE_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_A_LSB |
                        'h1000 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_B_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_C_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_MEM_OFFSET_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_RING_BUFFER_SIZE_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_PAD_MODE_EDGE_LSB |
                        'h0B0A << ifd_odr_pkg::IFD_ODR_AG_INTRA_PAD_VAL_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_VTRSP_EN_LSB |
                        'hC35A << ifd_odr_pkg::IFD_ODR_AG_PAD_VAL_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_LEN_A_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_LEN_B_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_LEN_C_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_STR_A_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_STR_B_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_INNER_STR_C_LSB |
                        'h2 << ifd_odr_pkg::IFD_ODR_AG_OUTER_LEN_A_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_OUTER_LEN_B_LSB |
                        'h3 << ifd_odr_pkg::IFD_ODR_AG_OUTER_LEN_C_LSB |
                        'h3 << ifd_odr_pkg::IFD_ODR_AG_OUTER_STR_A_LSB |
                        'h3 << ifd_odr_pkg::IFD_ODR_AG_OUTER_STR_B_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_OUTER_STR_C_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_DIM_OFF_A_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_DIM_OFF_B_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_DIM_OFF_C_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_DIM_W_A_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_DIM_W_B_LSB |
                        'h70 << ifd_odr_pkg::IFD_ODR_AG_DIM_W_C_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_MSK_START_LSB |
                        'h40 << ifd_odr_pkg::IFD_ODR_AG_MSK_END_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_FORMAT_LSB),
                      .cmd_format(ifd_odr_pkg::IFD_ODR_CMD_FALLBACK_FMT));

  force i_odr.u_dp.dpc_config = 1'b1;
  //force i_odr.u_dp.dpc_msk = '0;
  force i_odr.u_dp.dpc_drop = 1'b1;

  repeat (20) @(posedge tb_clk);
  $display("ODR: Execute @ %0t", $time());
  odr_cmd_drv.csr_wr(odr_csr_reg_pkg::ODR_CSR_CMDBLK_CTRL, 1);  // cmd exec

  for (int i=0;i<54-1;i++)
    snd_axis_tok('1, 0);
  snd_axis_tok('1, 1);

  repeat (80) @(posedge tb_clk);

  release i_odr.u_dp.dpc_config;
  //release i_odr.u_dp.dpc_msk;
  release i_odr.u_dp.dpc_drop;

endtask

`endif  // _SIMPLE_ODR_SV_
