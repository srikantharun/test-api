// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple IFD test
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _SIMPLE_IFD_SV_
`define _SIMPLE_IFD_SV_

task ifd_test;
  t_req wr_req, rd_req;

  logic [AXI_DW-1:0] rddata;

  ifd_tok_prod_rdy <= '1;
  ifd_tok_cons_vld <= '0;

  wait (tb_rst_n);
  repeat (20) @(posedge tb_clk);

  //   $display("IFD: Write out of bounds... @ %0t", $time());
  //   wr_req.burst = 2'b00;
  //   wr_req.len = 0;
  //   wr_req.size = $clog2(DW / 8);
  //   wr_req.id = 3;
  //   wr_req.addr = 'h4000;
  //   ifd_axi_drv.push_write_data('hb1a);
  //   ifd_axi_drv.write(wr_req);

  repeat (20) @(posedge tb_clk);

  $display("IFD: Send addr gen command @ %0t", $time());

  ifd_cmd_drv.snd_cmd(1, 1, 0,
                      ('h1a000 << ifd_odr_pkg::IFD_ODR_AG_MEM_BASE_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_A_LSB |
                        'h1000 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_B_LSB |
                        'h100 << ifd_odr_pkg::IFD_ODR_AG_MEM_STRIDE_C_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_MEM_OFFSET_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_RING_BUFFER_SIZE_LSB |
                        'h1 << ifd_odr_pkg::IFD_ODR_AG_PAD_MODE_EDGE_LSB |
                        'hC35A << ifd_odr_pkg::IFD_ODR_AG_INTRA_PAD_VAL_LSB |
                        'h0 << ifd_odr_pkg::IFD_ODR_AG_VTRSP_EN_LSB |
                        'h5AC3 << ifd_odr_pkg::IFD_ODR_AG_PAD_VAL_LSB |
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

  // I could not find how to control the following signals by sending
  // command then forced not to spend too much time. The following lines
  // can be removed when the command updated accordingly. - Emre
  force i_ifd.u_dp.dpc_config = 1'b0;
  //force i_ifd.u_dp.dpc_msk = '0;
  //force i_ifd.u_dp.dpc_pad = 1'b1;

  repeat (20) @(posedge tb_clk);

  ifd_cmd_drv.snd_cmd(1, 1, 0,
                      ('h1b000 << ifd_odr_pkg::IFD_ODR_AG_LIN_MEM_BASE_LSB |
                        9 << ifd_odr_pkg::IFD_ODR_AG_LIN_LENGTH_LSB),
                      .cmd_format(ifd_odr_pkg::IFD_ODR_CMD_LINEAR_FMT));
  repeat (20) @(posedge tb_clk);
  $display("IFD: Execute @ %0t", $time());
  ifd_cmd_drv.csr_wr(ifd_csr_reg_pkg::IFD_CSR_CMDBLK_CTRL, 1);  // cmd exec

  repeat (24) @(posedge tb_clk);

  release i_ifd.u_dp.dpc_config;
  //release i_ifd.u_dp.dpc_msk;
  //release i_ifd.u_dp.dpc_pad;

  repeat (56) @(posedge tb_clk);  

endtask

`endif  // _SIMPLE_IFD_SV_
