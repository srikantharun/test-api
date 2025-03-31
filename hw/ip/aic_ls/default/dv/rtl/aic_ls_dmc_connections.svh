
// Macros for assigning DMC if connections
`define assign_dmc_if(port_name, port_type, index) \
  assign if_``port_name``.dpc_vld               = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_vld; \
  assign if_``port_name``.dpc_rdy               = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_rdy; \
  assign if_``port_name``.dpc_addr              = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_addr; \
  assign if_``port_name``.dpc_msk               = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_msk; \
  assign if_``port_name``.dpc_format            = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_format; \
  assign if_``port_name``.dpc_config            = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_config; \
  assign if_``port_name``.dpc_pad               = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_pad; \
  assign if_``port_name``.dpc_last              = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_last; \
  assign if_``port_name``.dpc_pad_val           = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_pad_val; \
  assign if_``port_name``.dpc_intra_pad_val     = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.dpc_intra_pad_val; \
  assign if_``port_name``.err_addr_out_of_range = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.err_addr_out_of_range; \
  assign if_``port_name``.ag_cmd                = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.ag_cmd; \
  assign if_``port_name``.ag_vld                = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.ag_vld; \
  assign if_``port_name``.ag_rdy                = `LS_DUT_PATH.u_dmc.g_``port_type``[index].u_``port_type``.u_addr_gen.ag_rdy;

`ifdef AI_CORE_TOP_ENV_CHECK
  `define LS_DUT_PATH `DUT.u_ai_core_p.u_ai_core.i_aic_ls_p
 `else
  `define LS_DUT_PATH dut.u_aic_ls
 `endif
   
  assign if_m_ifd0.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_m_ifd1.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_m_ifd2.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_m_ifdw.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_m_odr.reset_an_i  = `LS_DUT_PATH.i_rst_n;

  assign if_d_ifd0.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_d_ifd1.reset_an_i = `LS_DUT_PATH.i_rst_n;
  assign if_d_odr.reset_an_i  = `LS_DUT_PATH.i_rst_n;

  `assign_dmc_if(m_ifd0, ifd, 0)
  `assign_dmc_if(m_ifd1, ifd, 1)
  `assign_dmc_if(m_ifd2, ifd, 2)
  `assign_dmc_if(m_ifdw, ifd, 3)
  `assign_dmc_if(d_ifd0, ifd, 4)
  `assign_dmc_if(d_ifd1, ifd, 5)
  `assign_dmc_if(m_odr, odr, 6)
  `assign_dmc_if(d_odr, odr, 7)

