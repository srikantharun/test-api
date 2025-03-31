`include "ep_x4_DWC_pcie_ctl_cc_constants.svh"

// ======================================================================
//                    External RAMs instantiation
// ======================================================================
module DWC_pcie_ctrl_memory_top
 (
  // Port list for RAM instance u_ib_mcpl_sb_ram of model ram_2p_1c_wrapper
input [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES*`ep_x4_CC_IB_MCPL_SEG_BUF_RAM_ADDR_WD-1:0]   ib_mcpl_sb_ram_addra,
input [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES*`ep_x4_CC_IB_MCPL_SEG_BUF_RAM_ADDR_WD-1:0]   ib_mcpl_sb_ram_addrb,
input [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES*`ep_x4_CC_MSTR_CPL_SEG_BUF_SLICE_WD-1:0]   ib_mcpl_sb_ram_dina,
output [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES*`ep_x4_CC_MSTR_CPL_SEG_BUF_SLICE_WD-1:0]   ib_mcpl_sb_ram_doutb,
input [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES-1:0]                                        ib_mcpl_sb_ram_enb,
input [`ep_x4_CC_MSTR_CPL_SEG_N_SLICES-1:0]                                        ib_mcpl_sb_ram_wea,
// Port list for RAM instance u_ib_mcpl_a2c_cdc_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_IB_MCPL_CDC_RAM_ADDR_WD-1:0]     ib_mcpl_a2c_cdc_ram_addra,
input [`ep_x4_CC_IB_MCPL_CDC_RAM_ADDR_WD-1:0]     ib_mcpl_a2c_cdc_ram_addrb,
input                                      ib_mcpl_a2c_cdc_ram_wea,
input                                      ib_mcpl_a2c_cdc_ram_enb,
output  [`ep_x4_CC_IB_MCPL_CDC_RAM_DATA_WD-1:0]     ib_mcpl_a2c_cdc_ram_doutb,
input [`ep_x4_CC_IB_MCPL_CDC_RAM_DATA_WD-1:0]     ib_mcpl_a2c_cdc_ram_dina,
// Port list for RAM instance u_ib_rreq_ordr_ram of model ram_2p_1c_wrapper
input [`ep_x4_CC_IB_RD_REQ_ORDR_RAM_ADDR_WD-1:0]     ib_rreq_ordr_ram_addra,
input [`ep_x4_CC_IB_RD_REQ_ORDR_RAM_ADDR_WD-1:0]     ib_rreq_ordr_ram_addrb,
input                                         ib_rreq_ordr_ram_wea,
input                                         ib_rreq_ordr_ram_enb,
input [`ep_x4_CC_IB_RD_REQ_ORDR_RAM_DATA_WD-1:0]     ib_rreq_ordr_ram_dina,
output  [`ep_x4_CC_IB_RD_REQ_ORDR_RAM_DATA_WD-1:0]     ib_rreq_ordr_ram_doutb,
// Port list for RAM instance u_ib_rreq_c2a_cdc_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_IB_RD_REQ_CDC_RAM_ADDR_WD-1:0]      ib_rreq_c2a_cdc_ram_addra,
input [`ep_x4_CC_IB_RD_REQ_CDC_RAM_ADDR_WD-1:0]      ib_rreq_c2a_cdc_ram_addrb,
input                                         ib_rreq_c2a_cdc_ram_wea,
input                                         ib_rreq_c2a_cdc_ram_enb,
input [`ep_x4_CC_IB_RD_REQ_CDC_RAM_DATA_WD-1:0]      ib_rreq_c2a_cdc_ram_dina,
output [`ep_x4_CC_IB_RD_REQ_CDC_RAM_DATA_WD-1:0]       ib_rreq_c2a_cdc_ram_doutb,
  // Port list for RAM instance u_ib_wreq_c2a_cdc_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_IB_WR_REQ_CDC_RAM_ADDR_WD-1:0]      ib_wreq_c2a_cdc_ram_addra,
input [`ep_x4_CC_IB_WR_REQ_CDC_RAM_ADDR_WD-1:0]      ib_wreq_c2a_cdc_ram_addrb,
input                                         ib_wreq_c2a_cdc_ram_wea,
input                                         ib_wreq_c2a_cdc_ram_enb,
input [`ep_x4_CC_IB_WR_REQ_CDC_RAM_DATA_WD-1:0]      ib_wreq_c2a_cdc_ram_dina,
output [`ep_x4_CC_IB_WR_REQ_CDC_RAM_DATA_WD-1:0]       ib_wreq_c2a_cdc_ram_doutb,
  // Port list for RAM instance u_ob_ccmp_data_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_OB_CCMP_NSLICES*`ep_x4_CC_OB_CCMP_DATA_RAM_ADDR_WD-1:0]  ob_ccmp_data_ram_addra,
input [`ep_x4_CC_OB_CCMP_NSLICES-1:0]                           ob_ccmp_data_ram_wea,
input [`ep_x4_CC_OB_CCMP_NSLICES*`ep_x4_CC_OB_CCMP_SLICE_WD-1:0]       ob_ccmp_data_ram_dina,
input [`ep_x4_CC_OB_CCMP_NSLICES*`ep_x4_CC_OB_CCMP_DATA_RAM_ADDR_WD-1:0]  ob_ccmp_data_ram_addrb,
input [`ep_x4_CC_OB_CCMP_NSLICES-1:0]                           ob_ccmp_data_ram_enb,
output  [`ep_x4_CC_OB_CCMP_NSLICES*`ep_x4_CC_OB_CCMP_SLICE_WD-1:0]       ob_ccmp_data_ram_doutb,
  // Port list for RAM instance u_ob_npdcmp_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_OB_NPDCMP_RAM_ADDR_WD-1:0]        ob_npdcmp_ram_addra,
input                                    ob_npdcmp_ram_wea,
input [`ep_x4_CC_OB_NPDCMP_RAM_DATA_WD-1:0]        ob_npdcmp_ram_dina,
input [`ep_x4_CC_OB_NPDCMP_RAM_ADDR_WD-1:0]        ob_npdcmp_ram_addrb,
input                                    ob_npdcmp_ram_enb,
output  [`ep_x4_CC_OB_NPDCMP_RAM_DATA_WD-1:0]        ob_npdcmp_ram_doutb,
  // Port list for RAM instance u_slv_npw_sab_ram of model ram_2p_1c_wrapper
input [`ep_x4_CC_SLV_NPW_SAB_RAM_ADDR_WD-1:0]      slv_npw_sab_ram_addra,
input                                    slv_npw_sab_ram_wea,
input [`ep_x4_CC_SLV_NPW_SAB_RAM_DATA_WD-1:0]      slv_npw_sab_ram_dina,
input [`ep_x4_CC_SLV_NPW_SAB_RAM_ADDR_WD-1:0]      slv_npw_sab_ram_addrb,
input                                    slv_npw_sab_ram_enb,
output  [`ep_x4_CC_SLV_NPW_SAB_RAM_DATA_WD-1:0]      slv_npw_sab_ram_doutb,
// Port list for RAM instance u_ob_pdcmp_data_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_OB_PDCMP_DATA_RAM_ADDR_WD-1:0]    ob_pdcmp_data_ram_addra,
input                                    ob_pdcmp_data_ram_wea,
input [`ep_x4_CC_OB_PDCMP_DATA_RAM_DATA_WD-1:0]    ob_pdcmp_data_ram_dina,
input [`ep_x4_CC_OB_PDCMP_DATA_RAM_ADDR_WD-1:0]    ob_pdcmp_data_ram_addrb,
input                                    ob_pdcmp_data_ram_enb,
output  [`ep_x4_CC_OB_PDCMP_DATA_RAM_DATA_WD-1:0]    ob_pdcmp_data_ram_doutb,
// Port list for RAM instance u_ob_pdcmp_hdr_ram of model ram_2p_2c_wrapper
input [`ep_x4_CC_OB_PDCMP_HDR_RAM_ADDR_WD-1:0]     ob_pdcmp_hdr_ram_addra,
input                                    ob_pdcmp_hdr_ram_wea,
input [`ep_x4_CC_OB_PDCMP_HDR_RAM_DATA_WD-1:0]     ob_pdcmp_hdr_ram_dina,
input [`ep_x4_CC_OB_PDCMP_HDR_RAM_ADDR_WD-1:0]     ob_pdcmp_hdr_ram_addrb,
input                                    ob_pdcmp_hdr_ram_enb,
output  [`ep_x4_CC_OB_PDCMP_HDR_RAM_DATA_WD-1:0]     ob_pdcmp_hdr_ram_doutb,
// Port list for RAM instance u_ram_cdm_rasdes_ec_reg of model ram_2p_1c_wrapper
input [`ep_x4_CX_RAS_DES_EC_RAM_ADDR_WIDTH-1:0]  cdm_ras_des_ec_ram_addra,
input [`ep_x4_CX_RAS_DES_EC_RAM_ADDR_WIDTH-1:0]  cdm_ras_des_ec_ram_addrb,
input [`ep_x4_CX_RAS_DES_EC_RAM_DATA_WIDTH-1:0]  cdm_ras_des_ec_ram_datain,
input                                 cdm_ras_des_ec_ram_wea,
input                                 cdm_ras_des_ec_ram_ena,
input                                 cdm_ras_des_ec_ram_enb,
output  [`ep_x4_CX_RAS_DES_EC_RAM_DATA_WIDTH-1:0]  cdm_ras_des_ec_ram_dataout,
// Port list for RAM instance u_ram_cdm_rasdes_tba_reg of model ram_2p_1c_wrapper
input [`ep_x4_CX_RAS_DES_TBA_RAM_ADDR_WIDTH-1:0] cdm_ras_des_tba_ram_addra,
input [`ep_x4_CX_RAS_DES_TBA_RAM_ADDR_WIDTH-1:0] cdm_ras_des_tba_ram_addrb,
input [`ep_x4_CX_RAS_DES_TBA_RAM_DATA_WIDTH-1:0] cdm_ras_des_tba_ram_datain,
input                                 cdm_ras_des_tba_ram_wea,
input                                 cdm_ras_des_tba_ram_ena,
input                                 cdm_ras_des_tba_ram_enb,
output  [`ep_x4_CX_RAS_DES_TBA_RAM_DATA_WIDTH-1:0] cdm_ras_des_tba_ram_dataout,
// Port list for RAM instance u_cplBuffer_ram of model ram_2p_1c_wrapper
output  [`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CX_DMA_RBUF_SLICE_WD-1:0]    ram2edmarbuff_din,
input [`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CC_DMA_SEG_BUF_NW_ADDR_WIDTH-1:0]  edmarbuff2ram_addra,
input [`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CC_DMA_SEG_BUF_NW_ADDR_WIDTH-1:0]  edmarbuff2ram_addrb,
input [`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CX_DMA_RBUF_SLICE_WD-1:0]     edmarbuff2ram_dout,
input [`ep_x4_CX_DMA_RBUF_NSLICES-1:0]                            edmarbuff2ram_re,
input [`ep_x4_CX_DMA_RBUF_NSLICES-1:0]                            edmarbuff2ram_we,
// Port list for RAM instance u_edmapfRdEng_c2w_lut_ram of model ram_2p_1c_wrapper
input         [`ep_x4_CC_IF_RD_CTXC2W_RAM_PW-1:0] edma_rd_eng_c2w_lut_addra_ram,
input         [`ep_x4_CC_IF_RD_CTXC2W_RAM_PW-1:0] edma_rd_eng_c2w_lut_addrb_ram,
input         [`ep_x4_CC_IF_RD_CTXC2W_RAM_WD-1:0] edma_rd_eng_c2w_lut_dout_ram,
input                                       edma_rd_eng_c2w_lut_we_ram,
input                                       edma_rd_eng_c2w_lut_re_ram,
output          [`ep_x4_CC_IF_RD_CTXC2W_RAM_WD-1:0] edma_rd_eng_c2w_lut_din_ram,
// Port list for RAM instance u_edmapfRdEng_ctrl_ll_ram of model ram_2p_1c_wrapper
input         [`ep_x4_CC_IF_RDCTRL_LL_RAM_PW-1:0] edma_rd_eng_ll_addra_ram,
input         [`ep_x4_CC_IF_RDCTRL_LL_RAM_PW-1:0] edma_rd_eng_ll_addrb_ram,
input         [`ep_x4_CC_IF_RDCTRL_LL_RAM_WD-1:0] edma_rd_eng_ll_dout_ram,
input                                       edma_rd_eng_ll_we_ram,
input                                       edma_rd_eng_ll_re_ram,
output          [`ep_x4_CC_IF_RDCTRL_LL_RAM_WD-1:0] edma_rd_eng_ll_din_ram,
  // Port list for RAM instance u_edmapfRdEng_llq_ovrl_ram of model ram_2p_1c_wrapper
input [`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_PW-1:0] edma_rd_eng_ovrl_addra_ram,
input [`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_PW-1:0] edma_rd_eng_ovrl_addrb_ram,
input [`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_WD-1:0] edma_rd_eng_ovrl_dout_ram,
input                                       edma_rd_eng_ovrl_we_ram,
input                                       edma_rd_eng_ovrl_re_ram,
output  [`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_WD-1:0] edma_rd_eng_ovrl_din_ram,
// Port list for RAM instance u_edmapfRdEng_msi_ram of model ram_2p_1c_wrapper
input            [`ep_x4_CC_IF_RD_MSI_RAM_PW-1:0] edma_rd_eng_msi_addra_ram,
input            [`ep_x4_CC_IF_RD_MSI_RAM_PW-1:0] edma_rd_eng_msi_addrb_ram,
input            [`ep_x4_CC_IF_RD_MSI_RAM_WD-1:0] edma_rd_eng_msi_dout_ram,
input                                       edma_rd_eng_msi_we_ram,
input                                       edma_rd_eng_msi_re_ram,
output             [`ep_x4_CC_IF_RD_MSI_RAM_WD-1:0] edma_rd_eng_msi_din_ram,
// Port list for RAM instance u_edmapfRdEng_stsh_lut_ram of model ram_2p_1c_wrapper
input        [`ep_x4_CC_IF_RD_CTXSTSH_RAM_PW-1:0] edma_rd_eng_stsh_lut_addra_ram,
input        [`ep_x4_CC_IF_RD_CTXSTSH_RAM_PW-1:0] edma_rd_eng_stsh_lut_addrb_ram,
input        [`ep_x4_CC_IF_RD_CTXSTSH_RAM_WD-1:0] edma_rd_eng_stsh_lut_dout_ram,
input                                       edma_rd_eng_stsh_lut_we_ram,
input                                       edma_rd_eng_stsh_lut_re_ram,
output         [`ep_x4_CC_IF_RD_CTXSTSH_RAM_WD-1:0] edma_rd_eng_stsh_lut_din_ram,
// Port list for RAM instance u_edmapfWrEng_c2w_lut_ram of model ram_2p_1c_wrapper
input         [`ep_x4_CC_IF_WR_CTXC2W_RAM_PW-1:0] edma_wr_eng_c2w_lut_addra_ram,
input         [`ep_x4_CC_IF_WR_CTXC2W_RAM_PW-1:0] edma_wr_eng_c2w_lut_addrb_ram,
input         [`ep_x4_CC_IF_WR_CTXC2W_RAM_WD-1:0] edma_wr_eng_c2w_lut_dout_ram,
input                                       edma_wr_eng_c2w_lut_we_ram,
input                                       edma_wr_eng_c2w_lut_re_ram,
output          [`ep_x4_CC_IF_WR_CTXC2W_RAM_WD-1:0] edma_wr_eng_c2w_lut_din_ram,
// Port list for RAM instance u_edmapfWrEng_ctrl_ll_ram of model ram_2p_1c_wrapper
input         [`ep_x4_CC_IF_WRCTRL_LL_RAM_PW-1:0] edma_wr_eng_ll_addra_ram,
input         [`ep_x4_CC_IF_WRCTRL_LL_RAM_PW-1:0] edma_wr_eng_ll_addrb_ram,
input         [`ep_x4_CC_IF_WRCTRL_LL_RAM_WD-1:0] edma_wr_eng_ll_dout_ram,
input                                       edma_wr_eng_ll_we_ram,
input                                       edma_wr_eng_ll_re_ram,
output          [`ep_x4_CC_IF_WRCTRL_LL_RAM_WD-1:0] edma_wr_eng_ll_din_ram,  
// Port list for RAM instance u_edmapfWrEng_llq_ovrl_ram of model ram_2p_1c_wrapper
input [`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_PW-1:0] edma_wr_eng_ovrl_addra_ram,
input [`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_PW-1:0] edma_wr_eng_ovrl_addrb_ram,
input [`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_WD-1:0] edma_wr_eng_ovrl_dout_ram,
input                                       edma_wr_eng_ovrl_we_ram,
input                                       edma_wr_eng_ovrl_re_ram,
output  [`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_WD-1:0] edma_wr_eng_ovrl_din_ram,
// Port list for RAM instance u_edmapfWrEng_msi_ram of model ram_2p_1c_wrapper
input            [`ep_x4_CC_IF_WR_MSI_RAM_PW-1:0] edma_wr_eng_msi_addra_ram,
input            [`ep_x4_CC_IF_WR_MSI_RAM_PW-1:0] edma_wr_eng_msi_addrb_ram,
input            [`ep_x4_CC_IF_WR_MSI_RAM_WD-1:0] edma_wr_eng_msi_dout_ram,
input                                       edma_wr_eng_msi_we_ram,
input                                       edma_wr_eng_msi_re_ram,
output             [`ep_x4_CC_IF_WR_MSI_RAM_WD-1:0] edma_wr_eng_msi_din_ram,
// Port list for RAM instance u_edmapfWrEng_stsh_lut_ram of model ram_2p_1c_wrapper
input        [`ep_x4_CC_IF_WR_CTXSTSH_RAM_PW-1:0] edma_wr_eng_stsh_lut_addra_ram,
input        [`ep_x4_CC_IF_WR_CTXSTSH_RAM_PW-1:0] edma_wr_eng_stsh_lut_addrb_ram,
input        [`ep_x4_CC_IF_WR_CTXSTSH_RAM_WD-1:0] edma_wr_eng_stsh_lut_dout_ram,
input                                       edma_wr_eng_stsh_lut_we_ram,
input                                       edma_wr_eng_stsh_lut_re_ram,
output         [`ep_x4_CC_IF_WR_CTXSTSH_RAM_WD-1:0] edma_wr_eng_stsh_lut_din_ram,
// Port list for RAM instance u3_ram_radm_qbuffer_data of model ram_2p_1c_wrapper
output   [`ep_x4_CX_RADM_Q_DATABITS_OUT-1:0]     p_dataq_dataout,
input  [`ep_x4_CX_RADM_PQ_D_ADDRBITS-1:0]    p_dataq_addra,
input  [`ep_x4_CX_RADM_PQ_D_ADDRBITS-1:0]    p_dataq_addrb,
input  [`ep_x4_CX_RADM_Q_DATABITS-1:0]       p_dataq_datain,
input  [`ep_x4_CX_RADM_Q_D_CTRLBITS-1:0]     p_dataq_ena,
input  [`ep_x4_CX_RADM_Q_D_CTRLBITS-1:0]     p_dataq_enb,
input  [`ep_x4_CX_RADM_Q_D_CTRLBITS-1:0]     p_dataq_wea,
// Port list for RAM instance u0_ram_radm_qbuffer_hdr of model ram_2p_1c_wrapper
output   [`ep_x4_CX_RADM_PQ_H_DATABITS_OUT-1:0]  p_hdrq_dataout,
input  [`ep_x4_CX_RADM_PQ_H_ADDRBITS-1:0]    p_hdrq_addra,
input  [`ep_x4_CX_RADM_PQ_H_ADDRBITS-1:0]    p_hdrq_addrb,
input  [`ep_x4_CX_RADM_PQ_H_DATABITS-1:0]    p_hdrq_datain,
input  [`ep_x4_CX_RADM_Q_H_CTRLBITS-1:0]     p_hdrq_ena,
input  [`ep_x4_CX_RADM_Q_H_CTRLBITS-1:0]     p_hdrq_enb,
input  [`ep_x4_CX_RADM_Q_H_CTRLBITS-1:0]     p_hdrq_wea,
// Port list for RAM instance u_ram_1p_rbuf of model ram_1p_wrapper
input  [`ep_x4_RBUF_PW -1:0]              xdlh_retryram_addr,
input  [`ep_x4_RBUF_WIDTH-1:0]           xdlh_retryram_data,
input                              xdlh_retryram_we,
input                              xdlh_retryram_en,
output   [`ep_x4_RBUF_WIDTH-1:0]           retryram_xdlh_data,
// Port list for RAM instance u_ram_2p_sotbuf of model ram_2p_1c_wrapper
input  [`ep_x4_SOTBUF_L2DEPTH -1:0]            xdlh_retrysotram_waddr,
input  [`ep_x4_SOTBUF_L2DEPTH -1:0]            xdlh_retrysotram_raddr,
input  [`ep_x4_SOTBUF_WIDTH -1:0]            xdlh_retrysotram_data,
input                              xdlh_retrysotram_we,
input                              xdlh_retrysotram_en,
output   [`ep_x4_SOTBUF_WIDTH -1:0]            retrysotram_xdlh_data,


  input                                       mstr_aclk_g,
  input                                       slv_aclk_g,
  input                                       radm_clk_g,
  input                                       muxd_aux_clk_g,
  input                                       core_clk

 );


// RAM instance u_ib_mcpl_sb_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_MSTR_CPL_SEG_BUF_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_IB_MCPL_SEG_BUF_RAM_DATA_WD),
  .PW          (`ep_x4_CC_IB_MCPL_SEG_BUF_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_IB_MCPL_SEG_BUF_RAM_DP)
) u_ib_mcpl_sb_ram [1-1:0] (
  .clk         (core_clk), // input
  .addra       (ib_mcpl_sb_ram_addra), // input
  .addrb       (ib_mcpl_sb_ram_addrb), // input
  .dina        (ib_mcpl_sb_ram_dina), // input
  .doutb       (ib_mcpl_sb_ram_doutb), // output
  .ena         (ib_mcpl_sb_ram_wea), // input
  .enb         (ib_mcpl_sb_ram_enb), // input
  .wea         (ib_mcpl_sb_ram_wea) // input
);

// RAM instance u_ib_mcpl_a2c_cdc_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IB_MCPL_CDC_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_IB_MCPL_CDC_RAM_DATA_WD),
  .PW          (`ep_x4_CC_IB_MCPL_CDC_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_IB_MCPL_CDC_RAM_DP_ACTUAL)
) u_ib_mcpl_a2c_cdc_ram (
  .clka        (mstr_aclk_g), // input
  .clkb        (core_clk), // input
  .addra       (ib_mcpl_a2c_cdc_ram_addra), // input
  .addrb       (ib_mcpl_a2c_cdc_ram_addrb), // input
  .dina        (ib_mcpl_a2c_cdc_ram_dina), // input
  .doutb       (ib_mcpl_a2c_cdc_ram_doutb), // output
  .ena         (ib_mcpl_a2c_cdc_ram_wea), // input
  .enb         (ib_mcpl_a2c_cdc_ram_enb), // input
  .wea         (ib_mcpl_a2c_cdc_ram_wea) // input
);

// RAM instance u_ib_rreq_ordr_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IB_RD_REQ_ORDR_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_IB_RD_REQ_ORDR_RAM_DATA_WD),
  .PW          (`ep_x4_CC_IB_RD_REQ_ORDR_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_IB_RD_REQ_ORDR_RAM_DP)
) u_ib_rreq_ordr_ram (
  .clk         (core_clk), // input
  .addra       (ib_rreq_ordr_ram_addra), // input
  .addrb       (ib_rreq_ordr_ram_addrb), // input
  .dina        (ib_rreq_ordr_ram_dina), // input
  .doutb       (ib_rreq_ordr_ram_doutb), // output
  .ena         (ib_rreq_ordr_ram_wea), // input
  .enb         (ib_rreq_ordr_ram_enb), // input
  .wea         (ib_rreq_ordr_ram_wea) // input
);

// RAM instance u_ib_rreq_c2a_cdc_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IB_RD_REQ_CDC_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_IB_RD_REQ_CDC_RAM_DATA_WD),
  .PW          (`ep_x4_CC_IB_RD_REQ_CDC_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_IB_RD_REQ_CDC_RAM_DP_ACTUAL)
) u_ib_rreq_c2a_cdc_ram (
  .clka        (core_clk), // input
  .clkb        (mstr_aclk_g), // input
  .addra       (ib_rreq_c2a_cdc_ram_addra), // input
  .addrb       (ib_rreq_c2a_cdc_ram_addrb), // input
  .dina        (ib_rreq_c2a_cdc_ram_dina), // input
  .doutb       (ib_rreq_c2a_cdc_ram_doutb), // output
  .ena         (ib_rreq_c2a_cdc_ram_wea), // input
  .enb         (ib_rreq_c2a_cdc_ram_enb), // input
  .wea         (ib_rreq_c2a_cdc_ram_wea) // input
);

// RAM instance u_ib_wreq_c2a_cdc_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IB_WR_REQ_CDC_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_IB_WR_REQ_CDC_RAM_DATA_WD),
  .PW          (`ep_x4_CC_IB_WR_REQ_CDC_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_IB_WR_REQ_CDC_RAM_DP_ACTUAL)
) u_ib_wreq_c2a_cdc_ram (
  .clka        (core_clk), // input
  .clkb        (mstr_aclk_g), // input
  .addra       (ib_wreq_c2a_cdc_ram_addra), // input
  .addrb       (ib_wreq_c2a_cdc_ram_addrb), // input
  .dina        (ib_wreq_c2a_cdc_ram_dina), // input
  .doutb       (ib_wreq_c2a_cdc_ram_doutb), // output
  .ena         (ib_wreq_c2a_cdc_ram_wea), // input
  .enb         (ib_wreq_c2a_cdc_ram_enb), // input
  .wea         (ib_wreq_c2a_cdc_ram_wea) // input
);

// RAM instance u_ob_ccmp_data_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_OB_CCMP_DATA_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_OB_CCMP_DATA_RAM_DATA_WD),
  .PW          (`ep_x4_CC_OB_CCMP_NSLICES*`ep_x4_CC_OB_CCMP_DATA_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_OB_CCMP_DATA_RAM_DP)
) u_ob_ccmp_data_ram [1-1:0] (
  .clka        (core_clk), // input
  .clkb        (slv_aclk_g), // input
  .addra       (ob_ccmp_data_ram_addra), // input
  .addrb       (ob_ccmp_data_ram_addrb), // input
  .dina        (ob_ccmp_data_ram_dina), // input
  .doutb       (ob_ccmp_data_ram_doutb), // output
  .ena         (ob_ccmp_data_ram_wea), // input
  .enb         (ob_ccmp_data_ram_enb), // input
  .wea         (ob_ccmp_data_ram_wea) // input
);

// RAM instance u_ob_npdcmp_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_OB_NPDCMP_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_OB_NPDCMP_RAM_DATA_WD),
  .PW          (`ep_x4_CC_OB_NPDCMP_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_OB_NPDCMP_RAM_DP)
) u_ob_npdcmp_ram (
  .clka        (slv_aclk_g), // input
  .clkb        (core_clk), // input
  .addra       (ob_npdcmp_ram_addra), // input
  .addrb       (ob_npdcmp_ram_addrb), // input
  .dina        (ob_npdcmp_ram_dina), // input
  .doutb       (ob_npdcmp_ram_doutb), // output
  .ena         (ob_npdcmp_ram_wea), // input
  .enb         (ob_npdcmp_ram_enb), // input
  .wea         (ob_npdcmp_ram_wea) // input
);

// RAM instance u_slv_npw_sab_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_SLV_NPW_SAB_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_SLV_NPW_SAB_RAM_DATA_WD),
  .PW          (`ep_x4_CC_SLV_NPW_SAB_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_SLV_NPW_SAB_RAM_DP)
) u_slv_npw_sab_ram (
  .clk         (slv_aclk_g), // input
  .addra       (slv_npw_sab_ram_addra), // input
  .addrb       (slv_npw_sab_ram_addrb), // input
  .dina        (slv_npw_sab_ram_dina), // input
  .doutb       (slv_npw_sab_ram_doutb), // output
  .ena         (slv_npw_sab_ram_wea), // input
  .enb         (slv_npw_sab_ram_enb), // input
  .wea         (slv_npw_sab_ram_wea) // input
);

// RAM instance u_ob_pdcmp_data_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_OB_PDCMP_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_OB_PDCMP_DATA_RAM_DATA_WD),
  .PW          (`ep_x4_CC_OB_PDCMP_DATA_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_OB_PDCMP_DATA_RAM_DP_ACTUAL)
) u_ob_pdcmp_data_ram (
  .clka        (slv_aclk_g), // input
  .clkb        (core_clk), // input
  .addra       (ob_pdcmp_data_ram_addra), // input
  .addrb       (ob_pdcmp_data_ram_addrb), // input
  .dina        (ob_pdcmp_data_ram_dina), // input
  .doutb       (ob_pdcmp_data_ram_doutb), // output
  .ena         (ob_pdcmp_data_ram_wea), // input
  .enb         (ob_pdcmp_data_ram_enb), // input
  .wea         (ob_pdcmp_data_ram_wea) // input
);

// RAM instance u_ob_pdcmp_hdr_ram of model ram_2p_2c_wrapper
ram_2p_2c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_OB_PDCMP_RAM_RD_LATENCY),
  .WD          (`ep_x4_CC_OB_PDCMP_HDR_RAM_DATA_WD),
  .PW          (`ep_x4_CC_OB_PDCMP_HDR_RAM_ADDR_WD),
  .DP          (`ep_x4_CC_OB_PDCMP_HDR_RAM_DP)
) u_ob_pdcmp_hdr_ram (
  .clka        (slv_aclk_g), // input
  .clkb        (core_clk), // input
  .addra       (ob_pdcmp_hdr_ram_addra), // input
  .addrb       (ob_pdcmp_hdr_ram_addrb), // input
  .dina        (ob_pdcmp_hdr_ram_dina), // input
  .doutb       (ob_pdcmp_hdr_ram_doutb), // output
  .ena         (ob_pdcmp_hdr_ram_wea), // input
  .enb         (ob_pdcmp_hdr_ram_enb), // input
  .wea         (ob_pdcmp_hdr_ram_wea) // input
);

// RAM instance u_ram_cdm_rasdes_ec_reg of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (1),
  .WD          (`ep_x4_CX_RAS_DES_EC_RAM_DATA_WIDTH),
  .PW          (`ep_x4_CX_RAS_DES_EC_RAM_ADDR_WIDTH),
  .DP          (`ep_x4_CX_RAS_DES_EC_RAM_DEPTH)
) u_ram_cdm_rasdes_ec_reg (
  .clk         (muxd_aux_clk_g), // input
  .addra       (cdm_ras_des_ec_ram_addra), // input
  .addrb       (cdm_ras_des_ec_ram_addrb), // input
  .dina        (cdm_ras_des_ec_ram_datain), // input
  .doutb       (cdm_ras_des_ec_ram_dataout), // output
  .ena         (cdm_ras_des_ec_ram_ena), // input
  .enb         (cdm_ras_des_ec_ram_enb), // input
  .wea         (cdm_ras_des_ec_ram_wea) // input
);

// RAM instance u_ram_cdm_rasdes_tba_reg of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (1),
  .WD          (`ep_x4_CX_RAS_DES_TBA_RAM_DATA_WIDTH),
  .PW          (`ep_x4_CX_RAS_DES_TBA_RAM_ADDR_WIDTH),
  .DP          (`ep_x4_CX_RAS_DES_TBA_RAM_DEPTH)
) u_ram_cdm_rasdes_tba_reg (
  .clk         (muxd_aux_clk_g), // input
  .addra       (cdm_ras_des_tba_ram_addra), // input
  .addrb       (cdm_ras_des_tba_ram_addrb), // input
  .dina        (cdm_ras_des_tba_ram_datain), // input
  .doutb       (cdm_ras_des_tba_ram_dataout), // output
  .ena         (cdm_ras_des_tba_ram_ena), // input
  .enb         (cdm_ras_des_tba_ram_enb), // input
  .wea         (cdm_ras_des_tba_ram_wea) // input
);

// RAM instance u_cplBuffer_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_DMA_SEG_BUF_RAM_LATENCY),
  .WD          (`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CX_DMA_RBUF_SLICE_WD),
  .PW          (`ep_x4_CX_DMA_RBUF_NSLICES*`ep_x4_CC_DMA_SEG_BUF_NW_ADDR_WIDTH),
  .DP          (`ep_x4_CC_DMA_SEG_BUF_DEPTH)
) u_cplBuffer_ram [1-1:0] (
  .clk         (core_clk), // input
  .addra       (edmarbuff2ram_addra), // input
  .addrb       (edmarbuff2ram_addrb), // input
  .dina        (edmarbuff2ram_dout), // input
  .doutb       (ram2edmarbuff_din), // output
  .ena         (edmarbuff2ram_we), // input
  .enb         (edmarbuff2ram_re), // input
  .wea         (edmarbuff2ram_we) // input
);

// RAM instance u_edmapfRdEng_c2w_lut_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_RD_CTXC2W_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_RD_CTXC2W_RAM_WD),
  .PW          (`ep_x4_CC_IF_RD_CTXC2W_RAM_PW),
  .DP          (`ep_x4_CC_IF_RD_CTXC2W_RAM_DP)
) u_edmapfRdEng_c2w_lut_ram (
  .clk         (core_clk), // input
  .addra       (edma_rd_eng_c2w_lut_addra_ram), // input
  .addrb       (edma_rd_eng_c2w_lut_addrb_ram), // input
  .dina        (edma_rd_eng_c2w_lut_dout_ram), // input
  .doutb       (edma_rd_eng_c2w_lut_din_ram), // output
  .ena         (edma_rd_eng_c2w_lut_we_ram), // input
  .enb         (edma_rd_eng_c2w_lut_re_ram), // input
  .wea         (edma_rd_eng_c2w_lut_we_ram) // input
);

// RAM instance u_edmapfRdEng_ctrl_ll_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_RDCTRL_LL_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_RDCTRL_LL_RAM_WD),
  .PW          (`ep_x4_CC_IF_RDCTRL_LL_RAM_PW),
  .DP          (`ep_x4_CC_IF_RDCTRL_LL_RAM_DP)
) u_edmapfRdEng_ctrl_ll_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_rd_eng_ll_addra_ram), // input
  .addrb       (edma_rd_eng_ll_addrb_ram), // input
  .dina        (edma_rd_eng_ll_dout_ram), // input
  .doutb       (edma_rd_eng_ll_din_ram), // output
  .ena         (edma_rd_eng_ll_we_ram), // input
  .enb         (edma_rd_eng_ll_re_ram), // input
  .wea         (edma_rd_eng_ll_we_ram) // input
);

// RAM instance u_edmapfRdEng_llq_ovrl_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_WD),
  .PW          (`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_PW),
  .DP          (`ep_x4_CC_IF_RDCTX_LLQ_OVERLAY_RAM_DP)
) u_edmapfRdEng_llq_ovrl_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_rd_eng_ovrl_addra_ram), // input
  .addrb       (edma_rd_eng_ovrl_addrb_ram), // input
  .dina        (edma_rd_eng_ovrl_dout_ram), // input
  .doutb       (edma_rd_eng_ovrl_din_ram), // output
  .ena         (edma_rd_eng_ovrl_we_ram), // input
  .enb         (edma_rd_eng_ovrl_re_ram), // input
  .wea         (edma_rd_eng_ovrl_we_ram) // input
);

// RAM instance u_edmapfRdEng_msi_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_RD_MSI_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_RD_MSI_RAM_WD),
  .PW          (`ep_x4_CC_IF_RD_MSI_RAM_PW),
  .DP          (`ep_x4_CC_IF_RD_MSI_RAM_DP)
) u_edmapfRdEng_msi_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_rd_eng_msi_addra_ram), // input
  .addrb       (edma_rd_eng_msi_addrb_ram), // input
  .dina        (edma_rd_eng_msi_dout_ram), // input
  .doutb       (edma_rd_eng_msi_din_ram), // output
  .ena         (edma_rd_eng_msi_we_ram), // input
  .enb         (edma_rd_eng_msi_re_ram), // input
  .wea         (edma_rd_eng_msi_we_ram) // input
);

// RAM instance u_edmapfRdEng_stsh_lut_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_RD_CTXSTSH_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_RD_CTXSTSH_RAM_WD),
  .PW          (`ep_x4_CC_IF_RD_CTXSTSH_RAM_PW),
  .DP          (`ep_x4_CC_IF_RD_CTXSTSH_RAM_DP)
) u_edmapfRdEng_stsh_lut_ram (
  .clk         (core_clk), // input
  .addra       (edma_rd_eng_stsh_lut_addra_ram), // input
  .addrb       (edma_rd_eng_stsh_lut_addrb_ram), // input
  .dina        (edma_rd_eng_stsh_lut_dout_ram), //input
  .doutb       (edma_rd_eng_stsh_lut_din_ram), // output
  .ena         (edma_rd_eng_stsh_lut_we_ram), // input
  .enb         (edma_rd_eng_stsh_lut_re_ram), // input
  .wea         (edma_rd_eng_stsh_lut_we_ram) // input
);

// RAM instance u_edmapfWrEng_c2w_lut_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_WR_CTXC2W_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_WR_CTXC2W_RAM_WD),
  .PW          (`ep_x4_CC_IF_WR_CTXC2W_RAM_PW),
  .DP          (`ep_x4_CC_IF_WR_CTXC2W_RAM_DP)
) u_edmapfWrEng_c2w_lut_ram (
  .clk         (core_clk), // input
  .addra       (edma_wr_eng_c2w_lut_addra_ram), // input
  .addrb       (edma_wr_eng_c2w_lut_addrb_ram), // input
  .dina        (edma_wr_eng_c2w_lut_dout_ram), // input
  .doutb       (edma_wr_eng_c2w_lut_din_ram), // output
  .ena         (edma_wr_eng_c2w_lut_we_ram), // input
  .enb         (edma_wr_eng_c2w_lut_re_ram), // input
  .wea         (edma_wr_eng_c2w_lut_we_ram) // input
);

// RAM instance u_edmapfWrEng_ctrl_ll_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_WRCTRL_LL_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_WRCTRL_LL_RAM_WD),
  .PW          (`ep_x4_CC_IF_WRCTRL_LL_RAM_PW),
  .DP          (`ep_x4_CC_IF_WRCTRL_LL_RAM_DP)
) u_edmapfWrEng_ctrl_ll_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_wr_eng_ll_addra_ram), // input
  .addrb       (edma_wr_eng_ll_addrb_ram), // input
  .dina        (edma_wr_eng_ll_dout_ram), // input
  .doutb       (edma_wr_eng_ll_din_ram), // output
  .ena         (edma_wr_eng_ll_we_ram), // input
  .enb         (edma_wr_eng_ll_re_ram), // input
  .wea         (edma_wr_eng_ll_we_ram) // input
);

// RAM instance u_edmapfWrEng_llq_ovrl_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_WD),
  .PW          (`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_PW),
  .DP          (`ep_x4_CC_IF_WRCTX_LLQ_OVERLAY_RAM_DP)
) u_edmapfWrEng_llq_ovrl_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_wr_eng_ovrl_addra_ram), // input
  .addrb       (edma_wr_eng_ovrl_addrb_ram), // input
  .dina        (edma_wr_eng_ovrl_dout_ram), // input
  .doutb       (edma_wr_eng_ovrl_din_ram), // output
  .ena         (edma_wr_eng_ovrl_we_ram), // input
  .enb         (edma_wr_eng_ovrl_re_ram), // input
  .wea         (edma_wr_eng_ovrl_we_ram) // input
);

// RAM instance u_edmapfWrEng_msi_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_WR_MSI_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_WR_MSI_RAM_WD),
  .PW          (`ep_x4_CC_IF_WR_MSI_RAM_PW),
  .DP          (`ep_x4_CC_IF_WR_MSI_RAM_DP)
) u_edmapfWrEng_msi_ram (
  .clk         (muxd_aux_clk_g), // input
  .addra       (edma_wr_eng_msi_addra_ram), // input
  .addrb       (edma_wr_eng_msi_addrb_ram), // input
  .dina        (edma_wr_eng_msi_dout_ram), // input
  .doutb       (edma_wr_eng_msi_din_ram), // output
  .ena         (edma_wr_eng_msi_we_ram), // input
  .enb         (edma_wr_eng_msi_re_ram), // input
  .wea         (edma_wr_eng_msi_we_ram) // input
);

// RAM instance u_edmapfWrEng_stsh_lut_ram of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CC_IF_WR_CTXSTSH_RAM_LATENCY),
  .WD          (`ep_x4_CC_IF_WR_CTXSTSH_RAM_WD),
  .PW          (`ep_x4_CC_IF_WR_CTXSTSH_RAM_PW),
  .DP          (`ep_x4_CC_IF_WR_CTXSTSH_RAM_DP)
) u_edmapfWrEng_stsh_lut_ram (
  .clk         (core_clk), // input
  .addra       (edma_wr_eng_stsh_lut_addra_ram), // input
  .addrb       (edma_wr_eng_stsh_lut_addrb_ram), // input
  .dina        (edma_wr_eng_stsh_lut_dout_ram), // input
  .doutb       (edma_wr_eng_stsh_lut_din_ram), // output
  .ena         (edma_wr_eng_stsh_lut_we_ram), // input
  .enb         (edma_wr_eng_stsh_lut_re_ram), // input
  .wea         (edma_wr_eng_stsh_lut_we_ram) // input
);

// RAM instance u3_ram_radm_qbuffer_data of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CX_RADM_RAM_RD_LATENCY),
  .WD          (`ep_x4_CX_RADM_PQ_D_WD),
  .PW          (`ep_x4_CX_RADM_PQ_D_ADDRBITS),
  .DP          (`ep_x4_CX_RADM_DATAQ_DEPTH)
) u3_ram_radm_qbuffer_data [1-1:0] (
  .clk         (radm_clk_g), // input
  .addra       (p_dataq_addra), // input
  .addrb       (p_dataq_addrb), // input
  .dina        (p_dataq_datain), // input
  .doutb       (p_dataq_dataout), // output
  .ena         (p_dataq_ena), // input
  .enb         (p_dataq_enb), // input
  .wea         (p_dataq_wea) // input
);

// RAM instance u0_ram_radm_qbuffer_hdr of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CX_RADM_RAM_RD_LATENCY),
  .WD          (`ep_x4_CX_RADM_PQ_H_WD),
  .PW          (`ep_x4_CX_RADM_PQ_H_ADDRBITS),
  .DP          (`ep_x4_CX_RADM_HDRQ_DEPTH)
) u0_ram_radm_qbuffer_hdr [1-1:0] (
  .clk         (radm_clk_g), // input
  .addra       (p_hdrq_addra), // input
  .addrb       (p_hdrq_addrb), // input
  .dina        (p_hdrq_datain), // input
  .doutb       (p_hdrq_dataout), // output
  .ena         (p_hdrq_ena), // input
  .enb         (p_hdrq_enb), // input
  .wea         (p_hdrq_wea) // input
);

// RAM instance u_ram_1p_rbuf of model ram_1p_wrapper
ram_1p_wrapper #(
  .RD_LATENCY  (`ep_x4_CX_RETRY_RAM_RD_LATENCY),
  .WD          (`ep_x4_RBUF_WIDTH),
  .PW          (`ep_x4_RBUF_PW),
  .DP          (`ep_x4_CX_RBUF_DEPTH)
) u_ram_1p_rbuf (
  .clk         (core_clk), // input
  .addr        (xdlh_retryram_addr), // input
  .din         (xdlh_retryram_data), // input
  .dout        (retryram_xdlh_data), // output
  .en          (xdlh_retryram_en), // input
  .we          (xdlh_retryram_we) // input
);

// RAM instance u_ram_2p_sotbuf of model ram_2p_1c_wrapper
ram_2p_1c_wrapper #(
  .RD_LATENCY  (`ep_x4_CX_RETRY_SOT_RAM_RD_LATENCY),
  .WD          (`ep_x4_SOTBUF_WIDTH),
  .PW          (`ep_x4_SOTBUF_L2DEPTH),
  .DP          (`ep_x4_SOTBUF_DEPTH)
) u_ram_2p_sotbuf (
  .clk         (core_clk), // input
  .addra       (xdlh_retrysotram_waddr), // input
  .addrb       (xdlh_retrysotram_raddr), // input
  .dina        (xdlh_retrysotram_data), // input
  .doutb       (retrysotram_xdlh_data), // output
  .ena         (xdlh_retrysotram_we), // input
  .enb         (xdlh_retrysotram_en), // input
  .wea         (xdlh_retrysotram_we) // input
);



endmodule

