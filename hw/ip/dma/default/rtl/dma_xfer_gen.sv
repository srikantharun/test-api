module dma_src_xfer_gen 
  import dma_pkg::*;
  #(
    parameters
  ) 
  (
    input  wire           i_clk,
    input  wire           i_rst_n,

    input  dma_chnl_cfg_t i_cfg,

    input  logic          i_dsc_req,
    output logic          o_dsc_gnt,
    input  dma_dsc_end_t  i_dsc_src,
    input  dma_dsc_end_t  i_dsc_dst,

    input  dma_ctl_t      i_ctl,
    output dma_sts_t      o_sts,

    output logic          o_xfer_req,
    input  logic          i_xfer_gnt,
    output dma_rd_xfer_t  o_xfer
  );


  always_ff @ (posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      dsc_valid_q <= 1'b0;
    end
    else begin
      if (dsc_load_en) begin
        dsc_valid_q <= 1'b1;
      end
    end
  end
    
endmodule
