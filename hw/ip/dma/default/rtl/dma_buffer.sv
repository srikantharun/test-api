

module dma_buffer
   # ( parameter   unsigned int DmaBufferAddrW
       parameter   type dma_trans_data_t = default_dma_trans_data_t
     ) 
     ( 
        input     wire                   i_clk,
        input     wire                   i_rst_n,

        input     logic                  i_resp_valid   [NumPorts],
        input     dma_trans_id_t         i_resp_tid     [NumPorts],
        input     dma_trans_data_t       i_resp_data    [NumPorts],


        input     logic                  i_alloc_req    [NumChannels],
        input     logic                  i_alloc_chid   [NumChannels],
        input     dma_trans_size_t       i_alloc_size   [NumChannels],
        output    logic                  o_alloc_gnt    [NumChannels],
        output    dma_trans_id_t         o_alloc_tid    [NumChannels],



     );


  typedef logic [DmaBufferAddrW-1:0] buffer_idx_t;
  typedef logic [$bits(dma_trans_data_t)/8-1:0] data_byte_idx_t;

  buffer_idx_t wr_ptr_q [NumChannels];
  buffer_idx_t rd_ptr_q [NumChannels];
  buffer_idx_t al_ptr_q [NumChannels];
  buffer_idx_t al_cnt_q [NumChannels];

  typedef packed struct = {
    buffer_idx_t    nxt_offset,
    data_byte_idx_t start_offset,
    data_byte_idx_t byte_count,
    logic           sod,             // Start of Descriptor
    logic           sol,             // Start of Line
    logic           eol,             // End of Line
    logic           eod,             // End of Descriptor

  }
  

endmodule
