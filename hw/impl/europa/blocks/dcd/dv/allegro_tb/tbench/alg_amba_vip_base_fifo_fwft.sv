




module alg_amba_vip_base_fifo_fwft #(parameter FIFO_WIDTH=8, FIFO_LOG2_DEPTH=8) (

  input  logic                  clk  ,
  input  logic                  rstn ,
  input  logic                  wreq ,
  input  logic [FIFO_WIDTH-1:0] wdata,
  output logic                  wfull,
  input  logic                  rreq ,
  output logic [FIFO_WIDTH-1:0] rdata,
  output logic                  rempty
);

  logic [FIFO_WIDTH-1:0]    s_array[2**FIFO_LOG2_DEPTH-1:0];
  logic [FIFO_LOG2_DEPTH:0] wptr    ;
  logic [FIFO_LOG2_DEPTH:0] rptr    ;
  logic                     i_wfull ;
  logic                     i_rempty;
  logic                     wren    ;
  logic                     rden    ;

  always  @ (posedge clk )
  if (rstn == 0) begin
    rptr         <= '0;
    wptr         <= '0;
    for (int i = 0; i < 2**FIFO_LOG2_DEPTH; i++)
      s_array[i]      <= '0;
  end else begin
    if (wren == 1) begin
      wptr          <= wptr + 1;
      s_array[wptr[FIFO_LOG2_DEPTH-1:0]] <= wdata;
    end
    if (rden == 1) begin
      rptr          <= rptr + 1;
    end
  end

  assign i_rempty  = (wptr == rptr);
  assign i_wfull   = ((rptr[FIFO_LOG2_DEPTH] != wptr[FIFO_LOG2_DEPTH]) && (rptr[FIFO_LOG2_DEPTH-1:0] == wptr[FIFO_LOG2_DEPTH-1:0]));
  assign wren      = wreq && !i_wfull;
  assign rden      = rreq && !i_rempty;
  assign rdata     = s_array[rptr[FIFO_LOG2_DEPTH-1:0]];
  assign wfull     = i_wfull;
  assign rempty    = i_rempty;

endmodule

