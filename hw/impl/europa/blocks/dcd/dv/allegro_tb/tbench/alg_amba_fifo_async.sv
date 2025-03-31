module alg_amba_fifo_async #(parameter DATA_WIDTH = 8) (
  input  logic                  wr_rstn,
  input  logic                  wr_clk,
  input  logic                  wr_valid,
  output logic                  wr_ready,
  input  logic [DATA_WIDTH-1:0] wr_data,
  output logic                  rd_valid,
  input  logic                  rd_ready,
  output logic [DATA_WIDTH-1:0] rd_data,
  input  logic                  rd_rstn,
  input  logic                  rd_clk
);

  localparam FIFO_LOG2_DEPTH=4;
  logic [DATA_WIDTH-1:0]    s_array[2**FIFO_LOG2_DEPTH-1:0];
  logic [DATA_WIDTH-1:0]    s_array_ff[2**FIFO_LOG2_DEPTH-1:0];
  logic [FIFO_LOG2_DEPTH:0] wptr;
  logic [FIFO_LOG2_DEPTH:0] wptr_ff;
  logic [FIFO_LOG2_DEPTH:0] rptr;
  logic [FIFO_LOG2_DEPTH:0] rptr_ff;


  always  @ (posedge wr_clk )
  if (wr_rstn == 0) begin
    wptr         <= '0;
    rptr_ff      <= '0;
    for (int i = 0; i < 2**FIFO_LOG2_DEPTH; i++)
      s_array[i]   <= '0;
  end else begin
    rptr_ff  <= rptr;
    if (wr_valid && wr_ready) begin
      wptr          <= wptr + 1;
      s_array[wptr[FIFO_LOG2_DEPTH-1:0]] <= wr_data;
    end
  end

  assign wr_ready = !((rptr_ff[FIFO_LOG2_DEPTH] != wptr[FIFO_LOG2_DEPTH]) && (rptr_ff[FIFO_LOG2_DEPTH-1:0] == wptr[FIFO_LOG2_DEPTH-1:0]));



  always  @ (posedge rd_clk )
  if (rd_rstn == 0) begin
    rptr         <= '0;
    wptr_ff      <= '0;
    for (int i = 0; i < 2**FIFO_LOG2_DEPTH; i++)
      s_array_ff[i]   <= '0;
  end else begin
    for (int i = 0; i < 2**FIFO_LOG2_DEPTH; i++)
      s_array_ff[i]  <= s_array[i];
    wptr_ff  <= wptr;
    if (rd_ready && rd_valid)
      rptr          <= rptr + 1;
  end

  assign rd_valid = !(wptr_ff == rptr);
  assign rd_data  = s_array_ff[rptr[FIFO_LOG2_DEPTH-1:0]];


endmodule
