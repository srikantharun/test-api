
module alg_amba_vip_base_delayline_channel #(
  parameter DATA_WIDTH      = 16,
  parameter SHIFT_LOG2      = 6,
  parameter FIFO_LOG2       = 6
)(
  
  input  logic                         clk,
  input  logic                         rstn,
  
  input  logic                         bypass,
  input  logic [FIFO_LOG2-1:0]         nb_req,
  input  logic                         len_valid,
  input  logic [15:0]                  len_value,
  
  output logic                         full_req,
  output logic                         need_len,
  output logic                         empty_req,
  
  input  logic                         s_valid,
  input  logic [DATA_WIDTH-1:0]        s_data,
  output logic                         s_ready,
  
  output logic                         m_valid,
  output logic [DATA_WIDTH-1:0]        m_data,
  input  logic                         m_ready
);

logic                  shift_wreq;
logic                  shift_wfull;
logic                  shift_rreq;
logic [DATA_WIDTH-1:0] shift_rdata;
logic                  shift_rvalid;

logic                  fifo_wreq;
logic [DATA_WIDTH-1:0] fifo_wdata;
logic                  fifo_wfull;
logic                  fifo_rreq;

logic                  req_in_enable; 
logic [FIFO_LOG2-1:0]  nb_req_in;
logic [FIFO_LOG2-1:0]  nb_req_out;


assign need_len = empty_req;
always_ff @(posedge clk) begin
  if (!rstn) begin
    full_req            <= 1'b0;
    empty_req           <= 1'b0;
    req_in_enable       <= 1'b0;
    nb_req_in           <= '0;
    nb_req_out          <= '0;
  end else begin

    
    full_req            <= 1'b0;
    empty_req           <= 1'b0;

    
    if (len_valid) begin
      nb_req_in         <= '0;
      req_in_enable     <= 1'b1;
    end else if (s_valid && s_ready) begin
      nb_req_in         <= nb_req_in + 1;
      if (nb_req_in >= (nb_req-1)) begin
        req_in_enable   <= 1'b0;
        full_req        <= 1'b1;
      end
    end

    
    if (len_valid) begin
      nb_req_out        <= '0;
    end else if (m_valid && m_ready) begin
      nb_req_out        <= nb_req_out + 1;
      if (nb_req_out >= (nb_req-1)) begin
        empty_req       <= 1'b1;
      end
    end

  end
end


assign shift_wreq = s_valid && s_ready;
assign s_ready    = (req_in_enable || bypass) && !shift_wfull;
assign shift_rreq = fifo_wreq;
alg_amba_vip_base_delayline_channel_shift #(
  .FIFO_WIDTH       (DATA_WIDTH),
  .FIFO_LOG2_DEPTH  (SHIFT_LOG2)
) SHIFT (
  .clk                (clk),
  .rstn               (rstn),
  .bypass             (bypass),
  .len_valid          (len_valid),
  .len_value          (len_value[SHIFT_LOG2-1:0]),
  .wreq               (shift_wreq),
  .wdata              (s_data),
  .wfull              (shift_wfull),
  .rreq               (shift_rreq),
  .rdata              (shift_rdata),
  .rvalid             (shift_rvalid)
);


assign fifo_wreq    = shift_rvalid && !fifo_wfull;
assign fifo_wdata   = shift_rdata;
assign fifo_rreq    = m_valid && m_ready;
alg_amba_vip_base_fifo #(
  .FIFO_WIDTH      (DATA_WIDTH),
  .FIFO_LOG2_DEPTH (FIFO_LOG2)
) FIFO (
  .clk             (clk),
  .rstn            (rstn),
  .wreq            (fifo_wreq),
  .wdata           (fifo_wdata),
  .wfull           (fifo_wfull),
  .rreq            (fifo_rreq),
  .rdata           (m_data),
  .rvalid          (m_valid),
  .rempty          ()
);

endmodule
