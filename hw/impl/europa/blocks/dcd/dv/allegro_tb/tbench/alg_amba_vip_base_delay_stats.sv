


module alg_amba_vip_base_delay_stats #(
  parameter TIMER_WIDTH          = 16,
  parameter OUTSTANDING_LOG2_MAX = 6
)(
  
  input  logic                         clk,
  input  logic                         rstn,
  
  input  logic                         cnt_rst,
  
  input  logic                         send_valid,
  input  logic                         ack_valid,
  
  output logic [63:0]                  delay_total,
  output logic [55:0]                  nb_request,
  output logic [15:0]                  max_value_req,
  output logic [15:0]                  min_value_req,
  output logic                         err_nbreq_overflow,
  output logic                         err_fifo_full,
  output logic                         err_timer_overflow,
  output logic                         err_total_overflow
);

logic [TIMER_WIDTH-1:0]  timer;
logic [64:0]             delay_total_cnt;

logic                    wreq;
logic [TIMER_WIDTH-1:0]  wdata;
logic                    wfull;
logic                    rreq;
logic [TIMER_WIDTH-1:0]  rdata;

assign delay_total    = delay_total_cnt[63:0];

always_ff @(posedge clk) begin
  if (!rstn) begin
    timer                   <= '0;
    wdata                   <= '0;
    wreq                    <= 1'b0;
    rreq                    <= 1'b0;
    err_fifo_full           <= 1'b0;
    err_nbreq_overflow      <= 1'b0;
    err_timer_overflow      <= 1'b0;
    err_total_overflow      <= 1'b0;
    delay_total_cnt         <= '0;
    nb_request              <= '0;
    max_value_req           <= '0;
    min_value_req           <= 16'hFFFF;
  end else begin

    
    if (cnt_rst) begin
      timer                 <= '0;
      err_fifo_full         <= 1'b0;
      err_nbreq_overflow    <= 1'b0;
      err_timer_overflow    <= 1'b0;
      err_total_overflow    <= 1'b0;
      delay_total_cnt       <= '0;
      nb_request            <= '0;
      max_value_req         <= '0;
      min_value_req           <= 16'hFFFF;
    end else begin
      if (timer != '1) begin
        timer               <= timer + 1'b1;
      end
      if (ack_valid) begin
        nb_request          <= nb_request + 1'b1;
        if (nb_request == '1) begin
          err_nbreq_overflow    <= 1'b1;
        end
      end
      if (delay_total_cnt[64]) begin
        err_total_overflow  <= 1'b1;
      end
    end

    
    wreq                    <= 1'b0;
    wdata                   <= timer;
    if (send_valid) begin
      if (timer == '1) begin
        err_timer_overflow  <= 1'b1;
      end
      if (!wfull) begin
        wreq                <= 1'b1;
      end else begin
        err_fifo_full       <= 1'b1;
      end
    end

    
    rreq                    <= 1'b0;
    if (ack_valid) begin
      rreq                  <= 1'b1;
      delay_total_cnt       <= delay_total_cnt + (timer-rdata);

      
      if (min_value_req > (timer-rdata))
        min_value_req       <= (timer-rdata);
      if (max_value_req < (timer-rdata))
        max_value_req       <= (timer-rdata);
    end
  end
end

alg_amba_vip_base_fifo #(
  .FIFO_WIDTH      (TIMER_WIDTH),
  .FIFO_LOG2_DEPTH (OUTSTANDING_LOG2_MAX)
) FIFO (
  .clk             (clk),
  .rstn            (rstn),
  .wreq            (wreq),
  .wdata           (wdata),
  .wfull           (wfull),
  .rreq            (rreq),
  .rdata           (rdata),
  .rvalid          (),
  .rempty          ()
);

endmodule
