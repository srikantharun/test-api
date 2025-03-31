
module alg_amba_vip_base_delayline #(
  parameter DATA_WIDTH      = 16,
  parameter DELAYLINE_OUTSTANDING_LOG2 = 6
)(
  
  input  logic                         clk,
  input  logic                         rstn,
  
  input  logic [15:0]                  distr_value,
  input  logic [DELAYLINE_OUTSTANDING_LOG2-1:0] distr_nbreq,
  input  logic                         distr_enable,
  input  logic                         distr_rstptr,
  input  logic                         distr_write,
  input  logic [15:0]                  distr_seed,
  
  input  logic                         s_valid,
  input  logic [DATA_WIDTH-1:0]        s_data,
  output logic                         s_ready,
  
  output logic                         m_valid,
  output logic [DATA_WIDTH-1:0]        m_data,
  input  logic                         m_ready
);

localparam NUM_CHANNEL               = 2;

localparam TABLE_WIDTH               = 11; 
localparam TABLE_LOG2_DEPTH          = 8;  

localparam CHANNEL_SHIFT_LOG2_DEPTH  = TABLE_WIDTH;
localparam CHANNEL_FIFO_LOG2_DEPTH   = DELAYLINE_OUTSTANDING_LOG2; 

logic [NUM_CHANNEL-1:0]                   channel_input_selected;
logic [NUM_CHANNEL-1:0]                   channel_output_selected;
logic [NUM_CHANNEL-1:0]                   channel_next_in;
logic [NUM_CHANNEL-1:0]                   channel_need_len;
logic [NUM_CHANNEL-1:0]                   channel_next_out;
logic [NUM_CHANNEL-1:0]                   s_channel_valid;
logic [NUM_CHANNEL-1:0] [DATA_WIDTH-1:0]  s_channel_data;
logic [NUM_CHANNEL-1:0]                   s_channel_ready;
logic [NUM_CHANNEL-1:0]                   m_channel_valid;
logic [NUM_CHANNEL-1:0] [DATA_WIDTH-1:0]  m_channel_data;
logic [NUM_CHANNEL-1:0]                   m_channel_ready;
logic [NUM_CHANNEL-1:0]                   len_valid;
logic [NUM_CHANNEL-1:0] [15:0]            len_value;

logic [NUM_CHANNEL-1:0]                   table_channel_selected;
logic                                     table_channel_selected_before_last;
logic                                     channel_len_init;

logic                                     i_m_valid;
logic [DATA_WIDTH-1:0]                    i_m_data;
logic                                     i_m_ready;

logic [TABLE_WIDTH-1:0]                   table_mem[2**TABLE_LOG2_DEPTH-1:0];
logic [TABLE_LOG2_DEPTH-1:0]              table_wptr;
logic [15:0]                              table_rptr;
logic                                     table_rreq;
logic                                     table_rreq_pending;
logic [TABLE_WIDTH-1:0]                   table_q;
logic                                     table_qvalid;

logic [15:0]                              table_rptr_next_lfsr;


alg_amba_vip_base_vldrdy_pipe #(
  .RSTPOL     (0),
  .NO_PIPE    (0),
  .DATA_WIDTH (DATA_WIDTH)
) PIPE (
  .rstn       (rstn),
  .clk        (clk),
  .in_valid   (i_m_valid),
  .in_data    (i_m_data),
  .in_ready   (i_m_ready),
  .out_valid  (m_valid),
  .out_data   (m_data),
  .out_ready  (m_ready)
);


assign table_rptr_next_lfsr[0]     = table_rptr[3] ^ table_rptr[12] ^ table_rptr[14] ^ table_rptr[15];
assign table_rptr_next_lfsr[15:1]  = table_rptr[14:0];
always_ff @(posedge clk) begin
  if (!rstn) begin
    table_wptr    <= '0;
    table_rptr    <= '0;
    table_qvalid  <= 1'b0;
    table_q       <= '0;
  end else begin
    table_qvalid            <= 1'b0;
    if (distr_rstptr) begin
      table_wptr    <= '0;
      table_rptr    <= distr_seed;
    end
    if (distr_write) begin
      table_mem[table_wptr] <= distr_value[TABLE_WIDTH-1:0];
      table_wptr            <= table_wptr + 1;
    end
    if (table_rreq) begin
      table_q               <= table_mem[table_rptr[TABLE_LOG2_DEPTH-1:0]];
      table_rptr            <= table_rptr_next_lfsr;
      table_qvalid          <= 1'b1;
    end
  end
end


generate
if (NUM_CHANNEL == 1) begin: g_channel_single

  assign channel_input_selected             = '1;
  assign channel_output_selected            = '1;
  assign table_channel_selected             = '1;
  assign table_channel_selected_before_last = '1;

end else begin: g_channel_multiple

  
  always_ff @(posedge clk) begin
    if (!rstn) begin
      channel_input_selected    <= '0;
      channel_input_selected[0] <= 1'b1;
    end else begin
      if (distr_rstptr) begin
        channel_input_selected    <= '0;
        channel_input_selected[0] <= 1'b1;
      end else if (distr_enable && (channel_next_in > 0)) begin
        channel_input_selected <= {channel_input_selected[NUM_CHANNEL-2:0], channel_input_selected[NUM_CHANNEL-1]};
      end
    end
  end

  
  always_ff @(posedge clk) begin
    if (!rstn) begin
      channel_output_selected    <= '0;
      channel_output_selected[0] <= 1'b1;
    end else begin
      if (distr_rstptr) begin
        channel_output_selected    <= '0;
        channel_output_selected[0] <= 1'b1;
      end else if (distr_enable && (channel_next_out > 0)) begin
        channel_output_selected <= {channel_output_selected[NUM_CHANNEL-2:0], channel_output_selected[NUM_CHANNEL-1]};
      end
    end
  end

  
  assign table_channel_selected_before_last = table_channel_selected[NUM_CHANNEL-2];
  always_ff @(posedge clk) begin
    if (!rstn) begin
      table_channel_selected    <= '0;
      table_channel_selected[0] <= 1'b1;
    end else begin
      if (distr_rstptr) begin
        table_channel_selected    <= '0;
        table_channel_selected[0] <= 1'b1;
      end else if (table_qvalid) begin
        table_channel_selected   <= {table_channel_selected[NUM_CHANNEL-2:0], table_channel_selected[NUM_CHANNEL-1]};
      end
    end
  end

end
endgenerate


always_ff @(posedge clk) begin
  if (!rstn) begin
    channel_len_init          <= 1'b0;
    table_rreq             <= 1'b0;
    table_rreq_pending     <= 1'b0;
  end else begin

    
    if (distr_rstptr) begin
      channel_len_init          <= 1'b1;
    end

    
    if (table_qvalid) begin
      table_rreq_pending    <= 1'b0;
    end

    
    table_rreq              <= 1'b0;
    if (channel_len_init) begin
      table_rreq_pending    <= 1'b0;
      if (table_qvalid && table_channel_selected_before_last) begin
        channel_len_init       <= 1'b0;
      end else begin
        table_rreq          <= 1'b1;
      end
    end else begin
      if ((channel_need_len & table_channel_selected) && !table_rreq_pending) begin
        table_rreq          <= 1'b1;
        table_rreq_pending  <= 1'b1;
      end
    end

  end
end


assign s_ready   = ((channel_input_selected & s_channel_ready) > 0) ? 1'b1 : 1'b0;
always @(m_channel_valid, i_m_ready, m_channel_data, channel_output_selected)
begin
  i_m_data      <= m_channel_data[0];
  m_channel_ready  <= '0;
  i_m_valid     <= m_channel_valid[0];
  for (int j=0; j < NUM_CHANNEL; j++) begin
    if (channel_output_selected[j] == 1'b1) begin
      m_channel_ready[j] <= i_m_ready;
      i_m_data        <= m_channel_data[j];
      i_m_valid       <= m_channel_valid[j];
    end
  end
end
genvar i;
generate
for (i = 0; i < NUM_CHANNEL; i++) begin: g_channel

  assign s_channel_valid[i] = channel_input_selected[i] ? s_valid : 1'b0;
  assign s_channel_data[i]  = s_data;

  assign len_valid[i]                    = table_qvalid & table_channel_selected[i];
  assign len_value[i][15:TABLE_WIDTH]    = '0;
  assign len_value[i][TABLE_WIDTH-1:0]   = table_q;

  alg_amba_vip_base_delayline_channel #(
    .DATA_WIDTH      (DATA_WIDTH),
    .SHIFT_LOG2      (CHANNEL_SHIFT_LOG2_DEPTH),
    .FIFO_LOG2       (CHANNEL_FIFO_LOG2_DEPTH)
  ) TABLE (
    .clk             (clk),
    .rstn            (rstn),
    .bypass          (~distr_enable),
    .nb_req          (distr_nbreq),
    .len_valid       (len_valid[i]),
    .len_value       (len_value[i]),
    .full_req        (channel_next_in[i]),
    .need_len        (channel_need_len[i]),
    .empty_req       (channel_next_out[i]),
    .s_valid         (s_channel_valid[i]),
    .s_data          (s_channel_data[i]),
    .s_ready         (s_channel_ready[i]),
    .m_valid         (m_channel_valid[i]),
    .m_data          (m_channel_data[i]),
    .m_ready         (m_channel_ready[i])
  );
end

endgenerate

endmodule
