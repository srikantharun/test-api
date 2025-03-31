
/* RTL implementation below has been written in stage order.
* That means top of the file is about first stage,
* and bottom of the file is about last stage.
* Stager order is :
*  > fault
*  > delay line
*  > blocking latency
*  > interleaving latency
*/

module alg_amba_vip_channel #(
  parameter DATA_WIDTH = 128,
  parameter ID_WIDTH = 5,
  parameter ID_START = 0,
  parameter ID_END   = 63,
  parameter FAULT_EN = 1,
  parameter FAULT_DATA_WIDTH = 128,
  parameter DELAYLINE_EN = 1,
  parameter DELAYLINE_OUTSTANDING_LOG2 = 6,
  parameter BLOCKING_EN = 1,
  parameter BLOCKING_PROB_EN = 1,
  parameter INTERLEAVING_EN = 1,
  parameter INTERLEAVING_PROB_EN = 1,
  parameter INTERLEAVING_FIFO_LOG2 = 1
)(
  
  input  logic                            clk,
  input  logic                            resetn,
  
  input  logic                            fault_restart,
  input  logic[19:0]                      fault_seed,
  input  logic[19:0]                      fault_probThresReq,
  input  logic[FAULT_DATA_WIDTH-1:0]      fault_regPattern,
  input  logic[3:0]                       fault_cmd,
  input  logic[ID_WIDTH-1:0]              fault_id,
  output logic[31:0]                      fault_stats_lfsr,
  output logic[31:0]                      fault_stats_nberror,
  output logic[31:0]                      fault_stats_nbrequest,
  
  input  logic [15:0]                     delay_distr_value,
  input  logic [DELAYLINE_OUTSTANDING_LOG2-1:0] delay_distr_nbreq,
  input  logic                            delay_distr_enable,
  input  logic                            delay_distr_rstptr,
  input  logic                            delay_distr_write,
  input  logic [15:0]                     delay_distr_seed,
  
  input  logic [7:0]                      blat_proba,
  input  logic [15:0]                     blat_seed,
  input  logic                            blat_seed_rst,
  input  logic [15:0]                     blat_min,
  input  logic [15:0]                     blat_width_mask,
  
  input  logic [2**ID_WIDTH-1:0] [7:0]    ilat_proba,
  input  logic [2**ID_WIDTH-1:0] [15:0]   ilat_seed,
  input  logic [2**ID_WIDTH-1:0]          ilat_seed_rst,
  input  logic [2**ID_WIDTH-1:0] [15:0]   ilat_min,
  input  logic [2**ID_WIDTH-1:0] [15:0]   ilat_width_mask,
  
  output logic                            m_valid,
  output logic [ID_WIDTH-1:0]             m_id,
  output logic [DATA_WIDTH-1:0]           m_data,
  input  logic                            m_ready,
  
  input  logic                            s_valid,
  input  logic [ID_WIDTH-1:0]             s_id,
  input  logic [DATA_WIDTH-1:0]           s_data,
  output logic                            s_ready
);


logic                                             s_fault_valid;
logic [ID_WIDTH-1:0]                              s_fault_id;
logic [DATA_WIDTH-1:0]                            s_fault_data;
logic                                             s_fault_ready;
logic                                             m_fault_valid;
logic [ID_WIDTH-1:0]                              m_fault_id;
logic [DATA_WIDTH-1:0]                            m_fault_data;
logic                                             m_fault_ready;


logic                                             s_delay_valid;
logic [DATA_WIDTH+ID_WIDTH-1:0]                   s_delay_data;
logic                                             s_delay_ready;
logic                                             m_delay_valid;
logic [DATA_WIDTH+ID_WIDTH-1:0]                   m_delay_data;
logic                                             m_delay_ready;


logic                                             s_blat_valid;
logic [DATA_WIDTH+ID_WIDTH-1:0]                   s_blat_data;
logic                                             s_blat_ready;
logic                                             m_blat_valid;
logic [DATA_WIDTH+ID_WIDTH-1:0]                   m_blat_data;
logic                                             m_blat_ready;


logic [2**ID_WIDTH-1:0]                           s_ififo_wreq;
logic [ID_WIDTH-1:0]                              s_ififo_id;
logic [2**ID_WIDTH-1:0] [DATA_WIDTH-1:0]          s_ififo_data;
logic [2**ID_WIDTH-1:0]                           s_ififo_full;
logic [2**ID_WIDTH-1:0]                           m_ififo_rreq;
logic [2**ID_WIDTH-1:0] [DATA_WIDTH-1:0]          m_ififo_data;
logic [2**ID_WIDTH-1:0]                           m_ififo_valid;


logic [2**ID_WIDTH-1:0]                           s_ilat_valid;
logic [2**ID_WIDTH-1:0] [DATA_WIDTH-1:0]          s_ilat_data;
logic [2**ID_WIDTH-1:0]                           s_ilat_ready;
logic [2**ID_WIDTH-1:0]                           m_ilat_valid;
logic [ID_WIDTH-1:0]                              m_ilat_id;
logic [2**ID_WIDTH-1:0] [DATA_WIDTH-1:0]          m_ilat_data;
logic [2**ID_WIDTH-1:0]                           m_ilat_ready;


generate genvar i;

/****************** Fault *********************/

assign s_fault_valid = s_valid;
assign s_fault_id    = s_id;
assign s_fault_data  = s_data;
assign s_ready       = s_fault_ready;

if (FAULT_EN) begin: g_fault

  alg_amba_vip_base_fault #(
    .DATA_WIDTH       (DATA_WIDTH),
    .FAULT_WIDTH      (FAULT_DATA_WIDTH),
    .ID_WIDTH         (ID_WIDTH)
  ) FAULT (
    .clk              (clk),
    .rstn             (resetn),
    .restart          (fault_restart),
    .seed             (fault_seed),
    .probThresReq     (fault_probThresReq),
    .regPattern       (fault_regPattern),
    .cmd              (fault_cmd),
    .id               (fault_id),
    .stats_lfsr       (fault_stats_lfsr),
    .stats_nberror    (fault_stats_nberror),
    .stats_nbrequest  (fault_stats_nbrequest),
    .m_valid          (m_fault_valid),
    .m_id             (m_fault_id),
    .m_data           (m_fault_data),
    .m_ready          (m_fault_ready),
    .s_valid          (s_fault_valid),
    .s_id             (s_fault_id),
    .s_data           (s_fault_data),
    .s_ready          (s_fault_ready)
  );

end else begin: g_nofault

  assign m_fault_valid = s_fault_valid;
  assign m_fault_id    = s_fault_id;
  assign m_fault_data  = s_fault_data;
  assign s_fault_ready = m_fault_ready;

end

/****************** DelayLine *****************/

assign s_delay_valid = m_fault_valid;
assign s_delay_data  = {m_fault_id, m_fault_data};
assign m_fault_ready = s_delay_ready;

if (DELAYLINE_EN) begin: g_delayline

  alg_amba_vip_base_delayline #(
    .DATA_WIDTH          (DATA_WIDTH + ID_WIDTH),
    .DELAYLINE_OUTSTANDING_LOG2(DELAYLINE_OUTSTANDING_LOG2)
  ) DELAYLINE (
    .clk                 (clk),
    .rstn                (resetn),
    .distr_value         (delay_distr_value),
    .distr_nbreq         (delay_distr_nbreq),
    .distr_enable        (delay_distr_enable),
    .distr_rstptr        (delay_distr_rstptr),
    .distr_write         (delay_distr_write),
    .distr_seed          (delay_distr_seed),
    .s_valid             (s_delay_valid),
    .s_data              (s_delay_data),
    .s_ready             (s_delay_ready),
    .m_valid             (m_delay_valid),
    .m_data              (m_delay_data),
    .m_ready             (m_delay_ready)
  );

end else begin: g_nodelayline

  assign m_delay_valid = s_delay_valid;
  assign m_delay_data  = s_delay_data;
  assign s_delay_ready = m_delay_ready;

end

/****************** Blocking ******************/

assign s_blat_valid  = m_delay_valid;
assign s_blat_data   = m_delay_data;
assign m_delay_ready = s_blat_ready;

if (BLOCKING_EN) begin: g_blocking

  alg_amba_vip_base_latency #(
    .DATA_WIDTH         (DATA_WIDTH+ID_WIDTH),
    .PROB_EN            (BLOCKING_PROB_EN)
  ) BLOCKING (
    .clk        (clk),
    .resetn     (resetn),
    .proba      (blat_proba),
    .seed       (blat_seed),
    .seed_rst   (blat_seed_rst),
    .min        (blat_min),
    .width_mask (blat_width_mask),
    .m_valid    (m_blat_valid),
    .m_data     (m_blat_data),
    .m_ready    (m_blat_ready),
    .s_valid    (s_blat_valid),
    .s_data     (s_blat_data),
    .s_ready    (s_blat_ready)
  );

end else begin: g_noblocking

  assign m_blat_valid = s_blat_valid;
  assign m_blat_data  = s_blat_data;
  assign s_blat_ready = m_blat_ready;

end

/****************** Interleaving **************/

if (INTERLEAVING_EN) begin: g_interleaving


  
  assign s_ififo_id    = m_blat_data[ID_WIDTH+DATA_WIDTH-1:DATA_WIDTH];
  always @(s_ififo_full, s_ififo_id) begin
    for (int id = 0; id < 2**ID_WIDTH; id++) begin
      if (s_ififo_id == id) begin
        m_blat_ready  = ~s_ififo_full[id];
      end
    end
  end

  
  for (i = 0; i < 2**ID_WIDTH; i++) begin: g_interleaving

    assign s_ififo_wreq[i] = (s_ififo_id == i) ? (m_blat_valid & m_blat_ready) : 1'b0;
    assign s_ififo_data[i]  = m_blat_data;

    
    if ((ID_START <= i) && (i <= ID_END)) begin: g_id_interleave
      alg_amba_vip_base_fifo #(
        .FIFO_WIDTH        (DATA_WIDTH),
        .FIFO_LOG2_DEPTH   (INTERLEAVING_FIFO_LOG2)
      ) FIFO (
        .clk               (clk),
        .rstn              (resetn),
        .wreq              (s_ififo_wreq[i]),
        .wdata             (s_ififo_data[i]),
        .wfull             (s_ififo_full[i]),
        .rreq              (m_ififo_rreq[i]),
        .rdata             (m_ififo_data[i]),
        .rvalid            (m_ififo_valid[i]),
        .rempty            ()
      );
    end else begin: g_id_nointerleave 
      assign s_ififo_full[i]  = 1'b1;
      assign m_ififo_valid[i] = 1'b0;
      assign m_ififo_data[i]  = '0;
    end

    assign s_ilat_valid[i] =  m_ififo_valid[i];
    assign s_ilat_data[i]  =  m_ififo_data[i];
    assign m_ififo_rreq[i] =  s_ilat_ready[i] & s_ilat_valid[i];

    
    alg_amba_vip_base_latency #(
      .DATA_WIDTH        (DATA_WIDTH),
      .PROB_EN           (INTERLEAVING_PROB_EN)
    ) INTERLEAVING (
      .clk               (clk),
      .resetn            (resetn),
      .proba             (ilat_proba[i]),
      .seed              (ilat_seed[i]),
      .seed_rst          (ilat_seed_rst[i]),
      .min               (ilat_min[i]),
      .width_mask        (ilat_width_mask[i]),
      .m_valid           (m_ilat_valid[i]),
      .m_data            (m_ilat_data[i]),
      .m_ready           (m_ilat_ready[i]),
      .s_valid           (s_ilat_valid[i]),
      .s_data            (s_ilat_data[i]),
      .s_ready           (s_ilat_ready[i])
    );

    assign m_ilat_ready[i] = (m_id == i) ? (m_ilat_valid[i] && m_ready) : 1'b0;

  end

  
  always @(m_ilat_valid, s_ilat_valid) begin
    m_ilat_id      <= '0;
    for (int id = 0; id < 2**ID_WIDTH; id++) begin 
      if (s_ilat_valid[id] == 1'b1) begin
        m_ilat_id  <= id;
      end
    end
    for (int id = 0; id < 2**ID_WIDTH; id++) begin
      if (m_ilat_valid[id] == 1'b1) begin
        m_ilat_id  <= id;
      end
    end
  end

  
  assign m_valid = m_ilat_valid[m_id];
  assign m_data  = m_ilat_data[m_id];
  always_ff @(posedge clk) begin
    if (~resetn) begin
      m_id  <= '0;
    end else begin
      if (~m_valid || m_ready) begin
        m_id  <= m_ilat_id;
      end
    end
  end


end else begin: g_nointerleaving

  assign m_valid      = m_blat_valid;
  assign m_id         = m_blat_data[ID_WIDTH+DATA_WIDTH-1:DATA_WIDTH];
  assign m_data       = m_blat_data[DATA_WIDTH-1:0];
  assign m_blat_ready = m_ready;

end

endgenerate

endmodule
