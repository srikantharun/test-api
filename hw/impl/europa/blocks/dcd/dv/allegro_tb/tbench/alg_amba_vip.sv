


module alg_amba_vip #(
  parameter DATA_WIDTH = 128,
  parameter ID = 1,
  parameter APB_RESYNC = 1,
  parameter ID_START = 0,
  parameter ID_END = 63,
  parameter DELAYLINE_OUTSTANDING_LOG2 = 6
)(
  
  al_vip_apb_if.slavemod               apb,
  
  output logic                         irq,
  
  al_vip_axi_if.slavemod               s_axi,
  al_vip_axi_if.mastermod              m_axi,
  
  input  logic [31:0]                  user_input,
  output logic [31:0]                  user_output
);

localparam PIPE_SLV_ENABLE = 0;
localparam PIPE_MST_ENABLE = 0;

al_vip_axi_if #(.WIDTH(DATA_WIDTH))       s_axi_p (.clk(s_axi.clk), .rstn(s_axi.rstn));
al_vip_axi_if #(.WIDTH(DATA_WIDTH))       m_axi_p (.clk(m_axi.clk), .rstn(m_axi.rstn));
al_vip_axi_if #(.WIDTH(DATA_WIDTH))       lat_axi (.clk(m_axi.clk), .rstn(m_axi.rstn));

logic [64+2+8+3-1:0]                      i_m_ar_data;
logic [64+2+8+3-1:0]                      i_lat_ar_data;
logic [64+2+8+3-1:0]                      i_m_aw_data;
logic [64+2+8+3-1:0]                      i_lat_aw_data;
logic [1:0]                               i_m_b_data;
logic [1:0]                               i_lat_b_data;
logic [1+2+DATA_WIDTH-1:0]                i_m_r_data;
logic [1+2+DATA_WIDTH-1:0]                i_lat_r_data;
logic [DATA_WIDTH+(DATA_WIDTH/8):0]       i_m_w_data;
logic [DATA_WIDTH+(DATA_WIDTH/8):0]       i_lat_w_data;

logic        [10:0]                       ar_delay_len;
logic        [7:0]                        ar_blat_proba;
logic        [15:0]                       ar_blat_seed;
logic                                     ar_blat_seed_rst;
logic        [15:0]                       ar_blat_min;
logic        [15:0]                       ar_blat_width_mask;
logic [31:0] [15:0]                       ar_ilat_seed;
logic [31:0]                              ar_ilat_seed_rst;
logic [31:0] [15:0]                       ar_ilat_min;
logic [31:0] [15:0]                       ar_ilat_width_mask;

logic        [7:0]                        aw_blat_proba;
logic        [15:0]                       aw_blat_seed;
logic                                     aw_blat_seed_rst;
logic        [15:0]                       aw_blat_min;
logic        [15:0]                       aw_blat_width_mask;

logic [31:0] [7:0]                        b_ilat_proba;
logic [31:0] [15:0]                       b_ilat_seed;
logic [31:0]                              b_ilat_seed_rst;
logic [31:0] [15:0]                       b_ilat_min;
logic [31:0] [15:0]                       b_ilat_width_mask;

logic                                     r_fault_restart;
logic        [19:0]                       r_fault_seed;
logic        [19:0]                       r_fault_probThresReq;
logic       [255:0]                       r_fault_regPattern;
logic        [3:0]                        r_fault_cmd;
logic        [4:0]                        r_fault_id;
logic        [31:0]                       r_fault_stats_lfsr;
logic        [31:0]                       r_fault_stats_nberror;
logic        [31:0]                       r_fault_stats_nbrequest;
logic [31:0] [7:0]                        r_ilat_proba;
logic [31:0] [15:0]                       r_ilat_seed;
logic [31:0]                              r_ilat_seed_rst;
logic [31:0] [15:0]                       r_ilat_min;
logic [31:0] [15:0]                       r_ilat_width_mask;

logic        [7:0]                        w_blat_proba;
logic        [15:0]                       w_blat_seed;
logic                                     w_blat_seed_rst;
logic        [15:0]                       w_blat_min;
logic        [15:0]                       w_blat_width_mask;

logic [15:0]                              outstanding_max_read;
logic [15:0]                              outstanding_max_write;
logic [15:0]                              outstanding_cur_read;
logic [15:0]                              outstanding_cur_write;

logic [0:0]                               bandwidth_rst;
logic [4:0]                               bandwidth_id;
logic [31:0]                              bandwidth_read_all;
logic [31:0]                              bandwidth_read_id;
logic [31:0]                              bandwidth_write_all;
logic [31:0]                              bandwidth_write_id;

logic [31:0]                              axi_offset_msb;
logic [31:0]                              axi_offset_lsb;
logic                                     axi_reset_status;
logic [7:0]                               axi_len_max_ar;
logic [7:0]                               axi_len_max_aw;
logic [15:0]                              axi_bytes_max_ar;
logic [15:0]                              axi_bytes_max_aw;
logic [31:0]                              axi_idle_counter;
logic [15:0]                              axi_nb_packet_read;
logic [15:0]                              axi_nb_packet_write;
logic [0:0]                               axi_sts_read_resp_err;
logic [0:0]                               axi_sts_write_resp_err;
logic [31:0]                              axi_addr_read_min_msb;
logic [31:0]                              axi_addr_read_min_lsb;
logic [31:0]                              axi_addr_read_max_msb;
logic [31:0]                              axi_addr_read_max_lsb;
logic [31:0]                              axi_addr_write_min_msb;
logic [31:0]                              axi_addr_write_min_lsb;
logic [31:0]                              axi_addr_write_max_msb;
logic [31:0]                              axi_addr_write_max_lsb;
logic [0:0]                               delay_mean_cnt_rst;
logic [63:0]                              delay_mean_total_delay_total;
logic [55:0]                              delay_mean_nb_request;
logic [15:0]                              delay_mean_max_value_req;
logic [15:0]                              delay_mean_min_value_req;
logic [0:0]                               delay_mean_err_fifo_full;
logic [0:0]                               delay_mean_err_nbreq_overflow;
logic [0:0]                               delay_mean_err_timer_overflow;
logic [0:0]                               delay_mean_err_total_overflow;
logic [15:0]                              delay_distr_value;
logic [DELAYLINE_OUTSTANDING_LOG2-1:0]    delay_distr_nbreq;
logic [0:0]                               delay_distr_enable;
logic [0:0]                               delay_distr_rstptr;
logic [0:0]                               delay_distr_write;
logic [15:0]                              delay_distr_seed;

alg_amba_vip_pipe #(
  .PIPE_ENABLE  (PIPE_SLV_ENABLE),
  .DATA_WIDTH   (DATA_WIDTH)
) PIPE_SLV (
  .s_axi        (s_axi),
  .m_axi        (s_axi_p)
);

alg_amba_vip_pipe #(
  .PIPE_ENABLE  (PIPE_MST_ENABLE),
  .DATA_WIDTH   (DATA_WIDTH)
) PIPE_MST (
  .s_axi        (m_axi_p),
  .m_axi        (m_axi)
);

alg_amba_vip_regs #(
  .APB_ADDR_WIDTH                   (16),
  .ID                               (ID),
  .RESYNC                           (APB_RESYNC)
) U_REGS (
  
  .aclk                             (m_axi_p.clk),
  .aresetn                          (m_axi_p.rstn),
  
  .apb                              (apb),
  
  .irq                              (irq),
  
  .user_input                       (user_input),
  .user_output                      (user_output),
  
  .ar_delay_len                     (ar_delay_len),
  
  .ar_blat_proba                    (ar_blat_proba),
  .ar_blat_seed                     (ar_blat_seed),
  .ar_blat_seed_rst                 (ar_blat_seed_rst),
  .ar_blat_min                      (ar_blat_min),
  .ar_blat_width_mask               (ar_blat_width_mask),
  .ar_ilat_seed                     (ar_ilat_seed),
  .ar_ilat_seed_rst                 (ar_ilat_seed_rst),
  .ar_ilat_min                      (ar_ilat_min),
  .ar_ilat_width_mask               (ar_ilat_width_mask),
  .aw_blat_proba                    (aw_blat_proba),
  .aw_blat_seed                     (aw_blat_seed),
  .aw_blat_seed_rst                 (aw_blat_seed_rst),
  .aw_blat_min                      (aw_blat_min),
  .aw_blat_width_mask               (aw_blat_width_mask),
  .b_ilat_proba                     (b_ilat_proba),
  .b_ilat_seed                      (b_ilat_seed),
  .b_ilat_seed_rst                  (b_ilat_seed_rst),
  .b_ilat_min                       (b_ilat_min),
  .b_ilat_width_mask                (b_ilat_width_mask),
  .r_ilat_proba                     (r_ilat_proba),
  .r_ilat_seed                      (r_ilat_seed),
  .r_ilat_seed_rst                  (r_ilat_seed_rst),
  .r_ilat_min                       (r_ilat_min),
  .r_ilat_width_mask                (r_ilat_width_mask),
  .w_blat_proba                     (w_blat_proba),
  .w_blat_seed                      (w_blat_seed),
  .w_blat_seed_rst                  (w_blat_seed_rst),
  .w_blat_min                       (w_blat_min),
  .w_blat_width_mask                (w_blat_width_mask),
  
  .r_fault_restart                  (r_fault_restart),
  .r_fault_seed                     (r_fault_seed),
  .r_fault_probThresReq             (r_fault_probThresReq),
  .r_fault_regPattern               (r_fault_regPattern),
  .r_fault_cmd                      (r_fault_cmd),
  .r_fault_id                       (r_fault_id),
  .r_fault_stats_lfsr               (r_fault_stats_lfsr),
  .r_fault_stats_nberror            (r_fault_stats_nberror),
  .r_fault_stats_nbrequest          (r_fault_stats_nbrequest),
  
  .outstanding_max_read             (outstanding_max_read),
  .outstanding_max_write            (outstanding_max_write),
  .outstanding_cur_read             (outstanding_cur_read),
  .outstanding_cur_write            (outstanding_cur_write),
  
  .bandwidth_rst                    (bandwidth_rst),
  .bandwidth_id                     (bandwidth_id),
  .bandwidth_read_all               (bandwidth_read_all),
  .bandwidth_read_id                (bandwidth_read_id),
  .bandwidth_write_all              (bandwidth_write_all),
  .bandwidth_write_id               (bandwidth_write_id),
  
  .axi_offset_msb                   (axi_offset_msb),
  .axi_offset_lsb                   (axi_offset_lsb),
  .axi_reset_status                 (axi_reset_status),
  .axi_len_max_ar                   (axi_len_max_ar),
  .axi_len_max_aw                   (axi_len_max_aw),
  .axi_bytes_max_ar                 (axi_bytes_max_ar),
  .axi_bytes_max_aw                 (axi_bytes_max_aw),
  .axi_idle_counter                 (axi_idle_counter),
  .axi_nb_packet_read               (axi_nb_packet_read),
  .axi_nb_packet_write              (axi_nb_packet_write),
  .axi_sts_read_resp_err            (axi_sts_read_resp_err),
  .axi_sts_write_resp_err           (axi_sts_write_resp_err),
  .axi_addr_read_min_msb            (axi_addr_read_min_msb),
  .axi_addr_read_min_lsb            (axi_addr_read_min_lsb),
  .axi_addr_read_max_msb            (axi_addr_read_max_msb),
  .axi_addr_read_max_lsb            (axi_addr_read_max_lsb),
  .axi_addr_write_min_msb           (axi_addr_write_min_msb),
  .axi_addr_write_min_lsb           (axi_addr_write_min_lsb),
  .axi_addr_write_max_msb           (axi_addr_write_max_msb),
  .axi_addr_write_max_lsb           (axi_addr_write_max_lsb),
  
  .delay_mean_cnt_rst               (delay_mean_cnt_rst),
  .delay_mean_total_delay_total     (delay_mean_total_delay_total[31:0]),
  .delay_mean_total_delay_total_msb (delay_mean_total_delay_total[63:32]),
  .delay_mean_nb_request            (delay_mean_nb_request[23:0]),
  .delay_mean_nb_request_msb        (delay_mean_nb_request[55:24]),
  .delay_mean_max_value_req         (delay_mean_max_value_req),
  .delay_mean_min_value_req         (delay_mean_min_value_req),
  .delay_mean_err_fifo_full         (delay_mean_err_fifo_full),
  .delay_mean_err_nbreq_overflow    (delay_mean_err_nbreq_overflow),
  .delay_mean_err_timer_overflow    (delay_mean_err_timer_overflow),
  .delay_mean_err_total_overflow    (delay_mean_err_total_overflow),
  
  .delay_distr_value                (delay_distr_value),
  .delay_distr_nbreq                (delay_distr_nbreq),
  .delay_distr_enable               (delay_distr_enable),
  .delay_distr_rstptr               (delay_distr_rstptr),
  .delay_distr_write                (delay_distr_write),
  .delay_distr_seed                 (delay_distr_seed)
);

alg_amba_vip_filter #(
  .DATA_WIDTH           (DATA_WIDTH),
  .OUTSTANDING_LOG2_MAX (DELAYLINE_OUTSTANDING_LOG2)
) U_FILTER (
  
  .outstanding_max_read             (outstanding_max_read),
  .outstanding_max_write            (outstanding_max_write),
  .outstanding_cur_read             (outstanding_cur_read),
  .outstanding_cur_write            (outstanding_cur_write),
  
  .bandwidth_rst                    (bandwidth_rst),
  .bandwidth_id                     (bandwidth_id),
  .bandwidth_read_total             (bandwidth_read_all),
  .bandwidth_read_id                (bandwidth_read_id),
  .bandwidth_write_total            (bandwidth_write_all),
  .bandwidth_write_id               (bandwidth_write_id),
  
  .idle_cnt                         (axi_idle_counter),
  .ar_len_max                       (axi_len_max_ar),
  .aw_len_max                       (axi_len_max_aw),
  .ar_bytes_max                     (axi_bytes_max_ar),
  .aw_bytes_max                     (axi_bytes_max_aw),
  
  .delay_mean_cnt_rst               (delay_mean_cnt_rst),
  .delay_mean_total_delay_total     (delay_mean_total_delay_total),
  .delay_mean_nb_request            (delay_mean_nb_request),
  .delay_mean_max_value_req         (delay_mean_max_value_req),
  .delay_mean_min_value_req         (delay_mean_min_value_req),
  .delay_mean_err_fifo_full         (delay_mean_err_fifo_full),
  .delay_mean_err_nbreq_overflow    (delay_mean_err_nbreq_overflow),
  .delay_mean_err_timer_overflow    (delay_mean_err_timer_overflow),
  .delay_mean_err_total_overflow    (delay_mean_err_total_overflow),
  
  .axi_offset_msb                   (axi_offset_msb),
  .axi_offset_lsb                   (axi_offset_lsb),
  .axi_reset_status                 (axi_reset_status),
  .ar_nb_packet                     (axi_nb_packet_read),
  .aw_nb_packet                     (axi_nb_packet_write),
  .read_resp_err                    (axi_sts_read_resp_err),
  .write_resp_err                   (axi_sts_write_resp_err),
  .read_addr_min_msb                (axi_addr_read_min_msb),
  .read_addr_min_lsb                (axi_addr_read_min_lsb),
  .read_addr_max_msb                (axi_addr_read_max_msb),
  .read_addr_max_lsb                (axi_addr_read_max_lsb),
  .write_addr_min_msb               (axi_addr_write_min_msb),
  .write_addr_min_lsb               (axi_addr_write_min_lsb),
  .write_addr_max_msb               (axi_addr_write_max_msb),
  .write_addr_max_lsb               (axi_addr_write_max_lsb),

  
  .s_axi                            (s_axi_p),
  .m_axi                            (lat_axi)
);


assign i_lat_ar_data = {lat_axi.araddr, lat_axi.arburst, lat_axi.arlen, lat_axi.arsize};
assign m_axi_p.araddr    = i_m_ar_data[76:13];
assign m_axi_p.arburst   = i_m_ar_data[12:11];
assign m_axi_p.arlen     = i_m_ar_data[10:3];
assign m_axi_p.arsize    = i_m_ar_data[2:0];
alg_amba_vip_channel #(
  .DATA_WIDTH                 (64+2+8+3),
  .ID_WIDTH                   (5),
  .ID_START                   (ID_START),
  .ID_END                     (ID_END),
  .FAULT_EN                   (0),
  .FAULT_DATA_WIDTH           (1),
  .DELAYLINE_EN               (1),
  .DELAYLINE_OUTSTANDING_LOG2 (DELAYLINE_OUTSTANDING_LOG2),
  .BLOCKING_EN                (1),
  .BLOCKING_PROB_EN           (1),
  .INTERLEAVING_EN            (1),
  .INTERLEAVING_PROB_EN       (0),
  .INTERLEAVING_FIFO_LOG2     (5)
) CHANNEL_AR (
  
  .clk                        (m_axi_p.clk),
  .resetn                     (m_axi_p.rstn),
  
  .fault_restart              (1'b0),
  .fault_seed                 ('0),
  .fault_probThresReq         ('0),
  .fault_regPattern           ('0),
  .fault_cmd                  ('0),
  .fault_id                   ('0),
  .fault_stats_lfsr           (),
  .fault_stats_nberror        (),
  .fault_stats_nbrequest      (),
  
  .delay_distr_value          (delay_distr_value),
  .delay_distr_nbreq          (delay_distr_nbreq),
  .delay_distr_enable         (delay_distr_enable[0]),
  .delay_distr_rstptr         (delay_distr_rstptr[0]),
  .delay_distr_write          (delay_distr_write[0]),
  .delay_distr_seed           (delay_distr_seed),
  
  .blat_proba                 (ar_blat_proba),
  .blat_seed                  (ar_blat_seed),
  .blat_seed_rst              (ar_blat_seed_rst),
  .blat_min                   (ar_blat_min),
  .blat_width_mask            (ar_blat_width_mask),
  
  .ilat_proba                 ('0),
  .ilat_seed                  (ar_ilat_seed),
  .ilat_seed_rst              (ar_ilat_seed_rst),
  .ilat_min                   (ar_ilat_min),
  .ilat_width_mask            (ar_ilat_width_mask),
  
  .m_valid                    (m_axi_p.arvalid),
  .m_id                       (m_axi_p.arid),
  .m_data                     (i_m_ar_data),
  .m_ready                    (m_axi_p.arready),
  
  .s_valid                    (lat_axi.arvalid),
  .s_id                       (lat_axi.arid),
  .s_data                     (i_lat_ar_data),
  .s_ready                    (lat_axi.arready)
);


assign i_lat_aw_data = {lat_axi.awaddr, lat_axi.awburst, lat_axi.awlen, lat_axi.awsize};
assign m_axi_p.awaddr      = i_m_aw_data[76:13];
assign m_axi_p.awburst     = i_m_aw_data[12:11];
assign m_axi_p.awlen       = i_m_aw_data[10:3];
assign m_axi_p.awsize      = i_m_aw_data[2:0];
alg_amba_vip_channel #(
  .DATA_WIDTH                 (64+2+8+3),
  .ID_WIDTH                   (5),
  .ID_START                   (ID_START),
  .ID_END                     (ID_END),
  .FAULT_EN                   (0),
  .FAULT_DATA_WIDTH           (1),
  .DELAYLINE_EN               (0),
  .BLOCKING_EN                (1),
  .BLOCKING_PROB_EN           (1),
  .INTERLEAVING_EN            (0),
  .INTERLEAVING_PROB_EN       (0),
  .INTERLEAVING_FIFO_LOG2     (2)
) CHANNEL_AW (
  
  .clk                        (m_axi_p.clk),
  .resetn                     (m_axi_p.rstn),
  
  .fault_restart              (1'b0),
  .fault_seed                 ('0),
  .fault_probThresReq         ('0),
  .fault_regPattern           ('0),
  .fault_cmd                  ('0),
  .fault_id                   ('0),
  .fault_stats_lfsr           (),
  .fault_stats_nberror        (),
  .fault_stats_nbrequest      (),
  
  .delay_distr_value          ('0),
  .delay_distr_nbreq          ('0),
  .delay_distr_enable         (1'b0),
  .delay_distr_rstptr         (1'b0),
  .delay_distr_write          (1'b0),
  .delay_distr_seed           ('0),
  
  .blat_proba                 (aw_blat_proba),
  .blat_seed                  (aw_blat_seed),
  .blat_seed_rst              (aw_blat_seed_rst),
  .blat_min                   (aw_blat_min),
  .blat_width_mask            (aw_blat_width_mask),
  
  .ilat_proba                 ('0),
  .ilat_seed                  ('0),
  .ilat_seed_rst              ('0),
  .ilat_min                   ('0),
  .ilat_width_mask            ('0),
  
  .m_valid                    (m_axi_p.awvalid),
  .m_id                       (m_axi_p.awid),
  .m_data                     (i_m_aw_data),
  .m_ready                    (m_axi_p.awready),
  
  .s_valid                    (lat_axi.awvalid),
  .s_id                       (lat_axi.awid),
  .s_data                     (i_lat_aw_data),
  .s_ready                    (lat_axi.awready)
);


assign i_m_b_data = {m_axi_p.bresp};
assign lat_axi.bresp  = i_lat_b_data[1:0];
alg_amba_vip_channel #(
  .DATA_WIDTH                 (2),
  .ID_WIDTH                   (5),
  .ID_START                   (ID_START),
  .ID_END                     (ID_END),
  .FAULT_EN                   (0),
  .FAULT_DATA_WIDTH           (1),
  .DELAYLINE_EN               (0),
  .BLOCKING_EN                (0),
  .BLOCKING_PROB_EN           (0),
  .INTERLEAVING_EN            (1),
  .INTERLEAVING_PROB_EN       (1),
  .INTERLEAVING_FIFO_LOG2     (6)
) CHANNEL_B (
  
  .clk                        (m_axi_p.clk),
  .resetn                     (m_axi_p.rstn),
  
  .fault_restart              (1'b0),
  .fault_seed                 ('0),
  .fault_probThresReq         ('0),
  .fault_regPattern           ('0),
  .fault_cmd                  ('0),
  .fault_id                   ('0),
  .fault_stats_lfsr           (),
  .fault_stats_nberror        (),
  .fault_stats_nbrequest      (),
  
  .delay_distr_value          ('0),
  .delay_distr_nbreq          ('0),
  .delay_distr_enable         (1'b0),
  .delay_distr_rstptr         (1'b0),
  .delay_distr_write          (1'b0),
  .delay_distr_seed           ('0),
  
  .blat_proba                 ('0),
  .blat_seed                  ('0),
  .blat_seed_rst              ('0),
  .blat_min                   ('0),
  .blat_width_mask            ('0),
  
  .ilat_proba                 (b_ilat_proba),
  .ilat_seed                  (b_ilat_seed),
  .ilat_seed_rst              (b_ilat_seed_rst),
  .ilat_min                   (b_ilat_min),
  .ilat_width_mask            (b_ilat_width_mask),
  
  .m_valid                    (lat_axi.bvalid),
  .m_id                       (lat_axi.bid),
  .m_data                     (i_lat_b_data),
  .m_ready                    (lat_axi.bready),
  
  .s_valid                    (m_axi_p.bvalid),
  .s_id                       (m_axi_p.bid),
  .s_data                     (i_m_b_data),
  .s_ready                    (m_axi_p.bready)
);


assign i_m_r_data = {m_axi_p.rresp, m_axi_p.rlast, m_axi_p.rdata};
assign lat_axi.rresp  = i_lat_r_data[DATA_WIDTH+2:DATA_WIDTH+1];
assign lat_axi.rlast  = i_lat_r_data[DATA_WIDTH:DATA_WIDTH];
assign lat_axi.rdata  = i_lat_r_data[DATA_WIDTH-1:0];
alg_amba_vip_channel #(
  .DATA_WIDTH                 (DATA_WIDTH+2+1),
  .ID_WIDTH                   (5),
  .ID_START                   (ID_START),
  .ID_END                     (ID_END),
  .FAULT_EN                   (1),
  .FAULT_DATA_WIDTH           (DATA_WIDTH),
  .DELAYLINE_EN               (0),
  .BLOCKING_EN                (0),
  .BLOCKING_PROB_EN           (0),
  .INTERLEAVING_EN            (1),
  .INTERLEAVING_PROB_EN       (1),
  .INTERLEAVING_FIFO_LOG2     (5)
) CHANNEL_R (
  
  .clk                        (m_axi_p.clk),
  .resetn                     (m_axi_p.rstn),
  
  .fault_restart              (r_fault_restart),
  .fault_seed                 (r_fault_seed),
  .fault_probThresReq         (r_fault_probThresReq),
  .fault_regPattern           (r_fault_regPattern[DATA_WIDTH-1:0]),
  .fault_cmd                  (r_fault_cmd),
  .fault_id                   (r_fault_id),
  .fault_stats_lfsr           (r_fault_stats_lfsr),
  .fault_stats_nberror        (r_fault_stats_nberror),
  .fault_stats_nbrequest      (r_fault_stats_nbrequest),
  
  .delay_distr_value          ('0),
  .delay_distr_nbreq          ('0),
  .delay_distr_enable         (1'b0),
  .delay_distr_rstptr         (1'b0),
  .delay_distr_write          (1'b0),
  .delay_distr_seed           ('0),
  
  .blat_proba                 ('0),
  .blat_seed                  ('0),
  .blat_seed_rst              ('0),
  .blat_min                   ('0),
  .blat_width_mask            ('0),
  
  .ilat_proba                 (r_ilat_proba),
  .ilat_seed                  (r_ilat_seed),
  .ilat_seed_rst              (r_ilat_seed_rst),
  .ilat_min                   (r_ilat_min),
  .ilat_width_mask            (r_ilat_width_mask),
  
  .m_valid                    (lat_axi.rvalid),
  .m_id                       (lat_axi.rid),
  .m_data                     (i_lat_r_data),
  .m_ready                    (lat_axi.rready),
  
  .s_valid                    (m_axi_p.rvalid),
  .s_id                       (m_axi_p.rid),
  .s_data                     (i_m_r_data),
  .s_ready                    (m_axi_p.rready)
);


assign i_lat_w_data = {lat_axi.wlast, lat_axi.wstrb, lat_axi.wdata};
assign m_axi_p.wlast    = i_m_w_data[DATA_WIDTH+(DATA_WIDTH/8):DATA_WIDTH+(DATA_WIDTH/8)];
assign m_axi_p.wstrb    = i_m_w_data[DATA_WIDTH+(DATA_WIDTH/8)-1:DATA_WIDTH];
assign m_axi_p.wdata    = i_m_w_data[DATA_WIDTH-1:0];
alg_amba_vip_channel #(
  .DATA_WIDTH                 (DATA_WIDTH+(DATA_WIDTH/8)+1),
  .ID_WIDTH                   (1),
  .ID_START                   (ID_START),
  .ID_END                     (ID_END),
  .FAULT_EN                   (0),
  .FAULT_DATA_WIDTH           (1),
  .DELAYLINE_EN               (0),
  .BLOCKING_EN                (1),
  .BLOCKING_PROB_EN           (1),
  .INTERLEAVING_EN            (0),
  .INTERLEAVING_PROB_EN       (0),
  .INTERLEAVING_FIFO_LOG2     (2)
) CHANNEL_W (
  
  .clk                        (m_axi_p.clk),
  .resetn                     (m_axi_p.rstn),
  
  .fault_restart              (1'b0),
  .fault_seed                 ('0),
  .fault_probThresReq         ('0),
  .fault_regPattern           ('0),
  .fault_cmd                  ('0),
  .fault_id                   ('0),
  .fault_stats_lfsr           (),
  .fault_stats_nberror        (),
  .fault_stats_nbrequest      (),
  
  .delay_distr_value          ('0),
  .delay_distr_nbreq          ('0),
  .delay_distr_enable         (1'b0),
  .delay_distr_rstptr         (1'b0),
  .delay_distr_write          (1'b0),
  .delay_distr_seed           ('0),
  
  .blat_proba                 (w_blat_proba),
  .blat_seed                  (w_blat_seed),
  .blat_seed_rst              (w_blat_seed_rst),
  .blat_min                   (w_blat_min),
  .blat_width_mask            (w_blat_width_mask),
  
  .ilat_proba                 ('0),
  .ilat_seed                  ('0),
  .ilat_seed_rst              ('0),
  .ilat_min                   ('0),
  .ilat_width_mask            ('0),
  
  .m_valid                    (m_axi_p.wvalid),
  .m_id                       (),
  .m_data                     (i_m_w_data),
  .m_ready                    (m_axi_p.wready),
  
  .s_valid                    (lat_axi.wvalid),
  .s_id                       (1'b0),
  .s_data                     (i_lat_w_data),
  .s_ready                    (lat_axi.wready)
);


endmodule
