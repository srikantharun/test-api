
module alg_amba_vip_regs #(
  parameter APB_ADDR_WIDTH = 16,
  parameter ID = 1,
  parameter RESYNC = 1
)(
  
  al_vip_apb_if.slavemod               apb,
  
  output logic                         irq,
  
  input  logic [31:0]                  user_input,
  output logic [31:0]                  user_output,
  
  input  logic                         aclk,
  input  logic                         aresetn,
  
  output logic                         r_fault_restart,
  output logic[19:0]                   r_fault_seed,
  output logic[19:0]                   r_fault_probThresReq,
  output logic[255:0]                  r_fault_regPattern,
  output logic[3:0]                    r_fault_cmd,
  output logic[4:0]                    r_fault_id,
  input  logic[31:0]                   r_fault_stats_lfsr,
  input  logic[31:0]                   r_fault_stats_nberror,
  input  logic[31:0]                   r_fault_stats_nbrequest,
  
  output logic        [10:0]           ar_delay_len,
  
  output logic        [7:0]            ar_blat_proba,
  output logic        [15:0]           ar_blat_seed,
  output logic                         ar_blat_seed_rst,
  output logic        [15:0]           ar_blat_min,
  output logic        [15:0]           ar_blat_width_mask,
  output logic [31:0] [15:0]           ar_ilat_seed,
  output logic [31:0]                  ar_ilat_seed_rst,
  output logic [31:0] [15:0]           ar_ilat_min,
  output logic [31:0] [15:0]           ar_ilat_width_mask,
  output logic        [7:0]            aw_blat_proba,
  output logic        [15:0]           aw_blat_seed,
  output logic                         aw_blat_seed_rst,
  output logic        [15:0]           aw_blat_min,
  output logic        [15:0]           aw_blat_width_mask,
  output logic [31:0] [7:0]            b_ilat_proba,
  output logic [31:0] [15:0]           b_ilat_seed,
  output logic [31:0]                  b_ilat_seed_rst,
  output logic [31:0] [15:0]           b_ilat_min,
  output logic [31:0] [15:0]           b_ilat_width_mask,
  output logic [31:0] [7:0]            r_ilat_proba,
  output logic [31:0] [15:0]           r_ilat_seed,
  output logic [31:0]                  r_ilat_seed_rst,
  output logic [31:0] [15:0]           r_ilat_min,
  output logic [31:0] [15:0]           r_ilat_width_mask,
  output logic        [7:0]            w_blat_proba,
  output logic        [15:0]           w_blat_seed,
  output logic                         w_blat_seed_rst,
  output logic        [15:0]           w_blat_min,
  output logic        [15:0]           w_blat_width_mask,
  
  output logic [15:0]                  outstanding_max_read,
  output logic [15:0]                  outstanding_max_write,
  input  logic [15:0]                  outstanding_cur_read,
  input  logic [15:0]                  outstanding_cur_write,
  
  output logic [0:0]                   bandwidth_rst,
  output logic [4:0]                   bandwidth_id,
  input  logic [31:0]                  bandwidth_read_all,
  input  logic [31:0]                  bandwidth_read_id,
  input  logic [31:0]                  bandwidth_write_all,
  input  logic [31:0]                  bandwidth_write_id,
  
  output logic [31:0]                  axi_offset_msb,
  output logic [31:0]                  axi_offset_lsb,
  output logic                         axi_reset_status,
  input  logic [7:0]                   axi_len_max_ar,
  input  logic [7:0]                   axi_len_max_aw,
  input  logic [15:0]                  axi_bytes_max_ar,
  input  logic [15:0]                  axi_bytes_max_aw,
  input  logic [31:0]                  axi_idle_counter,
  input  logic [15:0]                  axi_nb_packet_read,
  input  logic [15:0]                  axi_nb_packet_write,
  input  logic [0:0]                   axi_sts_read_resp_err,
  input  logic [0:0]                   axi_sts_write_resp_err,
  input  logic [31:0]                  axi_addr_read_min_msb,
  input  logic [31:0]                  axi_addr_read_min_lsb,
  input  logic [31:0]                  axi_addr_read_max_msb,
  input  logic [31:0]                  axi_addr_read_max_lsb,
  input  logic [31:0]                  axi_addr_write_min_msb,
  input  logic [31:0]                  axi_addr_write_min_lsb,
  input  logic [31:0]                  axi_addr_write_max_msb,
  input  logic [31:0]                  axi_addr_write_max_lsb,
  
  output logic [0:0]                   delay_mean_cnt_rst,
  input  logic [31:0]                  delay_mean_total_delay_total,
  input  logic [31:0]                  delay_mean_total_delay_total_msb,
  input  logic [23:0]                  delay_mean_nb_request,
  input  logic [31:0]                  delay_mean_nb_request_msb,
  input  logic [15:0]                  delay_mean_max_value_req,
  input  logic [15:0]                  delay_mean_min_value_req,
  input  logic [0:0]                   delay_mean_err_fifo_full,
  input  logic [0:0]                   delay_mean_err_nbreq_overflow,
  input  logic [0:0]                   delay_mean_err_timer_overflow,
  input  logic [0:0]                   delay_mean_err_total_overflow,
  
  output logic [15:0]                  delay_distr_value,
  output logic [7:0]                   delay_distr_nbreq,
  output logic [0:0]                   delay_distr_enable,
  output logic [0:0]                   delay_distr_rstptr,
  output logic [0:0]                   delay_distr_write,
  output logic [15:0]                  delay_distr_seed

);

logic                     psel_resync;
logic                     penable_resync;
logic                     pwrite_resync;
logic [15:0]              paddr_resync;
logic [31:0]              pwdata_resync;
logic [31:0]              prdata_resync;
logic                     pready_resync;

logic [15:0]              global_seed_value;
logic                     global_seed_reset;

logic [7:0]               vip_id;

logic                     delay_distr_rstptr_wr;
logic                     delay_distr_rstptr_rd;

assign delay_distr_rstptr[0] = delay_distr_rstptr_wr || delay_distr_rstptr_rd;

assign irq                = 1'b0;
assign vip_id             = ID;

al_vip_apb_if  #(.ADDR(16))          apb_resync   (.clk(aclk), .rstn(aresetn));

generate
if (RESYNC) begin: g_apb_resync
  alg_amba_vip_base_apb_stage APB_STAGE (
    .s_apb        (apb),
    .m_apb        (apb_resync)
  );
end else begin: g_noapb_resync
  assign apb_resync.sel    = apb.sel;
  assign apb_resync.enable = apb.enable;
  assign apb_resync.write  = apb.write;
  assign apb_resync.addr   = apb.addr;
  assign apb_resync.wdata  = apb.wdata;
  assign apb.rdata         = apb_resync.rdata;
  assign apb.ready         = apb_resync.ready;
  assign apb.slverr        = apb_resync.slverr;
end
endgenerate

assign apb_resync.slverr = 1'b0;

alg_amba_vip_regs_generated REGS_GENERATED (

  
  .sts_vip_id                             (vip_id),
  .sts_user_input                         (user_input),

  
  .cfg_user_output                        (user_output),
  .cfg_global_seed_value                  (global_seed_value),
  .cfg_global_seed_reset                  (global_seed_reset),

  
  .cfg_ar_blat_range_min                  (ar_blat_min),
  .cfg_ar_blat_range_width_mask           (ar_blat_width_mask),
  .cfg_ar_blat_proba                      (ar_blat_proba),
  .cfg_ar_ilat_range_0_min                (ar_ilat_min[0]),
  .cfg_ar_ilat_range_0_width_mask         (ar_ilat_width_mask[0]),
  .cfg_ar_ilat_range_1_min                (ar_ilat_min[1]),
  .cfg_ar_ilat_range_1_width_mask         (ar_ilat_width_mask[1]),
  .cfg_ar_ilat_range_2_min                (ar_ilat_min[2]),
  .cfg_ar_ilat_range_2_width_mask         (ar_ilat_width_mask[2]),
  .cfg_ar_ilat_range_3_min                (ar_ilat_min[3]),
  .cfg_ar_ilat_range_3_width_mask         (ar_ilat_width_mask[3]),
  .cfg_ar_ilat_range_4_min                (ar_ilat_min[4]),
  .cfg_ar_ilat_range_4_width_mask         (ar_ilat_width_mask[4]),
  .cfg_ar_ilat_range_5_min                (ar_ilat_min[5]),
  .cfg_ar_ilat_range_5_width_mask         (ar_ilat_width_mask[5]),
  .cfg_ar_ilat_range_6_min                (ar_ilat_min[6]),
  .cfg_ar_ilat_range_6_width_mask         (ar_ilat_width_mask[6]),
  .cfg_ar_ilat_range_7_min                (ar_ilat_min[7]),
  .cfg_ar_ilat_range_7_width_mask         (ar_ilat_width_mask[7]),
  .cfg_ar_ilat_range_8_min                (ar_ilat_min[8]),
  .cfg_ar_ilat_range_8_width_mask         (ar_ilat_width_mask[8]),
  .cfg_ar_ilat_range_9_min                (ar_ilat_min[9]),
  .cfg_ar_ilat_range_9_width_mask         (ar_ilat_width_mask[9]),
  .cfg_ar_ilat_range_10_min               (ar_ilat_min[10]),
  .cfg_ar_ilat_range_10_width_mask        (ar_ilat_width_mask[10]),
  .cfg_ar_ilat_range_11_min               (ar_ilat_min[11]),
  .cfg_ar_ilat_range_11_width_mask        (ar_ilat_width_mask[11]),
  .cfg_ar_ilat_range_12_min               (ar_ilat_min[12]),
  .cfg_ar_ilat_range_12_width_mask        (ar_ilat_width_mask[12]),
  .cfg_ar_ilat_range_13_min               (ar_ilat_min[13]),
  .cfg_ar_ilat_range_13_width_mask        (ar_ilat_width_mask[13]),
  .cfg_ar_ilat_range_14_min               (ar_ilat_min[14]),
  .cfg_ar_ilat_range_14_width_mask        (ar_ilat_width_mask[14]),
  .cfg_ar_ilat_range_15_min               (ar_ilat_min[15]),
  .cfg_ar_ilat_range_15_width_mask        (ar_ilat_width_mask[15]),
  .cfg_ar_ilat_range_16_min               (ar_ilat_min[16]),
  .cfg_ar_ilat_range_16_width_mask        (ar_ilat_width_mask[16]),
  .cfg_ar_ilat_range_17_min               (ar_ilat_min[17]),
  .cfg_ar_ilat_range_17_width_mask        (ar_ilat_width_mask[17]),
  .cfg_ar_ilat_range_18_min               (ar_ilat_min[18]),
  .cfg_ar_ilat_range_18_width_mask        (ar_ilat_width_mask[18]),
  .cfg_ar_ilat_range_19_min               (ar_ilat_min[19]),
  .cfg_ar_ilat_range_19_width_mask        (ar_ilat_width_mask[19]),
  .cfg_ar_ilat_range_20_min               (ar_ilat_min[20]),
  .cfg_ar_ilat_range_20_width_mask        (ar_ilat_width_mask[20]),
  .cfg_ar_ilat_range_21_min               (ar_ilat_min[21]),
  .cfg_ar_ilat_range_21_width_mask        (ar_ilat_width_mask[21]),
  .cfg_ar_ilat_range_22_min               (ar_ilat_min[22]),
  .cfg_ar_ilat_range_22_width_mask        (ar_ilat_width_mask[22]),
  .cfg_ar_ilat_range_23_min               (ar_ilat_min[23]),
  .cfg_ar_ilat_range_23_width_mask        (ar_ilat_width_mask[23]),
  .cfg_ar_ilat_range_24_min               (ar_ilat_min[24]),
  .cfg_ar_ilat_range_24_width_mask        (ar_ilat_width_mask[24]),
  .cfg_ar_ilat_range_25_min               (ar_ilat_min[25]),
  .cfg_ar_ilat_range_25_width_mask        (ar_ilat_width_mask[25]),
  .cfg_ar_ilat_range_26_min               (ar_ilat_min[26]),
  .cfg_ar_ilat_range_26_width_mask        (ar_ilat_width_mask[26]),
  .cfg_ar_ilat_range_27_min               (ar_ilat_min[27]),
  .cfg_ar_ilat_range_27_width_mask        (ar_ilat_width_mask[27]),
  .cfg_ar_ilat_range_28_min               (ar_ilat_min[28]),
  .cfg_ar_ilat_range_28_width_mask        (ar_ilat_width_mask[28]),
  .cfg_ar_ilat_range_29_min               (ar_ilat_min[29]),
  .cfg_ar_ilat_range_29_width_mask        (ar_ilat_width_mask[29]),
  .cfg_ar_ilat_range_30_min               (ar_ilat_min[30]),
  .cfg_ar_ilat_range_30_width_mask        (ar_ilat_width_mask[30]),
  .cfg_ar_ilat_range_31_min               (ar_ilat_min[31]),
  .cfg_ar_ilat_range_31_width_mask        (ar_ilat_width_mask[31]),

  
  .cfg_aw_blat_range_min                  (aw_blat_min),
  .cfg_aw_blat_range_width_mask           (aw_blat_width_mask),
  .cfg_aw_blat_proba                      (aw_blat_proba),

  
  .cfg_b_ilat_range_0_min                 (b_ilat_min[0]),
  .cfg_b_ilat_range_0_width_mask          (b_ilat_width_mask[0]),
  .cfg_b_ilat_proba_0                     (b_ilat_proba[0]),
  .cfg_b_ilat_range_1_min                 (b_ilat_min[1]),
  .cfg_b_ilat_range_1_width_mask          (b_ilat_width_mask[1]),
  .cfg_b_ilat_proba_1                     (b_ilat_proba[1]),
  .cfg_b_ilat_range_2_min                 (b_ilat_min[2]),
  .cfg_b_ilat_range_2_width_mask          (b_ilat_width_mask[2]),
  .cfg_b_ilat_proba_2                     (b_ilat_proba[2]),
  .cfg_b_ilat_range_3_min                 (b_ilat_min[3]),
  .cfg_b_ilat_range_3_width_mask          (b_ilat_width_mask[3]),
  .cfg_b_ilat_proba_3                     (b_ilat_proba[3]),
  .cfg_b_ilat_range_4_min                 (b_ilat_min[4]),
  .cfg_b_ilat_range_4_width_mask          (b_ilat_width_mask[4]),
  .cfg_b_ilat_proba_4                     (b_ilat_proba[4]),
  .cfg_b_ilat_range_5_min                 (b_ilat_min[5]),
  .cfg_b_ilat_range_5_width_mask          (b_ilat_width_mask[5]),
  .cfg_b_ilat_proba_5                     (b_ilat_proba[5]),
  .cfg_b_ilat_range_6_min                 (b_ilat_min[6]),
  .cfg_b_ilat_range_6_width_mask          (b_ilat_width_mask[6]),
  .cfg_b_ilat_proba_6                     (b_ilat_proba[6]),
  .cfg_b_ilat_range_7_min                 (b_ilat_min[7]),
  .cfg_b_ilat_range_7_width_mask          (b_ilat_width_mask[7]),
  .cfg_b_ilat_proba_7                     (b_ilat_proba[7]),
  .cfg_b_ilat_range_8_min                 (b_ilat_min[8]),
  .cfg_b_ilat_range_8_width_mask          (b_ilat_width_mask[8]),
  .cfg_b_ilat_proba_8                     (b_ilat_proba[8]),
  .cfg_b_ilat_range_9_min                 (b_ilat_min[9]),
  .cfg_b_ilat_range_9_width_mask          (b_ilat_width_mask[9]),
  .cfg_b_ilat_proba_9                     (b_ilat_proba[9]),
  .cfg_b_ilat_range_10_min                (b_ilat_min[10]),
  .cfg_b_ilat_range_10_width_mask         (b_ilat_width_mask[10]),
  .cfg_b_ilat_proba_10                    (b_ilat_proba[10]),
  .cfg_b_ilat_range_11_min                (b_ilat_min[11]),
  .cfg_b_ilat_range_11_width_mask         (b_ilat_width_mask[11]),
  .cfg_b_ilat_proba_11                    (b_ilat_proba[11]),
  .cfg_b_ilat_range_12_min                (b_ilat_min[12]),
  .cfg_b_ilat_range_12_width_mask         (b_ilat_width_mask[12]),
  .cfg_b_ilat_proba_12                    (b_ilat_proba[12]),
  .cfg_b_ilat_range_13_min                (b_ilat_min[13]),
  .cfg_b_ilat_range_13_width_mask         (b_ilat_width_mask[13]),
  .cfg_b_ilat_proba_13                    (b_ilat_proba[13]),
  .cfg_b_ilat_range_14_min                (b_ilat_min[14]),
  .cfg_b_ilat_range_14_width_mask         (b_ilat_width_mask[14]),
  .cfg_b_ilat_proba_14                    (b_ilat_proba[14]),
  .cfg_b_ilat_range_15_min                (b_ilat_min[15]),
  .cfg_b_ilat_range_15_width_mask         (b_ilat_width_mask[15]),
  .cfg_b_ilat_proba_15                    (b_ilat_proba[15]),
  .cfg_b_ilat_range_16_min                (b_ilat_min[16]),
  .cfg_b_ilat_range_16_width_mask         (b_ilat_width_mask[16]),
  .cfg_b_ilat_proba_16                    (b_ilat_proba[16]),
  .cfg_b_ilat_range_17_min                (b_ilat_min[17]),
  .cfg_b_ilat_range_17_width_mask         (b_ilat_width_mask[17]),
  .cfg_b_ilat_proba_17                    (b_ilat_proba[17]),
  .cfg_b_ilat_range_18_min                (b_ilat_min[18]),
  .cfg_b_ilat_range_18_width_mask         (b_ilat_width_mask[18]),
  .cfg_b_ilat_proba_18                    (b_ilat_proba[18]),
  .cfg_b_ilat_range_19_min                (b_ilat_min[19]),
  .cfg_b_ilat_range_19_width_mask         (b_ilat_width_mask[19]),
  .cfg_b_ilat_proba_19                    (b_ilat_proba[19]),
  .cfg_b_ilat_range_20_min                (b_ilat_min[20]),
  .cfg_b_ilat_range_20_width_mask         (b_ilat_width_mask[20]),
  .cfg_b_ilat_proba_20                    (b_ilat_proba[20]),
  .cfg_b_ilat_range_21_min                (b_ilat_min[21]),
  .cfg_b_ilat_range_21_width_mask         (b_ilat_width_mask[21]),
  .cfg_b_ilat_proba_21                    (b_ilat_proba[21]),
  .cfg_b_ilat_range_22_min                (b_ilat_min[22]),
  .cfg_b_ilat_range_22_width_mask         (b_ilat_width_mask[22]),
  .cfg_b_ilat_proba_22                    (b_ilat_proba[22]),
  .cfg_b_ilat_range_23_min                (b_ilat_min[23]),
  .cfg_b_ilat_range_23_width_mask         (b_ilat_width_mask[23]),
  .cfg_b_ilat_proba_23                    (b_ilat_proba[23]),
  .cfg_b_ilat_range_24_min                (b_ilat_min[24]),
  .cfg_b_ilat_range_24_width_mask         (b_ilat_width_mask[24]),
  .cfg_b_ilat_proba_24                    (b_ilat_proba[24]),
  .cfg_b_ilat_range_25_min                (b_ilat_min[25]),
  .cfg_b_ilat_range_25_width_mask         (b_ilat_width_mask[25]),
  .cfg_b_ilat_proba_25                    (b_ilat_proba[25]),
  .cfg_b_ilat_range_26_min                (b_ilat_min[26]),
  .cfg_b_ilat_range_26_width_mask         (b_ilat_width_mask[26]),
  .cfg_b_ilat_proba_26                    (b_ilat_proba[26]),
  .cfg_b_ilat_range_27_min                (b_ilat_min[27]),
  .cfg_b_ilat_range_27_width_mask         (b_ilat_width_mask[27]),
  .cfg_b_ilat_proba_27                    (b_ilat_proba[27]),
  .cfg_b_ilat_range_28_min                (b_ilat_min[28]),
  .cfg_b_ilat_range_28_width_mask         (b_ilat_width_mask[28]),
  .cfg_b_ilat_proba_28                    (b_ilat_proba[28]),
  .cfg_b_ilat_range_29_min                (b_ilat_min[29]),
  .cfg_b_ilat_range_29_width_mask         (b_ilat_width_mask[29]),
  .cfg_b_ilat_proba_29                    (b_ilat_proba[29]),
  .cfg_b_ilat_range_30_min                (b_ilat_min[30]),
  .cfg_b_ilat_range_30_width_mask         (b_ilat_width_mask[30]),
  .cfg_b_ilat_proba_30                    (b_ilat_proba[30]),
  .cfg_b_ilat_range_31_min                (b_ilat_min[31]),
  .cfg_b_ilat_range_31_width_mask         (b_ilat_width_mask[31]),
  .cfg_b_ilat_proba_31                    (b_ilat_proba[31]),

  
  .cfg_r_ilat_range_0_min                 (r_ilat_min[0]),
  .cfg_r_ilat_range_0_width_mask          (r_ilat_width_mask[0]),
  .cfg_r_ilat_proba_0                     (r_ilat_proba[0]),
  .cfg_r_ilat_range_1_min                 (r_ilat_min[1]),
  .cfg_r_ilat_range_1_width_mask          (r_ilat_width_mask[1]),
  .cfg_r_ilat_proba_1                     (r_ilat_proba[1]),
  .cfg_r_ilat_range_2_min                 (r_ilat_min[2]),
  .cfg_r_ilat_range_2_width_mask          (r_ilat_width_mask[2]),
  .cfg_r_ilat_proba_2                     (r_ilat_proba[2]),
  .cfg_r_ilat_range_3_min                 (r_ilat_min[3]),
  .cfg_r_ilat_range_3_width_mask          (r_ilat_width_mask[3]),
  .cfg_r_ilat_proba_3                     (r_ilat_proba[3]),
  .cfg_r_ilat_range_4_min                 (r_ilat_min[4]),
  .cfg_r_ilat_range_4_width_mask          (r_ilat_width_mask[4]),
  .cfg_r_ilat_proba_4                     (r_ilat_proba[4]),
  .cfg_r_ilat_range_5_min                 (r_ilat_min[5]),
  .cfg_r_ilat_range_5_width_mask          (r_ilat_width_mask[5]),
  .cfg_r_ilat_proba_5                     (r_ilat_proba[5]),
  .cfg_r_ilat_range_6_min                 (r_ilat_min[6]),
  .cfg_r_ilat_range_6_width_mask          (r_ilat_width_mask[6]),
  .cfg_r_ilat_proba_6                     (r_ilat_proba[6]),
  .cfg_r_ilat_range_7_min                 (r_ilat_min[7]),
  .cfg_r_ilat_range_7_width_mask          (r_ilat_width_mask[7]),
  .cfg_r_ilat_proba_7                     (r_ilat_proba[7]),
  .cfg_r_ilat_range_8_min                 (r_ilat_min[8]),
  .cfg_r_ilat_range_8_width_mask          (r_ilat_width_mask[8]),
  .cfg_r_ilat_proba_8                     (r_ilat_proba[8]),
  .cfg_r_ilat_range_9_min                 (r_ilat_min[9]),
  .cfg_r_ilat_range_9_width_mask          (r_ilat_width_mask[9]),
  .cfg_r_ilat_proba_9                     (r_ilat_proba[9]),
  .cfg_r_ilat_range_10_min                (r_ilat_min[10]),
  .cfg_r_ilat_range_10_width_mask         (r_ilat_width_mask[10]),
  .cfg_r_ilat_proba_10                    (r_ilat_proba[10]),
  .cfg_r_ilat_range_11_min                (r_ilat_min[11]),
  .cfg_r_ilat_range_11_width_mask         (r_ilat_width_mask[11]),
  .cfg_r_ilat_proba_11                    (r_ilat_proba[11]),
  .cfg_r_ilat_range_12_min                (r_ilat_min[12]),
  .cfg_r_ilat_range_12_width_mask         (r_ilat_width_mask[12]),
  .cfg_r_ilat_proba_12                    (r_ilat_proba[12]),
  .cfg_r_ilat_range_13_min                (r_ilat_min[13]),
  .cfg_r_ilat_range_13_width_mask         (r_ilat_width_mask[13]),
  .cfg_r_ilat_proba_13                    (r_ilat_proba[13]),
  .cfg_r_ilat_range_14_min                (r_ilat_min[14]),
  .cfg_r_ilat_range_14_width_mask         (r_ilat_width_mask[14]),
  .cfg_r_ilat_proba_14                    (r_ilat_proba[14]),
  .cfg_r_ilat_range_15_min                (r_ilat_min[15]),
  .cfg_r_ilat_range_15_width_mask         (r_ilat_width_mask[15]),
  .cfg_r_ilat_proba_15                    (r_ilat_proba[15]),
  .cfg_r_ilat_range_16_min                (r_ilat_min[16]),
  .cfg_r_ilat_range_16_width_mask         (r_ilat_width_mask[16]),
  .cfg_r_ilat_proba_16                    (r_ilat_proba[16]),
  .cfg_r_ilat_range_17_min                (r_ilat_min[17]),
  .cfg_r_ilat_range_17_width_mask         (r_ilat_width_mask[17]),
  .cfg_r_ilat_proba_17                    (r_ilat_proba[17]),
  .cfg_r_ilat_range_18_min                (r_ilat_min[18]),
  .cfg_r_ilat_range_18_width_mask         (r_ilat_width_mask[18]),
  .cfg_r_ilat_proba_18                    (r_ilat_proba[18]),
  .cfg_r_ilat_range_19_min                (r_ilat_min[19]),
  .cfg_r_ilat_range_19_width_mask         (r_ilat_width_mask[19]),
  .cfg_r_ilat_proba_19                    (r_ilat_proba[19]),
  .cfg_r_ilat_range_20_min                (r_ilat_min[20]),
  .cfg_r_ilat_range_20_width_mask         (r_ilat_width_mask[20]),
  .cfg_r_ilat_proba_20                    (r_ilat_proba[20]),
  .cfg_r_ilat_range_21_min                (r_ilat_min[21]),
  .cfg_r_ilat_range_21_width_mask         (r_ilat_width_mask[21]),
  .cfg_r_ilat_proba_21                    (r_ilat_proba[21]),
  .cfg_r_ilat_range_22_min                (r_ilat_min[22]),
  .cfg_r_ilat_range_22_width_mask         (r_ilat_width_mask[22]),
  .cfg_r_ilat_proba_22                    (r_ilat_proba[22]),
  .cfg_r_ilat_range_23_min                (r_ilat_min[23]),
  .cfg_r_ilat_range_23_width_mask         (r_ilat_width_mask[23]),
  .cfg_r_ilat_proba_23                    (r_ilat_proba[23]),
  .cfg_r_ilat_range_24_min                (r_ilat_min[24]),
  .cfg_r_ilat_range_24_width_mask         (r_ilat_width_mask[24]),
  .cfg_r_ilat_proba_24                    (r_ilat_proba[24]),
  .cfg_r_ilat_range_25_min                (r_ilat_min[25]),
  .cfg_r_ilat_range_25_width_mask         (r_ilat_width_mask[25]),
  .cfg_r_ilat_proba_25                    (r_ilat_proba[25]),
  .cfg_r_ilat_range_26_min                (r_ilat_min[26]),
  .cfg_r_ilat_range_26_width_mask         (r_ilat_width_mask[26]),
  .cfg_r_ilat_proba_26                    (r_ilat_proba[26]),
  .cfg_r_ilat_range_27_min                (r_ilat_min[27]),
  .cfg_r_ilat_range_27_width_mask         (r_ilat_width_mask[27]),
  .cfg_r_ilat_proba_27                    (r_ilat_proba[27]),
  .cfg_r_ilat_range_28_min                (r_ilat_min[28]),
  .cfg_r_ilat_range_28_width_mask         (r_ilat_width_mask[28]),
  .cfg_r_ilat_proba_28                    (r_ilat_proba[28]),
  .cfg_r_ilat_range_29_min                (r_ilat_min[29]),
  .cfg_r_ilat_range_29_width_mask         (r_ilat_width_mask[29]),
  .cfg_r_ilat_proba_29                    (r_ilat_proba[29]),
  .cfg_r_ilat_range_30_min                (r_ilat_min[30]),
  .cfg_r_ilat_range_30_width_mask         (r_ilat_width_mask[30]),
  .cfg_r_ilat_proba_30                    (r_ilat_proba[30]),
  .cfg_r_ilat_range_31_min                (r_ilat_min[31]),
  .cfg_r_ilat_range_31_width_mask         (r_ilat_width_mask[31]),
  .cfg_r_ilat_proba_31                    (r_ilat_proba[31]),

  
  .cfg_w_blat_range_min                   (w_blat_min),
  .cfg_w_blat_range_width_mask            (w_blat_width_mask),
  .cfg_w_blat_proba                       (w_blat_proba),

  
  .cfg_ar_delay                           (ar_delay_len),

  
  .cfg_r_fault_seed_value                 (r_fault_seed),
  .cfg_r_fault_seed_reset                 (r_fault_restart),
  .cfg_r_fault_param_probThresReq         (r_fault_probThresReq),
  .cfg_r_fault_param_cmd                  (r_fault_cmd),
  .cfg_r_fault_param_id                   (r_fault_id),
  .cfg_r_fault_pattern_0                  (r_fault_regPattern[255:224]),
  .cfg_r_fault_pattern_1                  (r_fault_regPattern[223:192]),
  .cfg_r_fault_pattern_2                  (r_fault_regPattern[191:160]),
  .cfg_r_fault_pattern_3                  (r_fault_regPattern[159:128]),
  .cfg_r_fault_pattern_4                  (r_fault_regPattern[127:96]),
  .cfg_r_fault_pattern_5                  (r_fault_regPattern[95:64]),
  .cfg_r_fault_pattern_6                  (r_fault_regPattern[63:32]),
  .cfg_r_fault_pattern_7                  (r_fault_regPattern[31:0]),
  .sts_r_fault_stats_lfsr                 (r_fault_stats_lfsr),
  .sts_r_fault_stats_nb_err               (r_fault_stats_nberror),
  .sts_r_fault_stats_nb_req               (r_fault_stats_nbrequest),

  
  .cfg_outstanding_max_read               (outstanding_max_read),
  .cfg_outstanding_max_write              (outstanding_max_write),
  .sts_outstanding_cur_read               (outstanding_cur_read),
  .sts_outstanding_cur_write              (outstanding_cur_write),

  
  .cfg_bandwidth_rst_reset                (bandwidth_rst),
  .cfg_bandwidth_rst_id                   (bandwidth_id),
  .sts_bandwidth_read_all                 (bandwidth_read_all),
  .sts_bandwidth_read_id                  (bandwidth_read_id),
  .sts_bandwidth_write_all                (bandwidth_write_all),
  .sts_bandwidth_write_id                 (bandwidth_write_id),

  
  .cfg_axi_offset_msb                     (axi_offset_msb),
  .cfg_axi_offset_lsb                     (axi_offset_lsb),
  .cfg_axi_reset_status                   (axi_reset_status),
  .sts_len_max_ar                         (axi_len_max_ar),
  .sts_len_max_aw                         (axi_len_max_aw),
  .sts_bytes_max_ar                       (axi_bytes_max_ar),
  .sts_bytes_max_aw                       (axi_bytes_max_aw),
  .sts_axi_idle_counter                   (axi_idle_counter),
  .sts_axi_nb_packet_read                 (axi_nb_packet_read),
  .sts_axi_nb_packet_write                (axi_nb_packet_write),
  .sts_axi_sts_read_resp_err              (axi_sts_read_resp_err),
  .sts_axi_sts_write_resp_err             (axi_sts_write_resp_err),
  .sts_axi_addr_read_min_msb              (axi_addr_read_min_msb),
  .sts_axi_addr_read_min_lsb              (axi_addr_read_min_lsb),
  .sts_axi_addr_read_max_msb              (axi_addr_read_max_msb),
  .sts_axi_addr_read_max_lsb              (axi_addr_read_max_lsb),
  .sts_axi_addr_write_min_msb             (axi_addr_write_min_msb),
  .sts_axi_addr_write_min_lsb             (axi_addr_write_min_lsb),
  .sts_axi_addr_write_max_msb             (axi_addr_write_max_msb),
  .sts_axi_addr_write_max_lsb             (axi_addr_write_max_lsb),

  
  .cfg_delay_mean_cfg_cnt_rst             (delay_mean_cnt_rst),
  .sts_delay_mean_total_delay_total       (delay_mean_total_delay_total),
  .sts_delay_mean_total_delay_total_msb   (delay_mean_total_delay_total_msb),
  .sts_delay_mean_sts_nb_request          (delay_mean_nb_request),
  .sts_delay_mean_sts_nb_request_msb      (delay_mean_nb_request_msb),
  .sts_delay_mean_max_value_req           (delay_mean_max_value_req),
  .sts_delay_mean_min_value_req           (delay_mean_min_value_req),
  .sts_delay_mean_sts_err_fifo_full       (delay_mean_err_fifo_full),
  .sts_delay_mean_sts_err_nbreq_overflow  (delay_mean_err_nbreq_overflow),
  .sts_delay_mean_sts_err_timer_overflow  (delay_mean_err_timer_overflow),
  .sts_delay_mean_sts_err_total_overflow  (delay_mean_err_total_overflow),

  
  .cfg_delay_distr_value                  (delay_distr_value),
  .cfg_delay_distr_nbreq                  (delay_distr_nbreq),
  .cfg_delay_distr_enable                 (delay_distr_enable),
  .cfg_delay_distr_rstptr                 (delay_distr_rstptr_wr),
  .cfg_delay_distr_write                  (delay_distr_write),

  
  .psel                                   (apb_resync.sel),
  .penable                                (apb_resync.enable),
  .pwrite                                 (apb_resync.write),
  .paddr                                  (apb_resync.addr),
  .pwdata                                 (apb_resync.wdata),
  .prdata                                 (apb_resync.rdata),
  .pready                                 (apb_resync.ready),

  
  .clk                                    (apb_resync.clk),
  .rstn                                   (apb_resync.rstn)
);



always_ff @(posedge aclk) begin
  if (!aresetn) begin

    ar_blat_seed_rst   <= 1'b0;
    ar_ilat_seed_rst   <= 1'b0;
    aw_blat_seed_rst   <= 1'b0;
    b_ilat_seed_rst    <= 1'b0;
    r_ilat_seed_rst    <= 1'b0;
    w_blat_seed_rst    <= 1'b0;

    ar_blat_seed       <= '0;
    ar_ilat_seed       <= '0;
    aw_blat_seed       <= '0;
    b_ilat_seed        <= '0;
    r_ilat_seed        <= '0;
    w_blat_seed        <= '0;

    delay_distr_seed      <= '0;
    delay_distr_rstptr_rd <= 1'b0;

  end else begin

    ar_blat_seed_rst   <= 1'b0;
    ar_ilat_seed_rst   <= 1'b0;
    aw_blat_seed_rst   <= 1'b0;
    b_ilat_seed_rst    <= 1'b0;
    r_ilat_seed_rst    <= 1'b0;
    w_blat_seed_rst    <= 1'b0;

    delay_distr_rstptr_rd <= 1'b0;

    if (global_seed_reset) begin

      ar_blat_seed_rst        <= 1'b1;
      aw_blat_seed_rst        <= 1'b1;
      w_blat_seed_rst         <= 1'b1;

      delay_distr_rstptr_rd   <= 1'b1;

      ar_blat_seed            <= global_seed_value + 0;
      aw_blat_seed            <= global_seed_value + 1;
      w_blat_seed             <= global_seed_value + 2;

      delay_distr_seed        <= global_seed_value;

      for (int i = 0; i < 32; i++) begin

        ar_ilat_seed_rst[i]   <= 1'b1;
        b_ilat_seed_rst[i]    <= 1'b1;
        r_ilat_seed_rst[i]    <= 1'b1;

        ar_ilat_seed[i]       <= global_seed_value + 3 + 3*i + 0;
        b_ilat_seed[i]        <= global_seed_value + 3 + 3*i + 1;
        r_ilat_seed[i]        <= global_seed_value + 3 + 3*i + 2;

      end

    end
  end
end

endmodule
