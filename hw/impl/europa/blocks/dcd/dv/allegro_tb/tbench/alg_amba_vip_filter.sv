


module alg_amba_vip_filter #(
  parameter DATA_WIDTH = 128,
  parameter OUTSTANDING_LOG2_MAX = 6
)(
  
  input  logic                         axi_reset_status,
  
  output logic [15:0]                  outstanding_cur_read,
  output logic [15:0]                  outstanding_cur_write,
  input  logic [15:0]                  outstanding_max_read,
  input  logic [15:0]                  outstanding_max_write,
  
  input  logic                         bandwidth_rst,
  input  logic [4:0]                   bandwidth_id,
  output logic [31:0]                  bandwidth_read_total,
  output logic [31:0]                  bandwidth_read_id,
  output logic [31:0]                  bandwidth_write_total,
  output logic [31:0]                  bandwidth_write_id,
  
  output logic [31:0]                  idle_cnt,
  output logic [7:0]                   ar_len_max,
  output logic [7:0]                   aw_len_max,
  output logic [15:0]                  ar_bytes_max,
  output logic [15:0]                  aw_bytes_max,
  
  input  logic [0:0]                   delay_mean_cnt_rst,
  output logic [63:0]                  delay_mean_total_delay_total,
  output logic [55:0]                  delay_mean_nb_request,
  output logic [15:0]                  delay_mean_max_value_req,
  output logic [15:0]                  delay_mean_min_value_req,
  output logic [0:0]                   delay_mean_err_fifo_full,
  output logic [0:0]                   delay_mean_err_nbreq_overflow,
  output logic [0:0]                   delay_mean_err_timer_overflow,
  output logic [0:0]                   delay_mean_err_total_overflow,
  
  input  logic [31:0]                  axi_offset_msb,
  input  logic [31:0]                  axi_offset_lsb,
  output logic [15:0]                  ar_nb_packet,
  output logic [15:0]                  aw_nb_packet,
  output logic                         read_resp_err,
  output logic                         write_resp_err,
  output logic [31:0]                  read_addr_min_msb,
  output logic [31:0]                  read_addr_min_lsb,
  output logic [31:0]                  read_addr_max_msb,
  output logic [31:0]                  read_addr_max_lsb,
  output logic [31:0]                  write_addr_min_msb,
  output logic [31:0]                  write_addr_min_lsb,
  output logic [31:0]                  write_addr_max_msb,
  output logic [31:0]                  write_addr_max_lsb,
  
  al_vip_axi_if.slavemod               s_axi,
  al_vip_axi_if.mastermod              m_axi
);


logic [16:0]    ar_bytes_cur;
logic [16:0]    aw_bytes_cur;

logic ar_enable;
logic aw_enable;

logic [63:0]                  read_addr_min;
logic [63:0]                  read_addr_max;
logic [63:0]                  write_addr_min;
logic [63:0]                  write_addr_max;

logic        ar_packet;
logic        aw_packet;
logic        r_packet;
logic        b_packet;

logic        delay_stats_send;
logic        delay_stats_ack;

logic [0:31] [31:0]   bandwidth_read;
logic [0:31] [31:0]   bandwidth_write;

assign m_axi.araddr  = s_axi.araddr + {axi_offset_msb, axi_offset_lsb};
assign m_axi.arburst = s_axi.arburst;
assign m_axi.arid    = s_axi.arid;
assign m_axi.arlen   = s_axi.arlen;
assign m_axi.arsize  = s_axi.arsize;
assign m_axi.awaddr  = s_axi.awaddr + {axi_offset_msb, axi_offset_lsb};
assign m_axi.awburst = s_axi.awburst;
assign m_axi.awid    = s_axi.awid;
assign m_axi.awlen   = s_axi.awlen;
assign m_axi.awsize  = s_axi.awsize;
assign m_axi.bready  = s_axi.bready;
assign s_axi.bvalid  = m_axi.bvalid;
assign s_axi.bresp   = m_axi.bresp;
assign s_axi.bid     = m_axi.bid;
assign s_axi.rdata   = m_axi.rdata;
assign s_axi.rid     = m_axi.rid;
assign s_axi.rlast   = m_axi.rlast;
assign m_axi.rready  = s_axi.rready;
assign s_axi.rvalid  = m_axi.rvalid;
assign s_axi.rresp   = m_axi.rresp;
assign m_axi.wdata   = s_axi.wdata;
assign m_axi.wstrb   = s_axi.wstrb;
assign m_axi.wlast   = s_axi.wlast;
assign s_axi.wready  = m_axi.wready;
assign m_axi.wvalid  = s_axi.wvalid;

assign ar_packet = s_axi.arvalid && s_axi.arready;
assign aw_packet = s_axi.awvalid && s_axi.awready;
assign r_packet  = s_axi.rvalid  && s_axi.rready && s_axi.rlast;
assign b_packet  = s_axi.bvalid  && s_axi.bready;


assign ar_enable     = ((outstanding_cur_read  < outstanding_max_read)  || outstanding_max_read  == 0) ? 1'b1 : 1'b0;
assign aw_enable     = ((outstanding_cur_write < outstanding_max_write) || outstanding_max_write == 0) ? 1'b1 : 1'b0;
assign m_axi.arvalid = ar_enable ? s_axi.arvalid : 1'b0;
assign s_axi.arready = ar_enable ? m_axi.arready : 1'b0;
assign m_axi.awvalid = aw_enable ? s_axi.awvalid : 1'b0;
assign s_axi.awready = aw_enable ? m_axi.awready : 1'b0;




always_ff @(posedge s_axi.clk) begin
  if (~s_axi.rstn) begin
    outstanding_cur_read   <= '0;
    outstanding_cur_write  <= '0;
  end else begin
    if (ar_packet  && !r_packet) begin
      outstanding_cur_read  <= outstanding_cur_read + 1;
    end else if (!ar_packet &&  r_packet) begin
      outstanding_cur_read  <= outstanding_cur_read - 1;
    end
    if (aw_packet  && !b_packet) begin
      outstanding_cur_write  <= outstanding_cur_write + 1;
    end else if (!aw_packet &&  b_packet) begin
      outstanding_cur_write  <= outstanding_cur_write - 1;
    end
  end
end


always @(s_axi.arlen, s_axi.arsize) begin
  case (s_axi.arsize)
    3'b000:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1)};
    3'b001:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 1'b0};
    3'b010:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 2'b00};
    3'b011:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 3'b000};
    3'b100:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 4'b0000};
    3'b101:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 5'b00000};
    3'b110:  ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 6'b000000};
    default: ar_bytes_cur <= {({1'b0, s_axi.arlen} + 1'b1), 7'b0000000};
  endcase
end
always @(s_axi.awlen, s_axi.awsize) begin
  case (s_axi.awsize)
    3'b000:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1)};
    3'b001:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 1'b0};
    3'b010:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 2'b00};
    3'b011:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 3'b000};
    3'b100:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 4'b0000};
    3'b101:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 5'b00000};
    3'b110:  aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 6'b000000};
    default: aw_bytes_cur <= {({1'b0, s_axi.awlen} + 1'b1), 7'b0000000};
  endcase
end


assign bandwidth_read_id   = bandwidth_read[bandwidth_id];
assign bandwidth_write_id  = bandwidth_write[bandwidth_id];

always_ff @(posedge s_axi.clk) begin
  if (~s_axi.rstn) begin
    bandwidth_read_total  <= '0;
    bandwidth_read        <= '0;
    bandwidth_write_total <= '0;
    bandwidth_write       <= '0;
    ar_bytes_max          <= '0;
    aw_bytes_max          <= '0;
  end else begin


    if (axi_reset_status) begin
      ar_bytes_max    <= '0;
    end else if (ar_packet && (ar_bytes_max < ar_bytes_cur)) begin
      ar_bytes_max    <= ar_bytes_cur;
    end
    if (axi_reset_status) begin
      aw_bytes_max    <= '0;
    end else if (aw_packet && (aw_bytes_max < aw_bytes_cur)) begin
      aw_bytes_max    <= aw_bytes_cur;
    end

    if (bandwidth_rst) begin
      bandwidth_read_total    <= '0;
      bandwidth_read          <= '0;
    end else if (ar_packet) begin
      bandwidth_read_total    <= bandwidth_read_total + ar_bytes_cur;
      bandwidth_read[s_axi.arid] <= bandwidth_read[s_axi.arid] + ar_bytes_cur;
    end

    if (bandwidth_rst) begin
      bandwidth_write_total   <= '0;
      bandwidth_write         <= '0;
    end else if (aw_packet) begin
      bandwidth_write_total   <= bandwidth_write_total + aw_bytes_cur;
      bandwidth_write[s_axi.awid] <= bandwidth_write[s_axi.awid] + aw_bytes_cur;
    end

  end
end


always_ff @(posedge s_axi.clk) begin
  if (~s_axi.rstn) begin
    ar_len_max      <= '0;
    aw_len_max      <= '0;
  end else begin
    if (axi_reset_status) begin
      ar_len_max    <= '0;
    end else if (ar_packet && (ar_len_max < s_axi.arlen)) begin
      ar_len_max    <= s_axi.arlen;
    end
    if (axi_reset_status) begin
      aw_len_max    <= '0;
    end else if (aw_packet && (aw_len_max < s_axi.awlen)) begin
      aw_len_max    <= s_axi.awlen;
    end
  end
end


always_ff @(posedge s_axi.clk) begin
  if (~s_axi.rstn) begin
    idle_cnt    <= '0;
  end else begin
    if ((axi_reset_status)               ||
        (s_axi.arvalid && s_axi.arready) ||
        (s_axi.awvalid && s_axi.awready) ||
        (s_axi.bvalid  && s_axi.bready)  ||
        (s_axi.rvalid  && s_axi.rready)  ||
        (s_axi.wvalid  && s_axi.wready)) begin
      idle_cnt  <= '0;
    end else begin
      if (idle_cnt != 32'hFFFFFFFF) begin
        idle_cnt  <= idle_cnt + 1;
      end
    end
  end
end



assign delay_stats_send = s_axi.arvalid && s_axi.arready;
assign delay_stats_ack  = s_axi.rvalid  && s_axi.rready && s_axi.rlast;

alg_amba_vip_base_delay_stats #(
  .TIMER_WIDTH             (64),
  .OUTSTANDING_LOG2_MAX    (OUTSTANDING_LOG2_MAX)
) DELAY_STAT_READ (
  .clk                     (s_axi.clk),
  .rstn                    (s_axi.rstn),
  
  .cnt_rst                 (delay_mean_cnt_rst),
  
  .send_valid              (delay_stats_send),
  .ack_valid               (delay_stats_ack),
  
  .delay_total             (delay_mean_total_delay_total),
  .nb_request              (delay_mean_nb_request),
  .max_value_req           (delay_mean_max_value_req),
  .min_value_req           (delay_mean_min_value_req),
  .err_fifo_full           (delay_mean_err_fifo_full),
  .err_nbreq_overflow      (delay_mean_err_nbreq_overflow),
  .err_timer_overflow      (delay_mean_err_timer_overflow),
  .err_total_overflow      (delay_mean_err_total_overflow)
);


assign read_addr_min_msb  = read_addr_min[63:32];
assign read_addr_min_lsb  = read_addr_min[31:0];
assign read_addr_max_msb  = read_addr_max[63:32];
assign read_addr_max_lsb  = read_addr_max[31:0];
assign write_addr_min_msb = write_addr_min[63:32];
assign write_addr_min_lsb = write_addr_min[31:0];
assign write_addr_max_msb = write_addr_max[63:32];
assign write_addr_max_lsb = write_addr_max[31:0];
always_ff @(posedge s_axi.clk) begin
  if (~s_axi.rstn) begin
    ar_nb_packet    <= '0;
    aw_nb_packet    <= '0;
    read_resp_err   <= 1'b0;
    write_resp_err  <= 1'b0;
    read_addr_min   <= '1;
    read_addr_max   <= '0;
    write_addr_min  <= '1;
    write_addr_max  <= '0;
  end else begin

    if (axi_reset_status) begin
      ar_nb_packet  <= '0;
    end else if (ar_packet) begin
      ar_nb_packet  <= ar_nb_packet + 1;
    end
    if (axi_reset_status) begin
      aw_nb_packet  <= '0;
    end else if (aw_packet) begin
      aw_nb_packet  <= aw_nb_packet + 1;
    end

    if (axi_reset_status) begin
      read_resp_err <= 1'b0;
    end else if (s_axi.rvalid && s_axi.rready && (s_axi.rresp > 0)) begin
      read_resp_err <= 1'b1;
    end
    if (axi_reset_status) begin
      write_resp_err <= 1'b0;
    end else if (s_axi.bvalid && s_axi.bready && (s_axi.bresp > 0)) begin
      write_resp_err <= 1'b1;
    end

    if (axi_reset_status) begin
      read_addr_min  <= '1;
      read_addr_max  <= '0;
    end else if (ar_packet) begin
      if (read_addr_min > s_axi.araddr) begin
        read_addr_min <= s_axi.araddr;
      end
      if (read_addr_max < s_axi.araddr) begin
        read_addr_max <= s_axi.araddr;
      end
    end
    if (axi_reset_status) begin
      write_addr_min  <= '1;
      write_addr_max  <= '0;
    end else if (aw_packet) begin
      if (write_addr_min > s_axi.awaddr) begin
        write_addr_min <= s_axi.awaddr;
      end
      if (write_addr_max < s_axi.awaddr) begin
        write_addr_max <= s_axi.awaddr;
      end
    end

  end
end

endmodule
