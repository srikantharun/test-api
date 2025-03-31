// external decoders

logic [39:0] i_config_axi_m_01_araddr;
logic [39:0] i_config_axi_m_01_awaddr;
logic [39:0] i_config_axi_m_02_araddr;
logic [39:0] i_config_axi_m_02_awaddr;

logic [39:0] i_lp_axi_m_01_araddr;
logic [39:0] i_lp_axi_m_01_awaddr;
logic [39:0] i_lp_axi_m_04_araddr;
logic [39:0] i_lp_axi_m_04_awaddr;
logic [39:0] i_lp_axi_m_05_araddr;
logic [39:0] i_lp_axi_m_05_awaddr;
logic [39:0] i_lp_axi_m_06_araddr;
logic [39:0] i_lp_axi_m_06_awaddr;

logic [39:0] i_hp_axi_m_01_araddr;
logic [39:0] i_hp_axi_m_01_awaddr;

logic [AIC_FABRIC_CONFIG_NUM_MASTERS:1][39:0] config_m_araddr;
logic [AIC_FABRIC_LP_NUM_MASTERS:1][39:0] lp_m_araddr;
logic [AIC_FABRIC_CONTROL_NUM_MASTERS:1][39:0] control_m_araddr;
logic [AIC_FABRIC_HP_NUM_MASTERS:1][39:0] hp_m_araddr;
logic [AIC_FABRIC_CVA6_DEMUX_NUM_MASTERS:1][39:0] cva6_demux_m_araddr;
logic [AIC_FABRIC_NOC_LP_S_DEMUX_NUM_MASTERS:1][39:0] noc_lp_s_demux_m_araddr;
logic [AIC_FABRIC_ACD_DEMUX_NUM_MASTERS:1][39:0] acd_demux_m_araddr;

logic [AIC_FABRIC_CONFIG_NUM_MASTERS:1][39:0] config_m_awaddr;
logic [AIC_FABRIC_LP_NUM_MASTERS:1][39:0] lp_m_awaddr;
logic [AIC_FABRIC_CONTROL_NUM_MASTERS:1][39:0] control_m_awaddr;
logic [AIC_FABRIC_HP_NUM_MASTERS:1][39:0] hp_m_awaddr;
logic [AIC_FABRIC_CVA6_DEMUX_NUM_MASTERS:1][39:0] cva6_demux_m_awaddr;
logic [AIC_FABRIC_NOC_LP_S_DEMUX_NUM_MASTERS:1][39:0] noc_lp_s_demux_m_awaddr;
logic [AIC_FABRIC_ACD_DEMUX_NUM_MASTERS:1][39:0] acd_demux_m_awaddr;

logic [AIC_FABRIC_ACD_DEMUX_NUM_MASTERS:1][1:0] acd_demux_xdcdr_slv_num_rd;
logic [AIC_FABRIC_ACD_DEMUX_NUM_MASTERS:1][1:0] acd_demux_xdcdr_slv_num_wr;
logic [AIC_FABRIC_CONFIG_NUM_MASTERS:1][3:0] config_bus_xdcdr_slv_num_rd;
logic [AIC_FABRIC_CONFIG_NUM_MASTERS:1][3:0] config_bus_xdcdr_slv_num_wr;
logic [AIC_FABRIC_CONTROL_NUM_MASTERS:1][1:0] control_xdcdr_slv_num_wr_pre; // before firewall
logic [AIC_FABRIC_CONTROL_NUM_MASTERS:1][1:0] control_xdcdr_slv_num_rd;
logic [AIC_FABRIC_CONTROL_NUM_MASTERS:1][1:0] control_xdcdr_slv_num_wr;
logic [AIC_FABRIC_CVA6_DEMUX_NUM_MASTERS:1][1:0] cva6_demux_xdcdr_slv_num_rd;
logic [AIC_FABRIC_CVA6_DEMUX_NUM_MASTERS:1][1:0] cva6_demux_xdcdr_slv_num_wr;
logic [AIC_FABRIC_HP_NUM_MASTERS:1][1:0] hp_xdcdr_slv_num_rd;
logic [AIC_FABRIC_HP_NUM_MASTERS:1][1:0] hp_xdcdr_slv_num_wr;
logic [AIC_FABRIC_LP_NUM_MASTERS:1][1:0] lp_xdcdr_slv_num_rd;
logic [AIC_FABRIC_LP_NUM_MASTERS:1][1:0] lp_xdcdr_slv_num_wr;
logic [AIC_FABRIC_NOC_LP_S_DEMUX_NUM_MASTERS:1][1:0] noc_lp_s_demux_xdcdr_slv_num_rd;
logic [AIC_FABRIC_NOC_LP_S_DEMUX_NUM_MASTERS:1][1:0] noc_lp_s_demux_xdcdr_slv_num_wr;

logic [AIC_FABRIC_DATAPATH_FIREWALL_NUM_ADDR_REGION-1:0] datapath_firewall_region_w_hit;
logic datapath_firewall_w_hit;

always_comb begin
  config_m_araddr[1] = i_config_axi_m_01_araddr;
  config_m_araddr[2] = i_config_axi_m_02_araddr;
  config_m_awaddr[1] = i_config_axi_m_01_awaddr;
  config_m_awaddr[2] = i_config_axi_m_02_awaddr;
end

always_comb begin
  control_m_araddr[1] = i_control_axi_m_01_araddr;
  control_m_araddr[2] = i_control_axi_m_02_araddr;
  control_m_awaddr[1] = i_control_axi_m_01_awaddr;
  control_m_awaddr[2] = i_control_axi_m_02_awaddr;
end

always_comb begin
  lp_m_araddr[1] = i_lp_axi_m_01_araddr;
  lp_m_araddr[2] = i_lp_axi_m_02_araddr;
  lp_m_araddr[3] = i_lp_axi_m_03_araddr;
  lp_m_araddr[4] = i_lp_axi_m_04_araddr;
  lp_m_araddr[5] = i_lp_axi_m_05_araddr;
  lp_m_araddr[6] = i_lp_axi_m_06_araddr;
  lp_m_awaddr[1] = i_lp_axi_m_01_awaddr;
  lp_m_awaddr[2] = i_lp_axi_m_02_awaddr;
  lp_m_awaddr[3] = i_lp_axi_m_03_awaddr;
  lp_m_awaddr[4] = i_lp_axi_m_04_awaddr;
  lp_m_awaddr[5] = i_lp_axi_m_05_awaddr;
  lp_m_awaddr[6] = i_lp_axi_m_06_awaddr;
end

always_comb begin
  hp_m_araddr[1] = i_hp_axi_m_01_araddr;
  hp_m_araddr[2] = i_hp_axi_m_02_araddr;
  hp_m_araddr[3] = i_hp_axi_m_03_araddr;
  hp_m_awaddr[1] = i_hp_axi_m_01_awaddr;
  hp_m_awaddr[2] = i_hp_axi_m_02_awaddr;
  hp_m_awaddr[3] = i_hp_axi_m_03_awaddr;
end

always_comb begin
  cva6_demux_m_araddr[1] = i_cva6_demux_axi_m_01_araddr;
  cva6_demux_m_awaddr[1] = i_cva6_demux_axi_m_01_awaddr;
end

always_comb begin
  noc_lp_s_demux_m_araddr[1] = i_noc_lp_s_demux_axi_m_01_araddr;
  noc_lp_s_demux_m_awaddr[1] = i_noc_lp_s_demux_axi_m_01_awaddr;
end

always_comb begin
  acd_demux_m_araddr[1] = i_acd_demux_axi_m_01_araddr;
  acd_demux_m_awaddr[1] = i_acd_demux_axi_m_01_awaddr;
end

// CONFIG master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_CONFIG_NUM_MASTERS; i = i + 1) begin : config_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CONFIG_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CONFIG_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CONFIG_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CONFIG_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CONFIG_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CONFIG_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CONFIG_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CONFIG_SL_IDX)
    ) u_rd_dec_config_m (
      .addr_in  (config_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(config_bus_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CONFIG_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CONFIG_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CONFIG_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CONFIG_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CONFIG_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CONFIG_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CONFIG_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CONFIG_SL_IDX)
    ) u_wr_dec_config_m (
      .addr_in  (config_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(config_bus_xdcdr_slv_num_wr[i])
    );

  end
endgenerate

// LP master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_LP_NUM_MASTERS; i = i + 1) begin : lp_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_LP_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_LP_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_LP_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_LP_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_LP_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_LP_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_LP_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_LP_SL_IDX)
    ) u_rd_dec_lp_m (
      .addr_in  (lp_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(lp_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_LP_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_LP_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_LP_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_LP_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_LP_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_LP_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_LP_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_LP_SL_IDX)
    ) u_wr_dec_lp_m (
      .addr_in  (lp_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(lp_xdcdr_slv_num_wr[i])
    );
  end
endgenerate

// CONTROL master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_CONTROL_NUM_MASTERS; i = i + 1) begin : control_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CONTROL_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CONTROL_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CONTROL_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CONTROL_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CONTROL_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CONTROL_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CONTROL_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CONTROL_SL_IDX)
    ) u_rd_dec_control_m (
      .addr_in  (control_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(control_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CONTROL_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CONTROL_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CONTROL_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CONTROL_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CONTROL_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CONTROL_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CONTROL_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CONTROL_SL_IDX)
    ) u_wr_dec_control_m (
      .addr_in  (control_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(control_xdcdr_slv_num_wr_pre[i])
    );
  end
endgenerate

generate
  for (genvar i=0; i < AIC_FABRIC_DATAPATH_FIREWALL_NUM_ADDR_REGION; i=i+1) begin : gen_firewall_region_w_hit
    always_comb datapath_firewall_region_w_hit[i] = control_m_awaddr[2] inside {[AIC_FABRIC_DATAPATH_FIREWALL_ADDR_S[i]:AIC_FABRIC_DATAPATH_FIREWALL_ADDR_E[i]]};
  end
  always_comb datapath_firewall_w_hit = |datapath_firewall_region_w_hit;
endgenerate

  // ACD write access
  always_comb control_xdcdr_slv_num_wr[1] = control_xdcdr_slv_num_wr_pre[1] & {$bits(control_xdcdr_slv_num_wr_pre[1]){i_datapath_firewall_sel}};

  // Config write access
  always_comb control_xdcdr_slv_num_wr[2] = control_xdcdr_slv_num_wr_pre[2] & {$bits(control_xdcdr_slv_num_wr_pre[2]){~i_datapath_firewall_sel | ~datapath_firewall_w_hit}};

// CVA6_DEMUX master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_CVA6_DEMUX_NUM_MASTERS; i = i + 1) begin : cva6_demux_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CVA6_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CVA6_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CVA6_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CVA6_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CVA6_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CVA6_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CVA6_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CVA6_DEMUX_SL_IDX)
    ) u_rd_dec_cva6_demux_m (
      .addr_in  (cva6_demux_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(cva6_demux_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_CVA6_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_CVA6_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_CVA6_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_CVA6_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_CVA6_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_CVA6_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_CVA6_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_CVA6_DEMUX_SL_IDX)
    ) u_wr_dec_cva6_demux_m (
      .addr_in  (cva6_demux_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(cva6_demux_xdcdr_slv_num_wr[i])
    );
  end
endgenerate

// HP master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_HP_NUM_MASTERS; i = i + 1) begin : hp_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_HP_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_HP_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_HP_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_HP_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_HP_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_HP_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_HP_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_HP_SL_IDX)
    ) u_rd_dec_hp_m (
      .addr_in  (hp_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(hp_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_HP_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_HP_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_HP_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_HP_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_HP_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_HP_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_HP_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_HP_SL_IDX)
    ) u_wr_dec_hp_m (
      .addr_in  (hp_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(hp_xdcdr_slv_num_wr[i])
    );
  end
endgenerate

// ACD_DEMUX master decoder
generate
  for (genvar i = 1; i <= AIC_FABRIC_ACD_DEMUX_NUM_MASTERS; i = i + 1) begin : acd_demux_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_ACD_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_ACD_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_ACD_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_ACD_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_ACD_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_ACD_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_ACD_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_ACD_DEMUX_SL_IDX)
    ) u_rd_dec_acd_demux_m (
      .addr_in  (acd_demux_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(acd_demux_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_ACD_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_ACD_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_ACD_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_ACD_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_ACD_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_ACD_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_ACD_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_ACD_DEMUX_SL_IDX)
    ) u_wr_dec_acd_demux_m (
      .addr_in  (acd_demux_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(acd_demux_xdcdr_slv_num_wr[i])
    );
  end
endgenerate

// NOC_LP_S_DEMUX master decoder
generate
  for (
      genvar i = 1; i <= AIC_FABRIC_NOC_LP_S_DEMUX_NUM_MASTERS; i = i + 1
  ) begin : noc_lp_s_demux_gen_

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_NOC_LP_S_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_NOC_LP_S_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_NOC_LP_S_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_NOC_LP_S_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_NOC_LP_S_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_NOC_LP_S_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_NOC_LP_S_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_NOC_LP_S_DEMUX_SL_IDX)
    ) u_rd_dec_noc_lp_s_demux_m (
      .addr_in  (noc_lp_s_demux_m_araddr[i]),
      .core_id  (i_core_id),
      .sl_select(noc_lp_s_demux_xdcdr_slv_num_rd[i])
    );

    aic_fabric_addr_decoder #(
      .AW(AIC_FABRIC_AXI_AW),
      .CORE_ID_LSB(AIC_FABRIC_CORE_ID_LSB),
      .NR_CORE_IDS(AIC_FABRIC_NUM_CORE),
      .CORE_IDS(AIC_FABRIC_CORE_ID),
      .DEFAULT_SLAVE(AIC_FABRIC_NOC_LP_S_DEMUX_DEFAULT_SLAVE),
      .NOT_THIS_CORE_SLAVE(AIC_FABRIC_NOC_LP_S_DEMUX_NOT_THIS_CORE_SLAVE),
      .NR_SLAVES(AIC_FABRIC_NOC_LP_S_DEMUX_NUM_SLAVES),
      .NR_REGIONS(AIC_FABRIC_NOC_LP_S_DEMUX_NUM_ADDR_REGION),
      .REGION_IS_CORE(AIC_FABRIC_NOC_LP_S_DEMUX_REGION_IS_CORE),
      .REGION_ST_ADDR(AIC_FABRIC_NOC_LP_S_DEMUX_ADDR_S),
      .REGION_END_ADDR(AIC_FABRIC_NOC_LP_S_DEMUX_ADDR_E),
      .REGION_SLAVE_ID(AIC_FABRIC_NOC_LP_S_DEMUX_SL_IDX)
    ) u_wr_dec_noc_lp_s_demux_m (
      .addr_in  (noc_lp_s_demux_m_awaddr[i]),
      .core_id  (i_core_id),
      .sl_select(noc_lp_s_demux_xdcdr_slv_num_wr[i])
    );
  end
endgenerate
