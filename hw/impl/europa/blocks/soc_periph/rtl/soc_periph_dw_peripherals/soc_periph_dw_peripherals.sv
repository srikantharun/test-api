// This file was automatically generated by coreAssembler (version V-2024.03).
//
// FILENAME : /home/projects/workspace/jmartins/europa/hw/impl/europa/blocks/soc_periph/soc_periph_dw_peripherals/src/soc_periph_dw_peripherals.sv
// DATE : 11/14/24 18:03:03
// ABSTRACT : SystemVerilog top-level subsystem RTL.
//

module soc_periph_dw_peripherals (
    // Ports for Interface PCLK
    input           PCLK_pclk,
    // Ports for Interface PRESETn
    input           PRESETn_presetn,
    // Ports for Interface SIO
    input           SIO_cts_n,
    input           SIO_sin,
    output          SIO_rts_n,
    output          SIO_sout,
    // Ports for Interface apb_cfg_emmc
    input   [31:0]  apb_cfg_emmc_prdata,
    input           apb_cfg_emmc_pready,
    input           apb_cfg_emmc_pslverr,
    output  [31:0]  apb_cfg_emmc_paddr,
    output          apb_cfg_emmc_penable,
    output          apb_cfg_emmc_psel,
    output  [31:0]  apb_cfg_emmc_pwdata,
    output          apb_cfg_emmc_pwrite,
    // Ports for Interface apb_gpio_api
    input   [15:0]  apb_gpio_api_gpio_ext_porta,
    output  [15:0]  apb_gpio_api_gpio_porta_ddr,
    output  [15:0]  apb_gpio_api_gpio_porta_dr,
    // Ports for Interface lt_axi_s
    input   [31:0]  lt_axi_s_araddr,
    input   [1:0]   lt_axi_s_arburst,
    input   [3:0]   lt_axi_s_arcache,
    input   [3:0]   lt_axi_s_arid,
    input   [7:0]   lt_axi_s_arlen,
    input           lt_axi_s_arlock,
    input   [2:0]   lt_axi_s_arprot,
    input   [2:0]   lt_axi_s_arsize,
    input           lt_axi_s_arvalid,
    input   [31:0]  lt_axi_s_awaddr,
    input   [1:0]   lt_axi_s_awburst,
    input   [3:0]   lt_axi_s_awcache,
    input   [3:0]   lt_axi_s_awid,
    input   [7:0]   lt_axi_s_awlen,
    input           lt_axi_s_awlock,
    input   [2:0]   lt_axi_s_awprot,
    input   [2:0]   lt_axi_s_awsize,
    input           lt_axi_s_awvalid,
    input           lt_axi_s_bready,
    input           lt_axi_s_rready,
    input   [63:0]  lt_axi_s_wdata,
    input           lt_axi_s_wlast,
    input   [7:0]   lt_axi_s_wstrb,
    input           lt_axi_s_wvalid,
    output          lt_axi_s_arready,
    output          lt_axi_s_awready,
    output  [3:0]   lt_axi_s_bid,
    output  [1:0]   lt_axi_s_bresp,
    output          lt_axi_s_bvalid,
    output  [63:0]  lt_axi_s_rdata,
    output  [3:0]   lt_axi_s_rid,
    output          lt_axi_s_rlast,
    output  [1:0]   lt_axi_s_rresp,
    output          lt_axi_s_rvalid,
    output          lt_axi_s_wready,
    // Ports for Interface slave0_soc_periph_dw_axi_ACLK
    input           slave0_soc_periph_dw_axi_ACLK_aclk,
    // Ports for Interface slave0_soc_periph_dw_axi_ARESETn
    input           slave0_soc_periph_dw_axi_ARESETn_aresetn,
    // Ports for Manually exported pins
    input           soc_periph_dw_gpio_pclk_intr,
    input           soc_periph_dw_i2c_0_ic_clk,
    input           soc_periph_dw_i2c_0_ic_clk_in_a,
    input           soc_periph_dw_i2c_0_ic_data_in_a,
    input           soc_periph_dw_i2c_0_ic_rst_n,
    input           soc_periph_dw_i2c_1_ic_clk,
    input           soc_periph_dw_i2c_1_ic_clk_in_a,
    input           soc_periph_dw_i2c_1_ic_data_in_a,
    input           soc_periph_dw_i2c_1_ic_rst_n,
    input   [3:0]   soc_periph_dw_ssi_rxd,
    input           soc_periph_dw_ssi_ss_in_n,
    input           soc_periph_dw_ssi_ssi_clk,
    input           soc_periph_dw_ssi_ssi_rst_n,
    input           soc_periph_dw_timers_scan_mode,
    input           soc_periph_dw_timers_timer_1_clk,
    input           soc_periph_dw_timers_timer_1_resetn,
    input           soc_periph_dw_timers_timer_2_clk,
    input           soc_periph_dw_timers_timer_2_resetn,
    input           soc_periph_dw_uart_dcd_n,
    input           soc_periph_dw_uart_dsr_n,
    input           soc_periph_dw_uart_ri_n,
    input   [9:0]   soc_periph_dw_uart_rx_ram_out,
    input           soc_periph_dw_uart_scan_mode,
    input   [7:0]   soc_periph_dw_uart_tx_ram_out,
    output          soc_periph_dw_gpio_gpio_intr_flag,
    output          soc_periph_dw_gpio_gpio_intrclk_en,
    output          soc_periph_dw_i2c_0_ic_activity_intr,
    output          soc_periph_dw_i2c_0_ic_clk_oe,
    output          soc_periph_dw_i2c_0_ic_data_oe,
    output          soc_periph_dw_i2c_0_ic_gen_call_intr,
    output          soc_periph_dw_i2c_0_ic_rd_req_intr,
    output          soc_periph_dw_i2c_0_ic_rx_done_intr,
    output          soc_periph_dw_i2c_0_ic_rx_full_intr,
    output          soc_periph_dw_i2c_0_ic_rx_over_intr,
    output          soc_periph_dw_i2c_0_ic_rx_under_intr,
    output          soc_periph_dw_i2c_0_ic_scl_stuck_at_low_intr,
    output          soc_periph_dw_i2c_0_ic_smbus_clk_mext_intr,
    output          soc_periph_dw_i2c_0_ic_smbus_clk_sext_intr,
    output          soc_periph_dw_i2c_0_ic_smbus_host_notify_intr,
    output          soc_periph_dw_i2c_0_ic_smbus_quick_cmd_det_intr,
    output          soc_periph_dw_i2c_0_ic_start_det_intr,
    output          soc_periph_dw_i2c_0_ic_stop_det_intr,
    output          soc_periph_dw_i2c_0_ic_tx_abrt_intr,
    output          soc_periph_dw_i2c_0_ic_tx_empty_intr,
    output          soc_periph_dw_i2c_0_ic_tx_over_intr,
    output          soc_periph_dw_i2c_1_ic_activity_intr,
    output          soc_periph_dw_i2c_1_ic_clk_oe,
    output          soc_periph_dw_i2c_1_ic_data_oe,
    output          soc_periph_dw_i2c_1_ic_gen_call_intr,
    output          soc_periph_dw_i2c_1_ic_rd_req_intr,
    output          soc_periph_dw_i2c_1_ic_rx_done_intr,
    output          soc_periph_dw_i2c_1_ic_rx_full_intr,
    output          soc_periph_dw_i2c_1_ic_rx_over_intr,
    output          soc_periph_dw_i2c_1_ic_rx_under_intr,
    output          soc_periph_dw_i2c_1_ic_scl_stuck_at_low_intr,
    output          soc_periph_dw_i2c_1_ic_smbus_clk_mext_intr,
    output          soc_periph_dw_i2c_1_ic_smbus_clk_sext_intr,
    output          soc_periph_dw_i2c_1_ic_smbus_host_notify_intr,
    output          soc_periph_dw_i2c_1_ic_smbus_quick_cmd_det_intr,
    output          soc_periph_dw_i2c_1_ic_start_det_intr,
    output          soc_periph_dw_i2c_1_ic_stop_det_intr,
    output          soc_periph_dw_i2c_1_ic_tx_abrt_intr,
    output          soc_periph_dw_i2c_1_ic_tx_empty_intr,
    output          soc_periph_dw_i2c_1_ic_tx_over_intr,
    output          soc_periph_dw_ssi_sclk_out,
    output  [1:0]   soc_periph_dw_ssi_spi_mode,
    output          soc_periph_dw_ssi_ss_0_n,
    output          soc_periph_dw_ssi_ss_1_n,
    output          soc_periph_dw_ssi_ss_2_n,
    output          soc_periph_dw_ssi_ss_3_n,
    output          soc_periph_dw_ssi_ssi_mst_intr,
    output  [3:0]   soc_periph_dw_ssi_ssi_oe_n,
    output          soc_periph_dw_ssi_ssi_rxf_intr,
    output          soc_periph_dw_ssi_ssi_rxo_intr,
    output          soc_periph_dw_ssi_ssi_rxu_intr,
    output          soc_periph_dw_ssi_ssi_txe_intr,
    output          soc_periph_dw_ssi_ssi_txo_intr,
    output  [3:0]   soc_periph_dw_ssi_txd,
    output  [1:0]   soc_periph_dw_timers_timer_en,
    output  [1:0]   soc_periph_dw_timers_timer_intr,
    output          soc_periph_dw_uart_intr,
    output  [9:0]   soc_periph_dw_uart_rx_ram_in,
    output  [3:0]   soc_periph_dw_uart_rx_ram_rd_addr,
    output          soc_periph_dw_uart_rx_ram_rd_ce_n,
    output          soc_periph_dw_uart_rx_ram_re_n,
    output          soc_periph_dw_uart_rx_ram_we_n,
    output  [3:0]   soc_periph_dw_uart_rx_ram_wr_addr,
    output  [7:0]   soc_periph_dw_uart_tx_ram_in,
    output  [3:0]   soc_periph_dw_uart_tx_ram_rd_addr,
    output          soc_periph_dw_uart_tx_ram_rd_ce_n,
    output          soc_periph_dw_uart_tx_ram_re_n,
    output          soc_periph_dw_uart_tx_ram_we_n,
    output  [3:0]   soc_periph_dw_uart_tx_ram_wr_addr
);

   wire [31:0]  soc_periph_dw_axi_paddr;
   wire         soc_periph_dw_axi_penable;
   wire         soc_periph_dw_axi_psel_s0;
   wire         soc_periph_dw_axi_psel_s1;
   wire         soc_periph_dw_axi_psel_s2;
   wire         soc_periph_dw_axi_psel_s3;
   wire         soc_periph_dw_axi_psel_s4;
   wire         soc_periph_dw_axi_psel_s5;
   wire [31:0]  soc_periph_dw_axi_pwdata;
   wire         soc_periph_dw_axi_pwrite;
   wire [31:0]  soc_periph_dw_gpio_prdata;
   wire [31:0]  soc_periph_dw_i2c_0_prdata;
   wire [31:0]  soc_periph_dw_i2c_1_prdata;
   wire [31:0]  soc_periph_dw_ssi_prdata;
   wire [31:0]  soc_periph_dw_timers_prdata;
   wire [31:0]  soc_periph_dw_uart_prdata;

   soc_periph_dw_axi_DW_axi_x2p soc_periph_dw_axi
      (.rdata      (lt_axi_s_rdata),
       .bresp      (lt_axi_s_bresp),
       .rresp      (lt_axi_s_rresp),
       .bid        (lt_axi_s_bid),
       .rid        (lt_axi_s_rid),
       .awready    (lt_axi_s_awready),
       .wready     (lt_axi_s_wready),
       .bvalid     (lt_axi_s_bvalid),
       .arready    (lt_axi_s_arready),
       .rlast      (lt_axi_s_rlast),
       .rvalid     (lt_axi_s_rvalid),
       .psel_s0    (soc_periph_dw_axi_psel_s0),
       .psel_s1    (soc_periph_dw_axi_psel_s1),
       .psel_s2    (soc_periph_dw_axi_psel_s2),
       .psel_s3    (soc_periph_dw_axi_psel_s3),
       .psel_s4    (soc_periph_dw_axi_psel_s4),
       .psel_s5    (soc_periph_dw_axi_psel_s5),
       .psel_s6    (apb_cfg_emmc_psel),
       .paddr      (soc_periph_dw_axi_paddr),
       .penable    (soc_periph_dw_axi_penable),
       .pwdata     (soc_periph_dw_axi_pwdata),
       .pwrite     (soc_periph_dw_axi_pwrite),
       .aclk       (slave0_soc_periph_dw_axi_ACLK_aclk),
       .pclk       (PCLK_pclk),
       .aresetn    (slave0_soc_periph_dw_axi_ARESETn_aresetn),
       .awaddr     (lt_axi_s_awaddr),
       .wdata      (lt_axi_s_wdata),
       .araddr     (lt_axi_s_araddr),
       .awvalid    (lt_axi_s_awvalid),
       .arvalid    (lt_axi_s_arvalid),
       .wlast      (lt_axi_s_wlast),
       .wvalid     (lt_axi_s_wvalid),
       .bready     (lt_axi_s_bready),
       .rready     (lt_axi_s_rready),
       .awburst    (lt_axi_s_awburst),
       .awlock     (lt_axi_s_awlock),
       .arburst    (lt_axi_s_arburst),
       .arlock     (lt_axi_s_arlock),
       .awsize     (lt_axi_s_awsize),
       .awprot     (lt_axi_s_awprot),
       .arsize     (lt_axi_s_arsize),
       .arprot     (lt_axi_s_arprot),
       .awid       (lt_axi_s_awid),
       .awlen      (lt_axi_s_awlen),
       .awcache    (lt_axi_s_awcache),
       .wstrb      (lt_axi_s_wstrb),
       .arid       (lt_axi_s_arid),
       .arlen      (lt_axi_s_arlen),
       .arcache    (lt_axi_s_arcache),
       .presetn    (PRESETn_presetn),
       .prdata_s0  (soc_periph_dw_gpio_prdata),
       .prdata_s1  (soc_periph_dw_i2c_0_prdata),
       .prdata_s2  (soc_periph_dw_ssi_prdata),
       .prdata_s3  (soc_periph_dw_i2c_1_prdata),
       .prdata_s4  (soc_periph_dw_uart_prdata),
       .prdata_s5  (soc_periph_dw_timers_prdata),
       .pready_s6  (apb_cfg_emmc_pready),
       .prdata_s6  (apb_cfg_emmc_prdata),
       .pslverr_s6 (apb_cfg_emmc_pslverr));

   soc_periph_dw_gpio_DW_apb_gpio soc_periph_dw_gpio
      (.pclk            (PCLK_pclk),
       .pclk_intr       (soc_periph_dw_gpio_pclk_intr),
       .presetn         (PRESETn_presetn),
       .penable         (soc_periph_dw_axi_penable),
       .pwrite          (soc_periph_dw_axi_pwrite),
       .pwdata          (soc_periph_dw_axi_pwdata),
       .paddr           (soc_periph_dw_axi_paddr[6:0]),
       .psel            (soc_periph_dw_axi_psel_s0),
       .gpio_ext_porta  (apb_gpio_api_gpio_ext_porta),
       .gpio_porta_dr   (apb_gpio_api_gpio_porta_dr),
       .gpio_porta_ddr  (apb_gpio_api_gpio_porta_ddr),
       .gpio_intr_flag  (soc_periph_dw_gpio_gpio_intr_flag),
       .gpio_intrclk_en (soc_periph_dw_gpio_gpio_intrclk_en),
       .prdata          (soc_periph_dw_gpio_prdata));

   soc_periph_dw_i2c_0_DW_apb_i2c soc_periph_dw_i2c_0
      (.ic_start_det_intr           (soc_periph_dw_i2c_0_ic_start_det_intr),
       .ic_stop_det_intr            (soc_periph_dw_i2c_0_ic_stop_det_intr),
       .ic_scl_stuck_at_low_intr    (soc_periph_dw_i2c_0_ic_scl_stuck_at_low_intr),
       .ic_smbus_clk_sext_intr      (soc_periph_dw_i2c_0_ic_smbus_clk_sext_intr),
       .ic_smbus_clk_mext_intr      (soc_periph_dw_i2c_0_ic_smbus_clk_mext_intr),
       .ic_smbus_quick_cmd_det_intr (soc_periph_dw_i2c_0_ic_smbus_quick_cmd_det_intr),
       .ic_smbus_host_notify_intr   (soc_periph_dw_i2c_0_ic_smbus_host_notify_intr),
       .ic_activity_intr            (soc_periph_dw_i2c_0_ic_activity_intr),
       .ic_rx_done_intr             (soc_periph_dw_i2c_0_ic_rx_done_intr),
       .ic_tx_abrt_intr             (soc_periph_dw_i2c_0_ic_tx_abrt_intr),
       .ic_rd_req_intr              (soc_periph_dw_i2c_0_ic_rd_req_intr),
       .ic_tx_empty_intr            (soc_periph_dw_i2c_0_ic_tx_empty_intr),
       .ic_tx_over_intr             (soc_periph_dw_i2c_0_ic_tx_over_intr),
       .ic_rx_full_intr             (soc_periph_dw_i2c_0_ic_rx_full_intr),
       .ic_rx_over_intr             (soc_periph_dw_i2c_0_ic_rx_over_intr),
       .ic_rx_under_intr            (soc_periph_dw_i2c_0_ic_rx_under_intr),
       .ic_gen_call_intr            (soc_periph_dw_i2c_0_ic_gen_call_intr),
       .pclk                        (PCLK_pclk),
       .presetn                     (PRESETn_presetn),
       .psel                        (soc_periph_dw_axi_psel_s1),
       .penable                     (soc_periph_dw_axi_penable),
       .pwrite                      (soc_periph_dw_axi_pwrite),
       .paddr                       (soc_periph_dw_axi_paddr[7:0]),
       .pwdata                      (soc_periph_dw_axi_pwdata),
       .prdata                      (soc_periph_dw_i2c_0_prdata),
       .pready                      (),
       .pslverr                     (),
       .pstrb                       (4'hf), // Manually changed due to APB3 fabric into APB4 slave
       .pprot                       (3'b0),
       .ic_clk                      (soc_periph_dw_i2c_0_ic_clk),
       .ic_clk_in_a                 (soc_periph_dw_i2c_0_ic_clk_in_a),
       .ic_data_in_a                (soc_periph_dw_i2c_0_ic_data_in_a),
       .ic_rst_n                    (soc_periph_dw_i2c_0_ic_rst_n),
       .debug_s_gen                 (),
       .debug_p_gen                 (),
       .debug_data                  (),
       .debug_addr                  (),
       .debug_rd                    (),
       .debug_wr                    (),
       .debug_hs                    (),
       .debug_master_act            (),
       .debug_slave_act             (),
       .debug_addr_10bit            (),
       .debug_mst_cstate            (),
       .debug_slv_cstate            (),
       .ic_clk_oe                   (soc_periph_dw_i2c_0_ic_clk_oe),
       .ic_data_oe                  (soc_periph_dw_i2c_0_ic_data_oe),
       .ic_en                       ());

   soc_periph_dw_i2c_1_DW_apb_i2c soc_periph_dw_i2c_1
      (.ic_start_det_intr           (soc_periph_dw_i2c_1_ic_start_det_intr),
       .ic_stop_det_intr            (soc_periph_dw_i2c_1_ic_stop_det_intr),
       .ic_scl_stuck_at_low_intr    (soc_periph_dw_i2c_1_ic_scl_stuck_at_low_intr),
       .ic_smbus_clk_sext_intr      (soc_periph_dw_i2c_1_ic_smbus_clk_sext_intr),
       .ic_smbus_clk_mext_intr      (soc_periph_dw_i2c_1_ic_smbus_clk_mext_intr),
       .ic_smbus_quick_cmd_det_intr (soc_periph_dw_i2c_1_ic_smbus_quick_cmd_det_intr),
       .ic_smbus_host_notify_intr   (soc_periph_dw_i2c_1_ic_smbus_host_notify_intr),
       .ic_activity_intr            (soc_periph_dw_i2c_1_ic_activity_intr),
       .ic_rx_done_intr             (soc_periph_dw_i2c_1_ic_rx_done_intr),
       .ic_tx_abrt_intr             (soc_periph_dw_i2c_1_ic_tx_abrt_intr),
       .ic_rd_req_intr              (soc_periph_dw_i2c_1_ic_rd_req_intr),
       .ic_tx_empty_intr            (soc_periph_dw_i2c_1_ic_tx_empty_intr),
       .ic_tx_over_intr             (soc_periph_dw_i2c_1_ic_tx_over_intr),
       .ic_rx_full_intr             (soc_periph_dw_i2c_1_ic_rx_full_intr),
       .ic_rx_over_intr             (soc_periph_dw_i2c_1_ic_rx_over_intr),
       .ic_rx_under_intr            (soc_periph_dw_i2c_1_ic_rx_under_intr),
       .ic_gen_call_intr            (soc_periph_dw_i2c_1_ic_gen_call_intr),
       .pclk                        (PCLK_pclk),
       .presetn                     (PRESETn_presetn),
       .psel                        (soc_periph_dw_axi_psel_s3),
       .penable                     (soc_periph_dw_axi_penable),
       .pwrite                      (soc_periph_dw_axi_pwrite),
       .paddr                       (soc_periph_dw_axi_paddr[7:0]),
       .pwdata                      (soc_periph_dw_axi_pwdata),
       .prdata                      (soc_periph_dw_i2c_1_prdata),
       .pready                      (),
       .pslverr                     (),
       .pstrb                       (4'hf), // Manually changed due to APB3 fabric into APB4 slave
       .pprot                       (3'b0),
       .ic_clk                      (soc_periph_dw_i2c_1_ic_clk),
       .ic_clk_in_a                 (soc_periph_dw_i2c_1_ic_clk_in_a),
       .ic_data_in_a                (soc_periph_dw_i2c_1_ic_data_in_a),
       .ic_rst_n                    (soc_periph_dw_i2c_1_ic_rst_n),
       .debug_s_gen                 (),
       .debug_p_gen                 (),
       .debug_data                  (),
       .debug_addr                  (),
       .debug_rd                    (),
       .debug_wr                    (),
       .debug_hs                    (),
       .debug_master_act            (),
       .debug_slave_act             (),
       .debug_addr_10bit            (),
       .debug_mst_cstate            (),
       .debug_slv_cstate            (),
       .ic_clk_oe                   (soc_periph_dw_i2c_1_ic_clk_oe),
       .ic_data_oe                  (soc_periph_dw_i2c_1_ic_data_oe),
       .ic_en                       ());

   soc_periph_dw_ssi_DW_apb_ssi soc_periph_dw_ssi
      (.pclk         (PCLK_pclk),
       .presetn      (PRESETn_presetn),
       .psel         (soc_periph_dw_axi_psel_s2),
       .penable      (soc_periph_dw_axi_penable),
       .pwrite       (soc_periph_dw_axi_pwrite),
       .paddr        (soc_periph_dw_axi_paddr[7:0]),
       .pwdata       (soc_periph_dw_axi_pwdata),
       .rxd          (soc_periph_dw_ssi_rxd),
       .ss_in_n      (soc_periph_dw_ssi_ss_in_n),
       .ssi_clk      (soc_periph_dw_ssi_ssi_clk),
       .ssi_rst_n    (soc_periph_dw_ssi_ssi_rst_n),
       .pready       (),
       .pslverr      (),
       .pstrb        (4'hf), // Manually changed due to APB3 fabric into APB4 slave
       .pprot        (3'b0),
       .prdata       (soc_periph_dw_ssi_prdata),
       .ssi_sleep    (),
       .ssi_busy     (),
       .txd          (soc_periph_dw_ssi_txd),
       .sclk_out     (soc_periph_dw_ssi_sclk_out),
       .ss_0_n       (soc_periph_dw_ssi_ss_0_n),
       .ss_1_n       (soc_periph_dw_ssi_ss_1_n),
       .ss_2_n       (soc_periph_dw_ssi_ss_2_n),
       .ss_3_n       (soc_periph_dw_ssi_ss_3_n),
       .ssi_oe_n     (soc_periph_dw_ssi_ssi_oe_n),
       .spi_mode     (soc_periph_dw_ssi_spi_mode),
       .ssi_txe_intr (soc_periph_dw_ssi_ssi_txe_intr),
       .ssi_txo_intr (soc_periph_dw_ssi_ssi_txo_intr),
       .ssi_rxf_intr (soc_periph_dw_ssi_ssi_rxf_intr),
       .ssi_rxo_intr (soc_periph_dw_ssi_ssi_rxo_intr),
       .ssi_rxu_intr (soc_periph_dw_ssi_ssi_rxu_intr),
       .ssi_mst_intr (soc_periph_dw_ssi_ssi_mst_intr));

   soc_periph_dw_timers_DW_apb_timers soc_periph_dw_timers
      (.pclk           (PCLK_pclk),
       .presetn        (PRESETn_presetn),
       .penable        (soc_periph_dw_axi_penable),
       .psel           (soc_periph_dw_axi_psel_s5),
       .pwrite         (soc_periph_dw_axi_pwrite),
       .paddr          (soc_periph_dw_axi_paddr[7:0]),
       .pwdata         (soc_periph_dw_axi_pwdata),
       .pprot          (3'b0),
       .pstrb          (4'hf), // Manually changed due to APB3 fabric into APB4 slave
       .scan_mode      (soc_periph_dw_timers_scan_mode),
       .timer_1_clk    (soc_periph_dw_timers_timer_1_clk),
       .timer_2_clk    (soc_periph_dw_timers_timer_2_clk),
       .timer_1_resetn (soc_periph_dw_timers_timer_1_resetn),
       .timer_2_resetn (soc_periph_dw_timers_timer_2_resetn),
       .timer_en       (soc_periph_dw_timers_timer_en),
       .timer_intr     (soc_periph_dw_timers_timer_intr),
       .pready         (),
       .pslverr        (),
       .prdata         (soc_periph_dw_timers_prdata));

   soc_periph_dw_uart_DW_apb_uart soc_periph_dw_uart
      (.pclk           (PCLK_pclk),
       .presetn        (PRESETn_presetn),
       .penable        (soc_periph_dw_axi_penable),
       .pwrite         (soc_periph_dw_axi_pwrite),
       .pwdata         (soc_periph_dw_axi_pwdata),
       .paddr          (soc_periph_dw_axi_paddr[7:0]),
       .psel           (soc_periph_dw_axi_psel_s4),
       .pprot          (3'b0),
       .pstrb          (4'hf), // Manually changed due to APB3 fabric into APB4 slave
       .scan_mode      (soc_periph_dw_uart_scan_mode),
       .tx_ram_out     (soc_periph_dw_uart_tx_ram_out),
       .rx_ram_out     (soc_periph_dw_uart_rx_ram_out),
       .cts_n          (SIO_cts_n),
       .dsr_n          (soc_periph_dw_uart_dsr_n),
       .dcd_n          (soc_periph_dw_uart_dcd_n),
       .ri_n           (soc_periph_dw_uart_ri_n),
       .sin            (SIO_sin),
       .prdata         (soc_periph_dw_uart_prdata),
       .pready         (),
       .pslverr        (),
       .tx_ram_in      (soc_periph_dw_uart_tx_ram_in),
       .tx_ram_rd_addr (soc_periph_dw_uart_tx_ram_rd_addr),
       .tx_ram_wr_addr (soc_periph_dw_uart_tx_ram_wr_addr),
       .tx_ram_we_n    (soc_periph_dw_uart_tx_ram_we_n),
       .tx_ram_re_n    (soc_periph_dw_uart_tx_ram_re_n),
       .tx_ram_rd_ce_n (soc_periph_dw_uart_tx_ram_rd_ce_n),
       .rx_ram_in      (soc_periph_dw_uart_rx_ram_in),
       .rx_ram_rd_addr (soc_periph_dw_uart_rx_ram_rd_addr),
       .rx_ram_wr_addr (soc_periph_dw_uart_rx_ram_wr_addr),
       .rx_ram_we_n    (soc_periph_dw_uart_rx_ram_we_n),
       .rx_ram_re_n    (soc_periph_dw_uart_rx_ram_re_n),
       .rx_ram_rd_ce_n (soc_periph_dw_uart_rx_ram_rd_ce_n),
       .dtr_n          (),
       .rts_n          (SIO_rts_n),
       .out2_n         (),
       .out1_n         (),
       .dma_tx_req_n   (),
       .dma_rx_req_n   (),
       .txrdy_n        (),
       .rxrdy_n        (),
       .sout           (SIO_sout),
       .baudout_n      (),
       .intr           (soc_periph_dw_uart_intr));

   assign apb_cfg_emmc_paddr          = soc_periph_dw_axi_paddr;
   assign apb_cfg_emmc_penable        = soc_periph_dw_axi_penable;
   assign apb_cfg_emmc_pwdata         = soc_periph_dw_axi_pwdata;
   assign apb_cfg_emmc_pwrite         = soc_periph_dw_axi_pwrite;


endmodule
