`include "soc_periph_dw_ssi_DW_apb_ssi_all_includes.vh"

module soc_periph_dw_ssi_DW_apb_ssi (

    //APB Slave I/O Signals                  
    pclk
    , presetn
    , psel
    , penable
    , pwrite
    , paddr
    , pwdata
    , rxd
    , ss_in_n
    , ssi_clk
    , ssi_rst_n
    , pready
    , pslverr
    , pstrb
    , pprot
    , prdata
    , ssi_sleep
    , ssi_busy
    , txd
    , sclk_out
    , ss_0_n
    , ss_1_n
    , ss_2_n
    , ss_3_n
    , ssi_oe_n
    , spi_mode
    , ssi_txe_intr
    , ssi_txo_intr
    , ssi_rxf_intr
    , ssi_rxo_intr
    , ssi_rxu_intr
    , ssi_mst_intr
);

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  svt_apb_if ssi_apb_if ();
  svt_apb_system_configuration ssi_apb_env_cfg;


  // --------------------------------------
  // -- Input and Output Port Declaration
  // --------------------------------------         

  input pclk;  // APB Clock Signal
  input presetn;  // APB async Reset Signal
  input psel;  // APB Peripheral Select Signal
  input penable;  // Strobe Signal
  input pwrite;  // Write Signal
  input [`soc_periph_dw_ssi_APB_ADDR_WIDTH-1:0] paddr;  // Address bus
  input [`soc_periph_dw_ssi_APB_DATA_WIDTH-1:0] pwdata;  // Write data Bus
  input [`soc_periph_dw_ssi_SSI_SPI_MULTIIO-1:0] rxd;  // Receive Data Signal
  input ss_in_n;  // Slave Select Input

  input ssi_clk;  // Peripheral Serial Clock Signal
  input ssi_rst_n;  // Preipheral async Reset Signal

  output [`soc_periph_dw_ssi_APB_DATA_WIDTH-1:0] prdata;  // Read Data Bus

  output pready;  // APB IF ready signal
  output pslverr;  // APB Slave error signal
  input [`soc_periph_dw_ssi_PSTRB_WIDTH-1:0] pstrb;
  //spyglass disable_block W240
  //SMD: Input 'pprot[2:0]' declared but not read.
  //SJ: PPROT signal is not used in current design, signal kept for interface consistency
  input [2:0] pprot;
  //spyglass enable_block W240
  output ssi_sleep;
  output ssi_busy;
  output [`soc_periph_dw_ssi_SSI_SPI_MULTIIO-1:0] txd;  // Transmit Data Signal
  output [`soc_periph_dw_ssi_SSI_SPI_MULTIIO-1:0] ssi_oe_n;  // Output enable Signal


  output ss_0_n;  // Slave Select Output
  output [1:0] spi_mode;  // SPI Frame format signal
  output ss_1_n;  // Slave Select Output
  output ss_2_n;  // Slave Select Output
  output ss_3_n;  // Slave Select Output
  output sclk_out;  // Serial bir-rate clock

  output ssi_txe_intr;  // Transmit FIFO Empty Interrupt
  output ssi_txo_intr;  // Transmit FIFO Overflow Interrput
  output ssi_rxf_intr;  // Recieve FIFO Full Interrupt
  output ssi_rxo_intr;  // Recieve FIFO Overflow Interrupt
  output ssi_rxu_intr;  // Recieve FIFO Underflow Interrupt
  output ssi_mst_intr;  // Multi-Master Contention Interrupt

  assign ssi_apb_if.slave_if[0].pclk = pclk;
  assign ssi_apb_if.slave_if[0].presetn = presetn;
  assign ssi_apb_if.slave_if[0].psel = psel;
  assign ssi_apb_if.slave_if[0].penable = penable;
  assign ssi_apb_if.slave_if[0].pwrite = pwrite;
  assign ssi_apb_if.slave_if[0].paddr = paddr;
  assign ssi_apb_if.slave_if[0].pwdata = pwdata;
  assign ssi_apb_if.slave_if[0].pprot = pprot;
  assign ssi_apb_if.slave_if[0].pstrb = pstrb;
  assign prdata = ssi_apb_if.slave_if[0].prdata;
  assign pslverr = ssi_apb_if.slave_if[0].pslverr;
  assign pready = ssi_apb_if.slave_if[0].pready;

  initial begin
    ssi_apb_env_cfg = new("ssi_apb_env_cfg");
    ssi_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_8;
    ssi_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    ssi_apb_env_cfg.apb4_enable = 0;
    ssi_apb_env_cfg.apb3_enable = 0;
    ssi_apb_env_cfg.create_sub_cfgs(1);
    ssi_apb_env_cfg.slave_addr_ranges = new[1];
    ssi_apb_env_cfg.slave_cfg[0].is_active = 1;
    ssi_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    ssi_apb_env_cfg.slave_cfg[0].default_pready = 1;
    ssi_apb_env_cfg.slave_cfg[0].slave_id = 0;
    ssi_apb_env_cfg.slave_addr_ranges[0] = new("ssi_addr_range");
    ssi_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    ssi_apb_env_cfg.slave_addr_ranges[0].end_addr = 'hff;
    ssi_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_ssi_apb_system_env", "cfg", ssi_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_ssi_apb_system_env", "vif",
                                            ssi_apb_if);
  end

endmodule
