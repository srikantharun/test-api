
`include "soc_periph_dw_uart_DW_apb_uart_all_includes.vh"

module soc_periph_dw_uart_DW_apb_uart (
    // Inputs
    pclk,
    presetn,
    penable,
    pwrite,
    pwdata,
    paddr,
    psel,
    pprot,
    pstrb,
    scan_mode,
    tx_ram_out,
    rx_ram_out,
    cts_n,
    dsr_n,
    dcd_n,
    ri_n,
    sin,
    // Outputs
    prdata,
    pready,
    pslverr,
    tx_ram_in,
    tx_ram_rd_addr,
    tx_ram_wr_addr,
    tx_ram_we_n,
    tx_ram_re_n,
    tx_ram_rd_ce_n,
    rx_ram_in,
    rx_ram_rd_addr,
    rx_ram_wr_addr,
    rx_ram_we_n,
    rx_ram_re_n,
    rx_ram_rd_ce_n,
    dtr_n,
    rts_n,
    out2_n,
    out1_n,
    dma_tx_req_n,
    dma_rx_req_n,
    txrdy_n,
    rxrdy_n,
    sout,
    baudout_n,
    intr
);


  //spyglass enable_block Topology_02
  input pclk;  // APB Clock
  input presetn;  // APB active low
                  // async reset
  input penable;  // strobe signal
  input pwrite;  // write enable
  input [`soc_periph_dw_uart_APB_DATA_WIDTH-1:0] pwdata;  // write data bus
  // paddr[1:0] is used to select byte enable signal.
  // IN APB_DATA_WIDTH=32 configuration, all four bytes of a 32 bit
  // register is enabled. Hence the LSB two bits are not used in this configuration.
  // paddr[0] is used to select lower byte of the 16-bit data word register.
  // IN APB_DATA_WIDTH=16 configuration, always 16-bit words are selected and
  // hence LSB bit of the paadr is not used in this configuration.

  input [`soc_periph_dw_uart_UART_ADDR_SLICE_LHS-1:0] paddr;  // address bus

  input psel;  // APB peripheral
               // select
               // low async reset
  input scan_mode;  // scan mode signal
  input [`soc_periph_dw_uart_TX_RAM_DATA_WIDTH-1:0] tx_ram_out;  // data to TX FIFO
  // RAM
  input [`soc_periph_dw_uart_RX_RAM_DATA_WIDTH-1:0] rx_ram_out;  // data from RX FIFO
  // RAM
  input cts_n;  // clear to send,
                // active low
  input dsr_n;  // data set ready,
                // active low
  input dcd_n;  // data carrier detect,
                // active low
  input ri_n;  // ring indicator,
               // active low
               // active high
               // active low
               // active high
               // active low
  input sin;  // serial in

  input [`soc_periph_dw_uart_APB_DATA_WIDTH/8-1:0] pstrb;  // write strobe
  input [2:0] pprot;  // protection signal

  output                          pready;        //Slave ready: A low on this APB3 signal stalls an APB transaction until signal goes high.
  output                          pslverr;       //Slave error: A high on this APB3 signal indicates an error condition on the transfer.

  output [`soc_periph_dw_uart_APB_DATA_WIDTH-1:0] prdata;  // read data bus

  output [`soc_periph_dw_uart_TX_RAM_DATA_WIDTH-1:0] tx_ram_in;  // data from TX FIFO 
  // RAM

  output [`soc_periph_dw_uart_FIFO_ADDR_WIDTH-1:0] tx_ram_rd_addr;  // read address bus
  // for TX FIFO RAM

  output [`soc_periph_dw_uart_FIFO_ADDR_WIDTH-1:0] tx_ram_wr_addr;  // write address bus
  // for TX FIFO RAM

  output tx_ram_we_n;  // write enable for
                       // TX FIFO RAM,
                       // active low

  output tx_ram_re_n;  // read enable for
                       // TX FIFO RAM,
                       // active low

  output tx_ram_rd_ce_n;  // TX FIFO read port
                          // chip enable for
                          // external ram,
                          // active low

  output [`soc_periph_dw_uart_RX_RAM_DATA_WIDTH-1:0] rx_ram_in;  // data from RX FIFO
  // RAM

  output [`soc_periph_dw_uart_FIFO_ADDR_WIDTH-1:0] rx_ram_rd_addr;  // read address bus
  // for RX FIFO RAM

  output [`soc_periph_dw_uart_FIFO_ADDR_WIDTH-1:0] rx_ram_wr_addr;  // write address bus
  // for RX FIFO RAM

  output rx_ram_we_n;  // write enable for
                       // RX FIFO RAM,
                       // active low

  output rx_ram_re_n;  // read enable for
                       // RX FIFO RAM,
                       // active low

  output rx_ram_rd_ce_n;  // rx FIFO read port
                          // chip enable for
                          // external ram,
                          // active low

  output dtr_n;  // data terminal ready,
                 // active low

  output rts_n;  // request to send,
                 // active low

  output out2_n;  // programmable output2,
                  // active low

  output out1_n;  // programmable output1,
                  // active low

                  // active high

  output dma_tx_req_n;  // TX buffer ready,
                        // active low

                        // active high

                        // active low

                        // active high

  output dma_rx_req_n;  // RX buffer ready,
                        // active low

                        // active high

                        // active low

  output txrdy_n;  // legacy DMA TX
                   // buffer ready,
                   // active low

  output rxrdy_n;  // legacy DMA rx
                   // buffer ready,
                   // active low

  output sout;  // serial out

                // active low



  output baudout_n;  // baud clock reference,
                     // active low


  output intr;  // interrupt

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  svt_apb_if uart_apb_if ();

  assign uart_apb_if.slave_if[0].pclk = pclk;
  assign uart_apb_if.slave_if[0].presetn = presetn;
  assign uart_apb_if.slave_if[0].psel = psel;
  assign uart_apb_if.slave_if[0].penable = penable;
  assign uart_apb_if.slave_if[0].pwrite = pwrite;
  assign uart_apb_if.slave_if[0].paddr = paddr;
  assign uart_apb_if.slave_if[0].pwdata = pwdata;
  assign uart_apb_if.slave_if[0].pprot = pprot;
  assign uart_apb_if.slave_if[0].pstrb = pstrb;
  assign prdata = uart_apb_if.slave_if[0].prdata;
  assign pslverr = uart_apb_if.slave_if[0].pslverr;
  assign pready = uart_apb_if.slave_if[0].pready;

  svt_apb_system_configuration uart_apb_env_cfg;

  initial begin
    uart_apb_env_cfg = new("uart_apb_env_cfg");
    uart_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_8;
    uart_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    uart_apb_env_cfg.apb4_enable = 0;
    uart_apb_env_cfg.apb3_enable = 0;
    uart_apb_env_cfg.create_sub_cfgs(1);
    uart_apb_env_cfg.slave_addr_ranges = new[1];
    uart_apb_env_cfg.slave_cfg[0].is_active = 1;
    uart_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    uart_apb_env_cfg.slave_cfg[0].default_pready = 1;
    uart_apb_env_cfg.slave_cfg[0].slave_id = 0;
    uart_apb_env_cfg.slave_addr_ranges[0] = new("uart_addr_range");
    uart_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    uart_apb_env_cfg.slave_addr_ranges[0].end_addr = 'hff;
    uart_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_uart_apb_system_env", "cfg", uart_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_uart_apb_system_env", "vif",
                                            uart_apb_if);
  end
endmodule
