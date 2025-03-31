`ifndef SOC_PERIPH_AXI_STRESS_TOP_TEST_PKG_SV
`define SOC_PERIPH_AXI_STRESS_TOP_TEST_PKG_SV

package axi_stress_top_test_pkg;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import axi_stress_top_pkg::*;
  import aipu_addr_map_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;
  import axi_stress_top_seq_pkg::*;



  parameter logic [39:0] SOC_PERIPH_ADDRESSES[`NB_PERIPHS][2] = '{
      {SOC_PERIPH_UART_ST_ADDR,  'h100},
      {SOC_PERIPH_GPIO_ST_ADDR,  'h80 },
      {SOC_PERIPH_SPI_ST_ADDR,   'h100},
      {SOC_PERIPH_I2C_0_ST_ADDR, 'h100},
      {SOC_PERIPH_I2C_1_ST_ADDR, 'h100},
      {SOC_PERIPH_EMMC_ST_ADDR,  'h500},
      {SOC_PERIPH_TIMER_ST_ADDR, 'h100}
  };

  `include "axi_stress_top_test.sv"

endpackage : axi_stress_top_test_pkg

`endif  // SOC_PERIPH_AXI_STRESS_TOP_TEST_PKG_SV
