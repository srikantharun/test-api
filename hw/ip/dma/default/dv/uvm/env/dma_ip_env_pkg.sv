package dma_ip_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import dma_pkg::*;

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif

  import dma_ip_common_pkg::*;
  import dma_ip_ral_pkg::*;
  import irq_pkg::*;

//  import dma_ip_func_cov_pkg::*;
//  import dma_ip_assertions_pkg::*;
//  import dma_ip_ref_model_pkg::*;
  import dma_ip_scoreboard_pkg::*;

  // Environment and environment Configurations
  `include "axi_vip_config.sv"
  `include "axi_virtual_sequencer.sv"

  // Environment configuration and environment
  `include "dma_ip_env_config.sv"
  `include "dma_ip_env.sv"

endpackage : dma_ip_env_pkg
