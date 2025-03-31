
`ifndef GUARD_DMA_IP_ENV_CONFIG_SV
`define GUARD_DMA_IP_ENV_CONFIG_SV

// DMA IP environment configuration class
class dma_ip_env_config extends uvm_object;

  `uvm_object_utils(dma_ip_env_config)

  /** Class Constructor */
  function new(string name = "dma_ip_env_config");
    super.new(name);
  endfunction : new

  // Objects handles

//  bit has_coverage   = 0;
//  bit has_scoreboard = 1;

endclass : dma_ip_env_config

`endif  // GUARD_DMA_IP_ENV_CONFIG_SV
