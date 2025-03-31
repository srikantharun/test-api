`define AXI_VIP
// SPM UVM package
package spm_uvm_pkg;

    timeunit      1ns;
    timeprecision 1ns;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;

    typedef struct {
        // Types
        int  spm_axi_data_width;
        int  spm_axi_strb_width;
        int  spm_axi_addr_width;
        int  spm_axi_id_width;
        int  spm_axi_atop_width;
        // Memory stuff
        int  spm_mem_size_kb;
        int  spm_mem_macro_depth_k;
        int  spm_nb_banks;
        int  spm_nb_sub_banks;
        int  spm_nb_mini_banks;
        int  spm_nb_srams_per_mini_bank;
        int  spm_nb_req_pipeline;
        int  spm_nb_rsp_pipeline;
        // ECC
        bit  ecc_protection_en;
    } spm_config_t;

   // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.svh"
  `include "axi_virtual_sequencer.svh"
  `include "spm_uvm_scoreboard.svh"
  `include "spm_uvm_monitor.svh"
  `include "spm_env.svh"
  `include "cust_svt_axi_master_transaction.svh"

endpackage
