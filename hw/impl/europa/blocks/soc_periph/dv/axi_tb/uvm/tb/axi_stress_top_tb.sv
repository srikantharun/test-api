
module axi_stress_top_tb;

  timeunit 1ns; timeprecision 1ps;

  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  import axi_stress_top_pkg::*;
  import axi_stress_top_test_pkg::*;

  axi_stress_top_config axi_stress_top_env_config;
  svt_axi_system_configuration axi_env_cfg;

  // test harness
  axi_stress_top_th th ();

  initial begin
    const int data_width = 64;
    const int addr_width = 40;
    const int id_width = 4;
    automatic int tx_count, nb_threads;
    automatic bit [63:0] addr;

    axi_stress_top_env_config = new("axi_stress_top_env_config");

    // AXI Master VIP config
    axi_env_cfg = new("axi_env_cfg");
    axi_env_cfg.manage_objections_enable = 0;  // Prevent VIP from raising objections
    axi_env_cfg.num_masters = 1;
    axi_env_cfg.num_slaves = 0;
    axi_env_cfg.create_sub_cfgs(1, 0);

    // Master config
    axi_env_cfg.master_cfg[0].silent_mode = 1;
    axi_env_cfg.master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI3;
    axi_env_cfg.master_cfg[0].data_width = data_width;
    axi_env_cfg.master_cfg[0].addr_width = addr_width;
    axi_env_cfg.master_cfg[0].id_width = id_width;
    axi_env_cfg.master_cfg[0].is_active = 1;
    axi_env_cfg.master_cfg[0].wysiwyg_enable = 1;
    axi_env_cfg.master_cfg[0].protocol_checks_enable = 1;
    axi_env_cfg.master_cfg[0].transaction_coverage_enable = 0;
    axi_env_cfg.master_cfg[0].exclusive_access_enable = 1;
    axi_env_cfg.master_cfg[0].exclusive_monitor_enable = 0;
    axi_env_cfg.master_cfg[0].use_separate_rd_wr_chan_id_width = 0;
    axi_env_cfg.master_cfg[0].read_interleaving_disabled = 1;
    axi_env_cfg.master_cfg[0].ignore_wstrb_check_for_wysiwyg_format = 1;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.master_cfg[0].write_chan_id_width = id_width;
    axi_env_cfg.master_cfg[0].read_chan_id_width = id_width;

    axi_stress_top_env_config.axi_vif = th.axi_if;

    axi_stress_top_env_config.m_axi_env_cfg = axi_env_cfg;

    if ($value$plusargs("TX_COUNT=%0d", tx_count)) begin
      axi_stress_top_env_config.m_transaction_count = tx_count;
    end

    if ($value$plusargs("NB_THREADS=%0d", nb_threads)) begin
      axi_stress_top_env_config.m_nb_threads_per_periph = nb_threads;
    end

    uvm_config_db#(axi_stress_top_config)::set(null, "uvm_test_top", "config",
                                               axi_stress_top_env_config);
    uvm_config_db#(axi_stress_top_config)::set(null, "uvm_test_top.m_env", "config",
                                               axi_stress_top_env_config);

    // Configure all apb slaves to use the svt_apb_slave_memory_sequence
    uvm_config_db#(uvm_object_wrapper)::set(
        null, "uvm_test_top.m_env.*apb_system_env.slave*.sequencer.run_phase", "default_sequence",
        svt_apb_slave_memory_sequence::type_id::get());
    run_test();
  end

endmodule
