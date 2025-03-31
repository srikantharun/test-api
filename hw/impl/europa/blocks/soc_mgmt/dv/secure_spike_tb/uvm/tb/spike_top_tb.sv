module spike_top_tb;

  timeunit 1ns; timeprecision 1ps;

  `include "uvm_macros.svh"
  `include "memory_preloading_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  import memory_preloading_pkg::*;

  import spike_seq_pkg::*;
  import spike_top_pkg::*;
  import spike_top_test_pkg::*;

  spike_top_config spike_top_env_config;
  svt_axi_system_configuration axi_env_cfg;

  // test harness
  spike_top_th th ();

  initial begin
    const int data_width = 64;
    const int addr_width = 40;
    const int id_width = 4;

    spike_top_env_config = new("spike_top_env_config");

    // AXI Master VIP config
    axi_env_cfg = new("axi_env_cfg");
    axi_env_cfg.manage_objections_enable = 0;  // Prevent VIP from raising objections
    axi_env_cfg.num_masters = 2;
    axi_env_cfg.num_slaves = 0;
    axi_env_cfg.create_sub_cfgs(axi_env_cfg.num_masters, axi_env_cfg.num_slaves);

    // Master for ROT
    axi_env_cfg.master_cfg[0].axi_interface_type                = svt_axi_port_configuration::AXI4;
    axi_env_cfg.master_cfg[0].data_width                        = data_width;
    axi_env_cfg.master_cfg[0].addr_width                        = addr_width;
    axi_env_cfg.master_cfg[0].id_width                          = id_width;
    axi_env_cfg.master_cfg[0].is_active                         = 1;
    axi_env_cfg.master_cfg[0].wysiwyg_enable                    = 0;
    axi_env_cfg.master_cfg[0].protocol_checks_enable            = 1;
    axi_env_cfg.master_cfg[0].transaction_coverage_enable       = 0;
    axi_env_cfg.master_cfg[0].exclusive_access_enable           = 1;
    axi_env_cfg.master_cfg[0].exclusive_monitor_enable          = 0;
    axi_env_cfg.master_cfg[0].use_separate_rd_wr_chan_id_width  = 0;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.master_cfg[0].write_chan_id_width               = id_width;
    axi_env_cfg.master_cfg[0].read_chan_id_width                = id_width;

    // Master for SYS SPM config
    axi_env_cfg.master_cfg[1].axi_interface_type                = svt_axi_port_configuration::AXI3;
    axi_env_cfg.master_cfg[1].data_width                        = data_width;
    axi_env_cfg.master_cfg[1].addr_width                        = addr_width;
    axi_env_cfg.master_cfg[1].id_width                          = id_width;
    axi_env_cfg.master_cfg[1].is_active                         = 1;
    axi_env_cfg.master_cfg[1].wysiwyg_enable                    = 0;
    axi_env_cfg.master_cfg[1].protocol_checks_enable            = 1;
    axi_env_cfg.master_cfg[1].transaction_coverage_enable       = 0;
    axi_env_cfg.master_cfg[1].exclusive_access_enable           = 1;
    axi_env_cfg.master_cfg[1].exclusive_monitor_enable          = 0;
    axi_env_cfg.master_cfg[1].use_separate_rd_wr_chan_id_width  = 0;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.master_cfg[1].write_chan_id_width               = id_width;
    axi_env_cfg.master_cfg[1].read_chan_id_width                = id_width;

    spike_top_env_config.axi_vif                          = th.axi_if;
    spike_top_env_config.m_axi_env_cfg                    = axi_env_cfg;

    if (!$value$plusargs("ELF_FILE=%s", spike_top_env_config.m_elf))
      `uvm_fatal("top_tb", "ELF_FILE plusarg is not set !")

    uvm_config_db#(spike_top_config)::set(null, "uvm_test_top", "config", spike_top_env_config);
    uvm_config_db#(spike_top_config)::set(null, "uvm_test_top.m_env", "config",
                                          spike_top_env_config);


    if (!$value$plusargs("ELF_FILE=%s", spike_top_env_config.m_elf))
      `uvm_fatal("top_tb", "ELF_FILE plusarg is not set !")

    fork
      begin
        run_test();
      end
      begin
        string hex_path;
        if (!$value$plusargs("HEX_PATH=%s", hex_path))
          `uvm_fatal("top_tb", "HEX_PATH plusarg is not set !")
        `MEMORY_PRELOADING_FAKE_SYS_SPM_FILE(th.u_dv_axi_ram.mem, hex_path, ~th.rst,
                                             aipu_addr_map_pkg::SYS_SPM_ST_ADDR >> 3)
      end
    join
  end

  //copy ROM code to secure enclave
  initial
    begin   : rom_initl_blk
      string sec_rom;
      if (!$value$plusargs("SEC_ROM_FILE=%s", sec_rom))
        `uvm_fatal("top_th", "SEC_ROM_FILE plusarg is not set !")
      $readmemh(sec_rom, th.u_soc_mgmt_p.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kudelski_kse3_rom.memory_q);
    end
endmodule
