module spike_top_tb;

  timeunit 1ns; timeprecision 1ps;

  `include "uvm_macros.svh"
  `include "memory_preloading_macros.svh"

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_spi_uvm_pkg::*;

  import memory_preloading_pkg::*;

  import spike_seq_pkg::*;
  import spike_top_pkg::*;
  import spike_top_test_pkg::*;


  spike_top_config spike_top_env_config;
  svt_axi_system_configuration axi_env_cfg;
  svt_spi_agent_configuration spi_agent_shared_cfg;

  // test harness
  spike_top_th th ();

  class uart_xactor_wrapper extends uart_xactor_wrapper_abstract;
    `uvm_object_utils(uart_xactor_wrapper)

    function new(string name = "");
      super.new(name);
    endfunction

    task send_char(input bit [7:0] char);
      th.u_uart_xactor.send_char(char);
    endtask

    task receive_char(output bit [7:0] char);
      th.u_uart_xactor.receive_char(char);
    endtask
  endclass

  initial begin
    const int data_width = 64;
    const int addr_width = 40;
    const int id_width = 4;
    automatic uvm_factory factory = uvm_factory::get();

    spike_top_env_config = new("spike_top_env_config");

    // Override abstract UART wrapper
    factory.set_type_override_by_type(uart_xactor_wrapper_abstract::get_type(),
                                      uart_xactor_wrapper::get_type());

    // AXI Master VIP config
    axi_env_cfg = new("axi_env_cfg");
    axi_env_cfg.manage_objections_enable = 0;  // Prevent VIP from raising objections
    axi_env_cfg.num_masters = 2;
    axi_env_cfg.num_slaves = 1;
    axi_env_cfg.create_sub_cfgs(2, 1);

    // SOC_PERIPH config
    axi_env_cfg.master_cfg[0].silent_mode                      = 1;
    axi_env_cfg.master_cfg[0].axi_interface_type               = svt_axi_port_configuration::AXI4;
    axi_env_cfg.master_cfg[0].data_width                       = data_width;
    axi_env_cfg.master_cfg[0].addr_width                       = addr_width;
    axi_env_cfg.master_cfg[0].id_width                         = id_width;
    axi_env_cfg.master_cfg[0].is_active                        = 1;
    axi_env_cfg.master_cfg[0].use_separate_rd_wr_chan_id_width = 0;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.master_cfg[0].write_chan_id_width              = id_width;
    axi_env_cfg.master_cfg[0].read_chan_id_width               = id_width;

    axi_env_cfg.master_cfg[0].wysiwyg_enable                   = 0;
    axi_env_cfg.master_cfg[0].protocol_checks_enable           = 1;
    axi_env_cfg.master_cfg[0].transaction_coverage_enable      = 0;
    axi_env_cfg.master_cfg[0].exclusive_access_enable          = 1;
    axi_env_cfg.master_cfg[0].exclusive_monitor_enable         = 0;

    // Slave VIP connected to EMMC config
    axi_env_cfg.slave_cfg[0].axi_interface_type                = svt_axi_port_configuration::AXI3;
    axi_env_cfg.slave_cfg[0].data_width                        = data_width;
    axi_env_cfg.slave_cfg[0].addr_width                        = addr_width;
    axi_env_cfg.slave_cfg[0].id_width                          = id_width;
    axi_env_cfg.slave_cfg[0].exclusive_access_enable           = 1;
    axi_env_cfg.slave_cfg[0].exclusive_monitor_enable          = 1;
    axi_env_cfg.slave_cfg[0].wysiwyg_enable                    = 0;
    axi_env_cfg.slave_cfg[0].is_active                         = 1;
    axi_env_cfg.slave_cfg[0].default_awready                   = 1;
    axi_env_cfg.slave_cfg[0].default_wready                    = 1;
    axi_env_cfg.slave_cfg[0].default_arready                   = 1;
    axi_env_cfg.slave_cfg[0].default_rready                    = 1;
    axi_env_cfg.slave_cfg[0].use_separate_rd_wr_chan_id_width  = 0;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.slave_cfg[0].write_chan_id_width               = id_width;
    axi_env_cfg.slave_cfg[0].read_chan_id_width                = id_width;


    // SPM config
    axi_env_cfg.master_cfg[1].silent_mode                      = 1;
    axi_env_cfg.master_cfg[1].axi_interface_type               = svt_axi_port_configuration::AXI3;
    axi_env_cfg.master_cfg[1].data_width                       = data_width;
    axi_env_cfg.master_cfg[1].addr_width                       = addr_width;
    axi_env_cfg.master_cfg[1].id_width                         = id_width;
    axi_env_cfg.master_cfg[1].is_active                        = 1;
    axi_env_cfg.master_cfg[1].use_separate_rd_wr_chan_id_width = 0;
    // Somehow these fields must still be set even though use_separate_rd_wr_chan_id_width==0
    axi_env_cfg.master_cfg[1].write_chan_id_width              = id_width;
    axi_env_cfg.master_cfg[1].read_chan_id_width               = id_width;

    axi_env_cfg.master_cfg[1].wysiwyg_enable                   = 0;
    axi_env_cfg.master_cfg[1].protocol_checks_enable           = 1;
    axi_env_cfg.master_cfg[1].transaction_coverage_enable      = 0;
    axi_env_cfg.master_cfg[1].exclusive_access_enable          = 1;
    axi_env_cfg.master_cfg[1].exclusive_monitor_enable         = 0;

    spi_agent_shared_cfg                                       = new("spi_agent_shared_cfg");
    spi_agent_shared_cfg.frame_format                          = svt_spi_types::SPI_STD;
    spi_agent_shared_cfg.spi_feature                           = svt_spi_types::SPI;
    spi_agent_shared_cfg.spi_if                                = th.spi_slave_if;

    spike_top_env_config.axi_vif                               = th.axi_if;
    spike_top_env_config.timer_vif                             = th.tim_if;
    spike_top_env_config.sd_vif                                = th.sd_if;
    spike_top_env_config.uhsii_vif                             = th.uhsii_if;
    spike_top_env_config.i2c0_master_vif                       = th.i2c0_master_if;
    spike_top_env_config.i2c1_master_vif                       = th.i2c1_master_if;
    spike_top_env_config.m_axi_env_cfg                         = axi_env_cfg;
    spike_top_env_config.m_spi_agent_shared_cfg                = spi_agent_shared_cfg;

    // Memfile to preload emmc axi slave memory with
    // Only used in emmc_test
    if (!$value$plusargs("EMMC_SLAVE_MEMFILE=%s", spike_top_env_config.m_emmc_slave_memfile))
      spike_top_env_config.m_emmc_slave_memfile = "";

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

endmodule
