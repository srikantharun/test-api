`include "soc_periph_dw_timers_DW_apb_timers_all_includes.vh"

module soc_periph_dw_timers_DW_apb_timers (
    pclk,
    presetn,
    penable,
    psel,
    pwrite,
    paddr,
    pwdata,
    pprot,
    pstrb,
    scan_mode,
    timer_1_clk,
    timer_2_clk,
    timer_1_resetn,
    timer_2_resetn,
    timer_en,
    timer_intr,
    pready,
    pslverr,
    prdata
);
  input pclk;
  input presetn;
  input penable;
  input psel;
  input pwrite;
  input [`soc_periph_dw_timers_TIM_ADDR_SLICE_LHS:0] paddr;
  input [`soc_periph_dw_timers_APB_DATA_WIDTH-1:0] pwdata;
  input [2:0] pprot;
  input [`soc_periph_dw_timers_APB_DATA_WIDTH/8-1:0] pstrb;
  input scan_mode;
  input timer_1_clk;
  input timer_1_resetn;
  input timer_2_clk;
  input timer_2_resetn;
  output [`soc_periph_dw_timers_NUM_TIMERS-1:0] timer_en;
  output [`soc_periph_dw_timers_NUM_TIMERS-1:0] timer_intr;
  output pready;
  output pslverr;
  output [`soc_periph_dw_timers_APB_DATA_WIDTH-1:0] prdata;

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  svt_apb_if timers_apb_if ();

  assign timers_apb_if.slave_if[0].pclk = pclk;
  assign timers_apb_if.slave_if[0].presetn = presetn;
  assign timers_apb_if.slave_if[0].psel = psel;
  assign timers_apb_if.slave_if[0].penable = penable;
  assign timers_apb_if.slave_if[0].pwrite = pwrite;
  assign timers_apb_if.slave_if[0].paddr = paddr;
  assign timers_apb_if.slave_if[0].pwdata = pwdata;
  assign timers_apb_if.slave_if[0].pprot = pprot;
  assign timers_apb_if.slave_if[0].pstrb = pstrb;
  assign prdata = timers_apb_if.slave_if[0].prdata;
  assign pslverr = timers_apb_if.slave_if[0].pslverr;
  assign pready = timers_apb_if.slave_if[0].pready;

  svt_apb_system_configuration timers_apb_env_cfg;

  initial begin
    timers_apb_env_cfg = new("timers_apb_env_cfg");
    timers_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_8;
    timers_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    timers_apb_env_cfg.apb4_enable = 0;
    timers_apb_env_cfg.apb3_enable = 0;
    timers_apb_env_cfg.create_sub_cfgs(1);
    timers_apb_env_cfg.slave_addr_ranges = new[1];
    timers_apb_env_cfg.slave_cfg[0].is_active = 1;
    timers_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    timers_apb_env_cfg.slave_cfg[0].default_pready = 1;
    timers_apb_env_cfg.slave_cfg[0].slave_id = 0;
    timers_apb_env_cfg.slave_addr_ranges[0] = new("timers_addr_range");
    timers_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    timers_apb_env_cfg.slave_addr_ranges[0].end_addr = 'hff;
    timers_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_timers_apb_system_env", "cfg", timers_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_timers_apb_system_env",
                                            "vif", timers_apb_if);
  end
endmodule
