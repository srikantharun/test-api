`include "soc_periph_dw_gpio_DW_apb_gpio_all_includes.vh"

module soc_periph_dw_gpio_DW_apb_gpio (



    pclk,  // APB Clock     
    pclk_intr,  // APB Clock used in detection
    // of edge-sensitive interrupts and
    // in synchronisation of level-sensitive
    // interrupts.
    presetn,  // APB Reset signal (active-low)
    penable,  // APB Enable Control signal
    pwrite,  // APB Write Control signal
    pwdata,  // APB Write Data Bus
    paddr,  // APB Address Bus
    psel,  // APB Peripheral Select
    gpio_ext_porta,  // Input data
    gpio_porta_dr,  // Output Data
    gpio_porta_ddr,  // Data Direction Control
    gpio_intr_flag,  // Combined Interrupt Detect Flag
    gpio_intrclk_en,  // Indicates that pclk_intr must be running
    // to detect interrupts 
    prdata  // APB Read Data Bus

);
  //spyglass enable_block Topology_02
  input pclk;
  input pclk_intr;
  input presetn;
  input penable;
  input pwrite;
  input [`soc_periph_dw_gpio_APB_DATA_WIDTH-1:0] pwdata;
  // Least significant 2 bits of paddr are not required in code as registers
  // are aligned to 32bit address and hence last two bits are always zero.
  // Hence, the bits are ignored and non-driving as part of design.
  input [`soc_periph_dw_gpio_GPIO_ADDR_SLICE_LHS:0] paddr;
  input psel;
  //spyglass disable_block Ac_glitch02
  //SMD: Reports clock domain crossings that are subject to glitches because of a reconverging source
  //SJ: Polarity of gpio_ext_porta is decided by a MUX before passing it to BCM21. There will not be any glitches.
  input [`soc_periph_dw_gpio_GPIO_PWIDTH_A-1:0] gpio_ext_porta;
  //spyglass enable_block Ac_glitch02

  output [`soc_periph_dw_gpio_GPIO_PWIDTH_A-1:0] gpio_porta_dr;
  output [`soc_periph_dw_gpio_GPIO_PWIDTH_A-1:0] gpio_porta_ddr;
  output gpio_intr_flag;
  output gpio_intrclk_en;
  output [`soc_periph_dw_gpio_APB_DATA_WIDTH-1:0] prdata;

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  svt_apb_if gpio_apb_if ();

  assign gpio_apb_if.slave_if[0].pclk = pclk;
  assign gpio_apb_if.slave_if[0].presetn = presetn;
  assign gpio_apb_if.slave_if[0].psel = psel;
  assign gpio_apb_if.slave_if[0].penable = penable;
  assign gpio_apb_if.slave_if[0].pwrite = pwrite;
  assign gpio_apb_if.slave_if[0].paddr = paddr;
  assign gpio_apb_if.slave_if[0].pwdata = pwdata;
  assign prdata = gpio_apb_if.slave_if[0].prdata;

  svt_apb_system_configuration gpio_apb_env_cfg;

  initial begin
    gpio_apb_env_cfg = new("gpio_apb_env_cfg");
    gpio_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_7;
    gpio_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    gpio_apb_env_cfg.apb4_enable = 0;
    gpio_apb_env_cfg.apb3_enable = 0;
    gpio_apb_env_cfg.create_sub_cfgs(1);
    gpio_apb_env_cfg.slave_addr_ranges = new[1];
    gpio_apb_env_cfg.slave_cfg[0].is_active = 1;
    gpio_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    gpio_apb_env_cfg.slave_cfg[0].slave_id = 0;
    gpio_apb_env_cfg.slave_addr_ranges[0] = new("gpio_addr_range");
    gpio_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    gpio_apb_env_cfg.slave_addr_ranges[0].end_addr = 'h7f;
    gpio_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_gpio_apb_system_env", "cfg", gpio_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_gpio_apb_system_env", "vif",
                                            gpio_apb_if);
  end


endmodule
