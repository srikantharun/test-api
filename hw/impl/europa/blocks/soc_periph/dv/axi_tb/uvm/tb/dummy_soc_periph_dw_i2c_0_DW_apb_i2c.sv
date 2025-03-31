`include "soc_periph_dw_i2c_0_DW_apb_i2c_all_includes.vh"

module soc_periph_dw_i2c_0_DW_apb_i2c (

    ic_start_det_intr,
    ic_stop_det_intr,
    ic_scl_stuck_at_low_intr,
    ic_smbus_clk_sext_intr,
    ic_smbus_clk_mext_intr,
    ic_smbus_quick_cmd_det_intr,
    ic_smbus_host_notify_intr,
    ic_activity_intr,
    ic_rx_done_intr,
    ic_tx_abrt_intr,
    ic_rd_req_intr,
    ic_tx_empty_intr,
    ic_tx_over_intr,
    ic_rx_full_intr,
    ic_rx_over_intr,
    ic_rx_under_intr,
    ic_gen_call_intr,
    //APB Slave I/O Signals
    pclk,
    presetn,
    psel,
    penable,
    pwrite,
    paddr,
    pwdata,
    prdata,
    pready,
    pslverr,
    pstrb,
    pprot,
    ic_clk,
    ic_clk_in_a,
    ic_data_in_a,
    ic_rst_n,
    debug_s_gen,
    debug_p_gen,
    debug_data,
    debug_addr,
    debug_rd,
    debug_wr,
    debug_hs,
    debug_master_act,
    debug_slave_act,
    debug_addr_10bit,
    debug_mst_cstate,
    debug_slv_cstate,
    ic_clk_oe,
    ic_data_oe,
    ic_en
);



  // ------------------------------------------------------
  // -- Port declaration
  // ------------------------------------------------------
  // Inputs

  input pclk;    //# APB Clock Signal, used for the bus interface unit, can be asynchronous to the I2C clocks

  input presetn;  //# APB Reset Signal (active low)

  input psel;    //# APB Peripheral Select Signal: lasts for two pclk cycles; when asserted indicates that the peripheral has been selected for read/write operation
  input penable; //# Strobe Signal: asserted for a single pclk cycle, used for timing read/write operations
  input [2:0] pprot ;  //# Protection Signal: APB4 mode signal indicates protection level of access. This signal is ignored internally in DW_apb_i2c
  input [`soc_periph_dw_i2c_0_APB_DATA_WIDTH/8-1:0] pstrb ;  //# Write Strobes: Each bits on this APB4 mode signal indicates that the corresponding write data-bus byte-lane is active.
  output pready;  //Slave ready: A low  on this APB3 signal stalls an APB transaction until signal goes high.
  output pslverr; //Slave error: A high on this APB3 signal indicates an error condition on the transfer.

  input pwrite;  //# Write Signal: when high indicates a write access to the peripheral; when low indicates a read access

  input [`soc_periph_dw_i2c_0_IC_ADDR_SLICE_LHS:0] paddr; //# Address Bus: uses the lower 7 bits of the address bus for register decode, ignores bits 0 and 1 so that the 8 registers are on 32 bit boundaries

  input [`soc_periph_dw_i2c_0_APB_DATA_WIDTH-1:0] pwdata;  //Write Data Bus: driven by the
  // bus master (bridge unit)
  // during write cycles. Can
  // be 8,16,32 bits wide depending
  // on CoreConsultant parameter APB_DATA_WIDTH

  input ic_rst_n;

  input ic_clk;  //I2C clock, used to clock transfers
                 // in standard, fast and high speed
                 // mode when this module is acting
                 // as master, can be asynchronous to pclk

  input ic_clk_in_a;  //Incoming I2C clock:  Synchronous
                      // to i2c_clk when Master
                      // (except during slave acknowledge
                      // phase).  Asynchronous in when Slave.
                      // Synchronized with meta-stability techniques

  input ic_data_in_a;  // Incoming I2C Data:  Asynchronous



  // OUTPUTS


  //# APB read data bus.
  //# Driven after the 1st APB cycle to align with the passing back of data to the AHB by the APB bridge.
  //# Varies in size and can be 8, 16 or 32-bits wide.
  output [`soc_periph_dw_i2c_0_APB_DATA_WIDTH-1:0] prdata;

  output ic_rx_over_intr;
  output ic_rx_under_intr;
  output ic_tx_over_intr;
  output ic_tx_abrt_intr;
  output ic_rx_done_intr;
  output ic_tx_empty_intr;
  output ic_activity_intr;
  output ic_stop_det_intr;
  output ic_scl_stuck_at_low_intr;

  output ic_smbus_clk_sext_intr;
  output ic_smbus_clk_mext_intr;
  output ic_smbus_quick_cmd_det_intr;
  output ic_smbus_host_notify_intr;

  output ic_start_det_intr;
  output ic_rd_req_intr;
  output ic_rx_full_intr;
  output ic_gen_call_intr;





  output debug_s_gen;
  output debug_p_gen;
  output debug_data;
  output debug_addr;
  output debug_rd;
  output debug_wr;
  output debug_hs;


  //# Outgoing I2C clock: Open drain synchronous with i2c_clk
  output ic_clk_oe;
  //# Outgoing I2C Data: Open Drain. Synchronous to i2c_clk
  output ic_data_oe;
  //# ic_en indicates whether the I2C module is enabled. Some registers can only be programmed when the ic_en is set to 0. 
  //# The FIFO is flushed whenever the module is disabled. There is no need for the ic_clk when the module is disabled.
  output ic_en;
  //# To assist in the debug of any problems that may arise and also to give more visibility into the internals when running on silicon,
  //# some internal states are brought out so that they can be viewed. Very helpful considering the source code is generally encrypted.
  output debug_master_act;
  output debug_slave_act;
  output debug_addr_10bit;
  output [4:0] debug_mst_cstate;
  output [3:0] debug_slv_cstate;

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  svt_apb_if i2c_0_apb_if ();

  assign i2c_0_apb_if.slave_if[0].pclk = pclk;
  assign i2c_0_apb_if.slave_if[0].presetn = presetn;
  assign i2c_0_apb_if.slave_if[0].psel = psel;
  assign i2c_0_apb_if.slave_if[0].penable = penable;
  assign i2c_0_apb_if.slave_if[0].pwrite = pwrite;
  assign i2c_0_apb_if.slave_if[0].paddr = paddr;
  assign i2c_0_apb_if.slave_if[0].pwdata = pwdata;
  assign i2c_0_apb_if.slave_if[0].pprot = pprot;
  assign i2c_0_apb_if.slave_if[0].pstrb = pstrb;
  assign prdata = i2c_0_apb_if.slave_if[0].prdata;
  assign pslverr = i2c_0_apb_if.slave_if[0].pslverr;
  assign pready = i2c_0_apb_if.slave_if[0].pready;

  svt_apb_system_configuration i2c_0_apb_env_cfg;

  initial begin
    i2c_0_apb_env_cfg = new("i2c_0_apb_env_cfg");
    i2c_0_apb_env_cfg.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_8;
    i2c_0_apb_env_cfg.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    i2c_0_apb_env_cfg.apb4_enable = 0;
    i2c_0_apb_env_cfg.apb3_enable = 0;
    i2c_0_apb_env_cfg.create_sub_cfgs(1);
    i2c_0_apb_env_cfg.slave_addr_ranges = new[1];
    i2c_0_apb_env_cfg.slave_cfg[0].is_active = 1;
    i2c_0_apb_env_cfg.slave_cfg[0].mem_enable = 1;
    i2c_0_apb_env_cfg.slave_cfg[0].default_pready = 1;
    i2c_0_apb_env_cfg.slave_cfg[0].slave_id = 0;
    i2c_0_apb_env_cfg.slave_addr_ranges[0] = new("i2c_0_addr_range");
    i2c_0_apb_env_cfg.slave_addr_ranges[0].start_addr = 'h00;
    i2c_0_apb_env_cfg.slave_addr_ranges[0].end_addr = 'hff;
    i2c_0_apb_env_cfg.slave_addr_ranges[0].slave_id = 0;

    uvm_config_db#(svt_apb_system_configuration)::set(
        null, "uvm_test_top.m_env.m_i2c_0_apb_system_env", "cfg", i2c_0_apb_env_cfg);

    uvm_config_db#(virtual svt_apb_if)::set(null, "uvm_test_top.m_env.m_i2c_0_apb_system_env",
                                            "vif", i2c_0_apb_if);
  end


endmodule
