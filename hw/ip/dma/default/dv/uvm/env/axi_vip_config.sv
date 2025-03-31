// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : sultan.khan@axelera.ai       *** //

// *****************************************************************************************
// Description: Class axi_vip_config is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************

//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef GUARD_AXI_VIP_CONFIG_SV
`define GUARD_AXI_VIP_CONFIG_SV
// Class
class axi_vip_config extends svt_axi_system_configuration;

  bit b2b;
  bit [dma_ip_common_pkg::AXI_S_ADDR_WIDTH-1:0]  axi_slave_mem_addr_max;
  
  bit axi_slv_default_rdy;

  // Factory registration
  `uvm_object_utils(axi_vip_config)

  // Class Constructor
  function new(string name = "axi_vip_config");
    super.new(name);

    // --------------------------------------------------------------------------------------------
    // Create Correct Number of AXI Master and Slave Agents (VIPs)
    this.num_masters = 1;                   // DMA_IP : 1 AXI-Slave  Interface  (Register Interface)
    this.num_slaves  = 2;                   // DMA_IP : 2 AXI-Master Interfaces (for DMA Transfers)

    // --------------------------------------------------------------------------------------------
    this.system_monitor_enable = 1;
    this.display_summary_report = 1;
    // svt_axi_system_configuration::display_summary_report

    // --------------------------------------------------------------------------------------------
    // Disable timeout on ready
    this.awready_watchdog_timeout=0;
    // this.wready_watchdog_timeout=100000;
    // this.rready_watchdog_timeout=100000;

    // Disable timeout on axi interface idle
    this.bus_inactivity_timeout = 0;

    // --------------------------------------------------------------------------------------------
    this.allow_slaves_with_overlapping_addr = 1;

    // --------------------------------------------------------------------------------------------
    // Create port configurations
    this.create_sub_cfgs(this.num_masters, this.num_slaves);
	
    // --------------------------------------------------------------------------------------------
    // AXI Master Agent Configuration

    foreach (this.master_cfg[i]) begin
      this.master_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].uvm_reg_enable = 1;
      this.master_cfg[i].data_width = dma_ip_common_pkg::AXI_M_DATA_WIDTH; 
      this.master_cfg[i].addr_width = dma_ip_common_pkg::AXI_M_ADDR_WIDTH; 
      this.master_cfg[i].id_width   = dma_ip_common_pkg::AXI_M_ID_WIDTH;
      this.master_cfg[i].default_bready = 1;
      this.master_cfg[i].default_rready = 1; 
      this.master_cfg[i].is_active = 1;                           // Default : Is_ACTIVE
      this.master_cfg[i].wysiwyg_enable = 1;
      this.master_cfg[i].protocol_checks_enable = 1;
      this.master_cfg[i].transaction_coverage_enable = 1;

      // These to make sure VIP is not driving 'hX/Z during idle
      this.master_cfg[i].write_addr_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].write_data_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].write_resp_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].read_addr_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].read_data_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;

      if($test$plusargs("B2B_ENB")) begin
        b2b = 1'b1;
        `uvm_info("Set-Op: TEST", $sformatf("BACK2BACK Enabled (zero axi-delays) Enabled"), UVM_LOW)
        this.master_cfg[i].num_outstanding_xact   = 10;
      end
			// Other Options Available
      // this.master_cfg[i].exclusive_access_enable = 1;
      // this.master_cfg[i].exclusive_monitor_enable = 1;
      // this.master_cfg[i].max_num_exclusive_access = 0;            // 0 : no restriction of max number of exclusive transactions
      // this.master_cfg[i].reasonable_constraint_mode ( 1'b1 );
    end

    // --------------------------------------------------------------------------------------------
    // AXI Slave Agent Configuration - all with the same configurations
    if($test$plusargs("AXISLV_RDY_BY_DEFAULT")) begin
      axi_slv_default_rdy = 1;
    end
    `uvm_info("AXI_VIP_CONFIG", $sformatf("Default value for AXI_SLV_DEFAULT_RDY=%0d", axi_slv_default_rdy), UVM_LOW)

    foreach (this.slave_cfg[i]) begin
      this.slave_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.slave_cfg[i].data_width = dma_ip_common_pkg::AXI_S_DATA_WIDTH; 
      this.slave_cfg[i].addr_width = dma_ip_common_pkg::AXI_S_ADDR_WIDTH; 
      this.slave_cfg[i].id_width   = dma_ip_common_pkg::AXI_S_ID_WIDTH;
      this.slave_cfg[i].num_outstanding_xact = 10;
      this.slave_cfg[i].protocol_checks_enable = 1;
      this.slave_cfg[i].wysiwyg_enable = 1;
      this.slave_cfg[i].is_active = 1;
      this.slave_cfg[i].default_awready = axi_slv_default_rdy;
      this.slave_cfg[i].default_wready  = axi_slv_default_rdy; 
      this.slave_cfg[i].default_arready = axi_slv_default_rdy;
      this.slave_cfg[i].transaction_coverage_enable = 1;

      // These to make sure VIP is not driving 'hX/Z during idle
      this.slave_cfg[i].write_addr_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].write_data_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].write_resp_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].read_addr_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].read_data_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;

			// Other Options Available
      // this.slave_cfg[i].exclusive_access_enable = 1;
      // this.slave_cfg[i].exclusive_monitor_enable = 1;
      // this.slave_cfg[i].awqos_enable = 1;
      // this.slave_cfg[i].arqos_enable = 1;
    end

    // --------------------------------------------------------------------------------------------

`ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    this.enable_complex_memory_map = 1;
`else
    axi_slave_mem_addr_max = '1;
    `uvm_info("AXI_VIP_CONFIG", $sformatf("AXI SLAVE VIP : SLAVE MEMORY MAX (BYTE) ADDRESS = h%0h", axi_slave_mem_addr_max), UVM_LOW) 

    this.set_addr_range(0, 'h0 , axi_slave_mem_addr_max );    // AXI_Slave 0 Memory (Data-Streo) Address Range
    this.set_addr_range(1, 'h0 , axi_slave_mem_addr_max );    // AXI_Slave 1 Memory (Data-Streo) Address Range
`endif
  endfunction

    // --------------------------------------------------------------------------------------------

endclass
`endif  //GUARD_AXI_VIP_CONFIG_SV
