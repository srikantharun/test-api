`ifndef GUARD_SOC_MGMT_MEMORY_MAP_AXI_TEST_SV
`define GUARD_SOC_MGMT_MEMORY_MAP_AXI_TEST_SV
// Extends from AI CORE soc_mgmt base test class
class soc_mgmt_memory_map_axi_test extends soc_mgmt_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(soc_mgmt_memory_map_axi_test)

  bit [36-1:0] axi_addr_intr[$];
  bit [36-1:0] apb_addr_intr[$];

  int  axi_write_addr;
  int  axi_write_data;
  int loop_strt;
  int loop_len;


  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  axi_slave_mem_response_sequence  axi_slave_resp_seq;
  apb_master_directed_sequence apb_wr_rd_seq;
  uvm_status_e   status;

  // soc_mgmt user Inteface Handle
  virtual soc_mgmt_if soc_mgmt_if;

  /** Class Constructor */
  function new(string name = "soc_mgmt_memory_map_axi_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);


    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)

    // random selection of slave response normal or zero delay sequence
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
    axi_slave_resp_seq	= axi_slave_mem_response_sequence::type_id::create("axi_slave_resp_seq");
    apb_wr_rd_seq	= apb_master_directed_sequence::type_id::create("apb_wr_rd_seq");

    // Recieve soc_mgmt user interface handle
    uvm_config_db#(virtual soc_mgmt_if)::get(
        uvm_root::get(), "uvm_test_top", "soc_mgmt_if", soc_mgmt_if);

    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);

    `uvm_info("base_test:run_phase", "Entered...", UVM_LOW)


    if ($value$plusargs ("LOOP_STRT=%d", loop_strt))
      `uvm_info("SOC_MGMT_AXI",$sformatf("value of loop_start is %d",loop_strt ), UVM_LOW)
    else loop_strt=0;

    if ($value$plusargs ("LOOP_LEN=%d", loop_len))
      `uvm_info("SOC_MGMT_AXI",$sformatf("value of loop_len is  %d",loop_len ), UVM_LOW)
    else loop_len=2;

    `uvm_info("SOC_MGMT_AXI",$sformatf("value of loop_start is %0d and loop_len is %d",loop_strt, loop_len ), UVM_LOW)

    // Address and data
    `uvm_info("SOC_MGMT_AXI_LP",$sformatf("Soc mgmt axi lp starting"), UVM_LOW)
    `uvm_info("SOC_MGMT_AXI_LP",$sformatf("Entered into running phase"), UVM_LOW)

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_ROT_KSE_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_ROT_KSE_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_ROT_AO_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_ROT_AO_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_OTP_HOST_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_OTP_HOST_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_TMS_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_TMS_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_RTC_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_RTC_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_WATCHDOG_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_WATCHDOG_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_DEBUG_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_DEBUG_END_ADDR - 8);

    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_MBIST_ST_ADDR);
    axi_addr_intr.push_back(soc_mgmt_common_pkg::SOC_MGMT_MBIST_END_ADDR - 8);

    // NoC is down until o_global_rst_n is set.
    @(posedge soc_mgmt_if.o_global_rst_n);
    `uvm_info("SOC_MGMT_AXI",$sformatf("introducing delay .. "), UVM_LOW)
    #100;
    `uvm_info("SOC_MGMT_AXI",$sformatf("after delay .. "), UVM_LOW)
    for (int i =loop_strt;i<loop_len;i++) begin
      // Randomize the sequence
      axi_wr_seq.randomize() with {
        cfg_addr        == axi_addr_intr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_32BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == 'hFFFF_FFFF;

      };
      axi_wr_seq.start(env.axi_system_env.master[0].sequencer);

      `uvm_info("SOC_MGMT_AXI",$sformatf("write sequence ended for addr %0h",axi_addr_intr[i] ), UVM_LOW)


      axi_rd_seq.randomize() with {
        cfg_addr        == axi_addr_intr[i];
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_32BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
      };
      axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
      `uvm_info("SOC_MGMT_AXI",$sformatf("write and read sequence ended for addr %0h",axi_addr_intr[i] ), UVM_LOW)
    end

    `uvm_info("base_test:run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask

endclass:soc_mgmt_memory_map_axi_test

`endif // GUARD_SOC_MGMT_MEMORY_MAP_AXI_TEST_SV
