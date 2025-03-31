// emmc_test
//
// - Start the spike
// - Preload the AXI VIP memory
// - Plug in the EMMC the fake card once the SW is ready
// - Wait for end-of-test
`ifndef SOC_PERIPH_EMMC_TEST_SV
`define SOC_PERIPH_EMMC_TEST_SV

class emmc_test extends spike_top_test;

  `uvm_component_utils(emmc_test)

  sd_slot_cl sd_slot;

  extern function new(string name, uvm_component parent);

  extern task run_phase(uvm_phase phase);
endclass : emmc_test


function emmc_test::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new


task emmc_test::run_phase(uvm_phase phase);
  legacy_config_cl legacy_conf;

  fork
    begin
      super.run_phase(phase);
    end
  join_none

  // Preload emmc slave mem
  if (m_config.m_emmc_slave_memfile == "") begin
    `uvm_fatal(get_type_name(), "No memfile to init axi emmc slave !")
  end
  m_env.m_axi_system_env.slave[0].axi_slave_mem.load_mem(m_config.m_emmc_slave_memfile);

  `uvm_info(get_type_name(), "Waiting for start of test", UVM_LOW)
  uvm_sw_ipc_wait_event(0);

  sd_slot = new("SLOT", "0", null, m_config.sd_vif, m_config.uhsii_vif, null, 0);
  sd_slot.card_events = null;  // deletes the unused mailbox to limit memory usage

  sd_slot.build;
  sd_slot.connect;
  sd_slot.launch;

  #100us;
  legacy_conf = new(EMMC_SECTOR, legacy_config_cl::default_ocr_emmc);
  sd_slot.insert_card(1'b0, 1'b0, legacy_conf, null, "card", 1'b0, -1, -1);  // EMMC card model
  `uvm_info("top_tb", "EMMC memory init completed!", UVM_LOW)
  `uvm_info(get_type_name(), "Starting EMMC VIP!", UVM_LOW)
endtask : run_phase

`endif  // SOC_PERIPH_EMMC_TEST_SV
