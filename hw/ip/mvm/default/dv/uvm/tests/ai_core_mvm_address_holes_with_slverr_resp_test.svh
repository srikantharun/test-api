`ifndef __AI_CORE_MVM_ADDRESS_HOLES_WITH_SLVERR_RESP_TEST__
`define __AI_CORE_MVM_ADDRESS_HOLES_WITH_SLVERR_RESP_TEST__

// AI Core MVM test to verify the address  holes in register map
class ai_core_mvm_address_holes_with_slverr_resp_test extends ai_core_mvm_base_test;

  // Registration with the factory
  `uvm_component_utils (ai_core_mvm_address_holes_with_slverr_resp_test)
  // Reset sequence
  axi_simple_reset_sequence axi_reset_seq;
  axi_master_write_sequence axi_wr_seq;
  axi_master_read_sequence axi_rd_seq;
  
  // Single write/read sequence
  ral_access_single_write_read_seq wrrd_seq;
  
  // Register list
  uvm_reg reg_list[$];
  uvm_status_e status;
  uvm_status_e expected_status;
  uvm_reg_addr_t avail_address_list[$];
  uvm_reg_addr_t not_avail_address_list[$];
  int success;
  
  
  // Class Constructor
  function new (string name="ai_core_mvm_address_holes_with_slverr_resp_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    // Create simple reset sequence
    axi_reset_seq = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    axi_wr_seq       = axi_master_write_sequence::type_id::create("axi_wr_seq");
    axi_rd_seq       = axi_master_read_sequence::type_id::create("axi_rd_seq");
    wrrd_seq= ral_access_single_write_read_seq::type_id::create("wrrd_seq");
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    // Variables declaration

    phase.raise_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)

    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)
    // Start reset sequence on the sequencer
    if(!axi_reset_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
    axi_reset_seq.start(env.sequencer);

    // Get register list
    mvm_regmodel.get_registers(reg_list);

    //get the addresses available for accessing
    foreach (reg_list[i]) begin
      avail_address_list.push_back(reg_list[i].get_address());
    end
    foreach (avail_address_list[i]) begin
      `uvm_info(get_type_name(), $sformatf("avail_address_list[%0d] = 0x%0x", i, avail_address_list[i]), UVM_HIGH)
    end

    //repeat 20 times the following steps
    repeat (20) begin
      //randomize the list of not_avail_address_list
      success = std::randomize(not_avail_address_list) with {
        not_avail_address_list.size ==  20;
        foreach(not_avail_address_list[i]) {
          foreach(avail_address_list[j]) {
            not_avail_address_list[i] != avail_address_list[j];
          }
          (not_avail_address_list[i] % 8) == 0;
          not_avail_address_list[i] inside {[MVMEXE_CSR_START_ADDR: MVMEXE_CSR_END_ADDR], [MVMPRG_CSR_START_ADDR: MVMPRG_CSR_END_ADDR]};
        }
      } ;
      if(success) begin
        `uvm_info(get_type_name(), $sformatf("Randomization of not_avail_address_list was successful and size is equal to %0d", not_avail_address_list.size), UVM_HIGH)
      end
      else begin
        `uvm_error(get_type_name(), $sformatf("Randomization of not_avail_address_list was unsuccessful"))
      end
      foreach (not_avail_address_list[i]) begin
        `uvm_info(get_type_name(), $sformatf("not_avail_address_list[%0d] = 0x%0x", i, not_avail_address_list[i]), UVM_HIGH)
      end

      //go through every address and request a write and a read. The answer shall be always the same (SLVERR)
      foreach (not_avail_address_list[i]) begin
        //write register
        `uvm_info("MVM_REG",$sformatf("MVM axi reg starting for register 0x%0x", not_avail_address_list[i]), UVM_LOW)
        // Randomize the sequence
        if(!axi_wr_seq.randomize() with {
          cfg_addr        == not_avail_address_list[i];
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          cfg_data.size == 1;
        }) `uvm_error(get_name, $sformatf("axi_wr_seq randomization error!"));
        // Start the sequence on the respective sequencer
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        if(axi_wr_seq.write_transaction.bresp == AXI_SLVERR_RESPONSE)
          `uvm_info("MVM_WRITE_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and BRESP = %s", not_avail_address_list[i], axi_wr_seq.write_transaction.bresp), UVM_LOW)
        else
         `uvm_error("MVM_WRITE_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and BRESP = %s", not_avail_address_list[i], axi_wr_seq.write_transaction.bresp))

        //read register
        if(!axi_rd_seq.randomize() with {
          cfg_addr        == not_avail_address_list[i];
          sequence_length == 'd1;
          burst_size_enum_t == BURST_SIZE_64BIT;
          burst_type_enum_t == INCR;
          burst_lenght_enum_t == BURST_LENGTH_1;
        }) `uvm_error(get_name, $sformatf("axi_rd_seq randomization error!"));
        axi_rd_seq.start(env.axi_system_env.master[0].sequencer);
        foreach(axi_rd_seq.read_transaction.rresp[i]) begin
          if(axi_rd_seq.read_transaction.rresp[i] == AXI_SLVERR_RESPONSE)
           `uvm_info("MVM_READ_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i], i, axi_rd_seq.read_transaction.rresp[i]), UVM_LOW)
          else
           `uvm_error("MVM_READ_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", not_avail_address_list[i], i, axi_rd_seq.read_transaction.rresp[i]))
        end
      end
    end

    //start a sequence that will receive an OKAY response. This is necessary for coverage purpose of transition from ERROR to OKAY
    wrrd_seq.start(env.sequencer);

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask
endclass

`endif	// __AI_CORE_MVM_ADDRESS_HOLES_WITH_SLVERR_RESP_TEST__
