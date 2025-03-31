`ifndef GUARD_AI_CORE_DWPU_RAL_CUSTOM_TEST_SV
`define GUARD_AI_CORE_DWPU_RAL_CUSTOM_TEST_SV

/** AI Core DWPU registers write/read testcase class
* This testcase does the verification of the status of request answer to RO and WO registers.
* No data is compared.
*/
class ai_core_dwpu_ral_custom_test extends ai_core_dwpu_base_test;

  // Registration with the factory
  `uvm_component_utils (ai_core_dwpu_ral_custom_test)
  // Reset sequence
  axi_simple_reset_sequence axi_reset_seq;
  // Register list
  uvm_reg reg_list[$];

  uvm_reg_hw_reset_seq hw_rst_seq;

  // Class Constructor
  function new (string name="ai_core_dwpu_ral_custom_test", uvm_component parent=null);
    super.new (name, parent);
  endfunction: new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...",UVM_LOW)
    super.build_phase(phase);
    // Create simple reset sequence
    axi_reset_seq = axi_simple_reset_sequence::type_id::create("axi_reset_seq");
    hw_rst_seq = uvm_reg_hw_reset_seq::type_id::create("hw_rst_seq",,get_full_name());
    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction: build_phase

  // Run phase
  virtual task run_phase(uvm_phase phase);
    // Variables declaration
    uvm_status_e status;
    uvm_status_e expected_status;
    bit   [63:0] wr_val;
    bit   [63:0] rd_val;
    int          iter_num;
    uvm_reg_field field_list[$];
    bit          wo_field;
    bit          ro_field;

    phase.raise_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)

    // Print RAL model registers information
    regmodel.print();

    // Start reset sequence on the sequencer
    if(!axi_reset_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
    axi_reset_seq.start(env.sequencer);

    // Get register list
    regmodel.get_registers(reg_list);

    // Initializations
    iter_num = 0;

    `uvm_info(get_type_name(), $sformatf("DWPU CSRs WRITES/READ WITH RANDOM VALUES"), UVM_HIGH)
    // Write/Read to all registers of the RAL
    repeat (5)
    begin
      // Write random values to all registers
      foreach(reg_list[i])
      begin

        `uvm_info(get_type_name(), $sformatf("Verifying register %s with access type %s", reg_list[i].get_name(), reg_list[i].get_rights()), UVM_LOW)
        //cleaning queue of fields
        field_list.delete();
        reg_list[i].get_fields(field_list);
        //reset local variables
        wo_field = 0;
        ro_field = 0;
        /** update local variables with information regarding register access type */
        foreach (field_list[i]) begin
          `uvm_info(get_type_name(), $sformatf("field %s with access type %s", field_list[i].get_name(), field_list[i].get_access()), UVM_HIGH)
          if(field_list[i].get_access() == "WO") wo_field = 1;
          if(field_list[i].get_access() inside {"RO", "RC"}) ro_field = 1;
        end
        // Random write value
        /** Write register */
        wr_val = {$urandom(), $urandom()};
        reg_list[i].write(status, wr_val);
        //set the expected values and check the response
        if(ro_field) expected_status = UVM_NOT_OK;
        else         expected_status = UVM_IS_OK;
        if(status != expected_status)
          `uvm_error(get_type_name(), $sformatf("writing operation failed for reg %s. Status = %s and Expected Status = %s", reg_list[i].get_full_name(), status.name(), expected_status.name()))

        /** Read register */
        reg_list[i].read(status, rd_val);
        //set the expected values and check the response
        if(wo_field) expected_status = UVM_NOT_OK;
        else         expected_status = UVM_IS_OK;
        if(status != expected_status)
          `uvm_error(get_type_name(), $sformatf("reading operation failed for reg %s. Status = %s and Expected Status = %s", reg_list[i].get_full_name(), status.name(), expected_status.name()))
        uvm_report_info("DWPURALWRRDTEST: WRVALS", $psprintf("Iter Num = %d Register Name = %18s Written Value = 64'h%h", iter_num, reg_list[i].get_name, wr_val), UVM_HIGH);
        uvm_report_info("DWPURALWRRDTEST: RDVALS", $psprintf("Iter Num = %d Register Name = %18s Read Value    = 64'h%h", iter_num, reg_list[i].get_name, rd_val), UVM_HIGH);
      end
      repeat(20) @(posedge env.m_axi_system_env.vif.common_aclk);
      // Increment iteration number
      iter_num++;
    end // end repeat

    if(!axi_reset_seq.randomize()) `uvm_error(get_name, "axi_reset_seq randomization error!");
    axi_reset_seq.start(env.sequencer);
    repeat(20) @(posedge env.m_axi_system_env.vif.common_aclk);

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask
endclass
`endif // GUARD_AI_CORE_DWPU_RAL_CUSTOM_TEST_SV
