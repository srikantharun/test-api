// dpu di test-case class
`ifndef DPU_REGISTER_TEST_SVH
`define DPU_REGISTER_TEST_SVH
class dpu_register_test extends dpu_base_test;

  // Registration with the factory
  `uvm_component_utils(dpu_register_test)

  // Axi reset sequece
  uvm_reg_bit_bash_seq reg_bash_seq;
  uvm_reg reg_list[$];
  bit reg_is_ro_rc[$];
  bit reg_is_w1c[$];
  bit reg_is_default_x[$];

  // Class Constructor
  function new(string name = "dpu_register_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new

  virtual task run_phase(uvm_phase phase);
    uvm_status_e status;
    bit [63:0] idu_dpu_read_value;
    bit [63:0] w1c_read_reg;
    bit [63:0] rc_read_reg;
    phase.raise_objection(this);

    `uvm_info(get_type_name(), $sformatf("Run phase started, raising objection"), UVM_LOW)
    axi_reset_seq.start(env.sequencer);
    env.regmodel.get_registers(reg_list);
    foreach (reg_list[i]) begin
      if (reg_list[i].get_offset() inside { 64'h08, 64'h28, 64'h30, 64'h38, 64'h48, 64'h50, 64'h60, 64'h68, 'h70, 64'h78}  )
        reg_is_ro_rc[i] = 1;
      else reg_is_ro_rc[i] = 0;

      if (reg_list[i].get_offset() inside {64'h28, 64'h30, 64'h38, 64'h48}) reg_is_default_x[i] = 1;
      else begin
        reg_is_default_x[i] = 0;
      end
      if (reg_list[i].get_offset() == 64'h18) reg_is_w1c[i] = 1;
      else begin
        reg_is_w1c[i] = 0;
      end
    end

    /*** DPU REGISTER READING AND WRITING ***/
    // READING RESET VALUES
    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    // Writing AAAA_AAAA_AAAA_AAAA values and reading 
    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].write(status, 64'hAAAA_AAAA_AAAA_AAAA);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reg is Ro/RC = %0d, writing operation falied for reg %s",
                     reg_is_ro_rc[i],
                     reg_list[i].get_full_name()
                     ))
      end
    end

    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    // Writing 5555_5555_5555_5555 values and reading 
    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].write(status, 64'h5555_5555_5555_5555);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "writing operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
        if (rc_read_reg != 0)
          `uvm_error(get_full_name(), $sformatf(
                     "RC regs not zero after writing 1 , value of reg = %0h ", rc_read_reg))

      end
    end

    // Writing random values and reading 
    repeat (5) begin
      foreach (reg_list[i]) begin
        if (!(reg_is_ro_rc[i])) begin
          reg_list[i].write(status, $urandom());
          if (status == UVM_NOT_OK)
            `uvm_error(get_type_name(), $sformatf(
                       "writing operation falied for reg %s", reg_list[i].get_full_name()))
        end

      end
      foreach (reg_list[i]) begin
        if (!(reg_is_ro_rc[i])) begin
          reg_list[i].read(status, idu_dpu_read_value);
          if (status == UVM_NOT_OK)
            `uvm_error(get_type_name(), $sformatf(
                       "reading operation falied for reg %s", reg_list[i].get_full_name()))
        end
      end
    end

   //***  REGISTER READING AND WRITING ***

    // READING RESET VALUES for ro and rc
    foreach (reg_list[i]) begin
      if ((reg_is_ro_rc[i]) && !(reg_is_default_x[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    foreach (reg_list[i]) begin
      if ((reg_is_ro_rc[i]) && !(reg_is_default_x[i])) begin
        reg_list[i].write(status, 64'hAAAA_AAAA_AAAA_AAAA);
        if (status == UVM_IS_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].write(status, 64'hAAAA_AAAA_AAAA_AAAA);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "writing operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    // Writing 5555_5555_5555_5555 values and reading 

    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].write(status, 64'h5555_5555_5555_5555);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "writing operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end
    foreach (reg_list[i]) begin
      if (!(reg_is_ro_rc[i])) begin
        reg_list[i].read(status, idu_dpu_read_value);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))
      end
    end

    // Writing $urandom values and reading 
    repeat (5) begin
      foreach (reg_list[i]) begin
        if (!(reg_is_ro_rc[i])) begin
          reg_list[i].write(status, $urandom());
          if (status == UVM_NOT_OK)
            `uvm_error(get_type_name(), $sformatf(
                       "writing operation falied for reg %s", reg_list[i].get_full_name()))
        end
      end
      foreach (reg_list[i]) begin
        if (!(reg_is_ro_rc[i])) begin
          reg_list[i].read(status, idu_dpu_read_value);
          if (status == UVM_NOT_OK)
            `uvm_error(get_type_name(), $sformatf(
                       "reading operation falied for reg %s", reg_list[i].get_full_name()))
        end
      end
    end

    // Test W1C regs

    foreach (reg_list[i]) begin
      if ((reg_is_w1c[i])) begin
        reg_list[i].write(status, 'hFFFF_FFFF_FFFF_FFFF);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "writing operation falied for reg %s", reg_list[i].get_full_name()))
        reg_list[i].read(status, w1c_read_reg);
        if (status == UVM_NOT_OK)
          `uvm_error(get_type_name(), $sformatf(
                     "reading operation falied for reg %s", reg_list[i].get_full_name()))

        if (w1c_read_reg != 0)
          `uvm_error(get_full_name(), $sformatf(
                     "W1C regs not zero after writing 1 , value of reg = %0h ", w1c_read_reg))

      end
    end


    // Instantiate the bashing sequence
    reg_bash_seq = uvm_reg_bit_bash_seq::type_id::create("reg_bash_seq");
    // Set the register model to be tested
    reg_bash_seq.model = env.regmodel;
    // Exclude specific register from being tested
    uvm_resource_db#(bit)::set(
        {"REG::", env.regmodel.perf_stall_out.get_full_name(), "*"},
        "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set(
        {"REG::", env.regmodel.cmdblk_status.get_full_name(), "*"},
        "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.dp_status.get_full_name(), "*"
                               }, "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set(
        {"REG::", env.regmodel.dbg_observe.get_full_name(), "*"},
        "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set(
        {"REG::", env.regmodel.cmdgen_status.get_full_name(), "*"},
        "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set({"REG::", env.regmodel.dbg_id.get_full_name(), "*"},
                               "NO_REG_BIT_BASH_TEST", 1, this);
    uvm_resource_db#(bit)::set(
        {"REG::", env.regmodel.hw_capability.get_full_name(), "*"},
        "NO_REG_BIT_BASH_TEST", 1, this);

    // Reset the DUT
    reg_bash_seq.reset_blk(env.regmodel);

    // Start the testing
    reg_bash_seq.body();

    phase.drop_objection(this);
    `uvm_info(get_type_name(), $sformatf("Run phase finished, dropping objection"), UVM_LOW)
  endtask

endclass
`endif
