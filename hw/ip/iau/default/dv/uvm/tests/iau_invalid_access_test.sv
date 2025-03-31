class iau_invalid_access_test extends iau_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_invalid_access_test)

  /** Class Constructor */
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);
    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    bit invld_prgmem_sweep;
    bit invalid_reg_sweep;
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout
    for (int k = 0; k < 2; k++) begin
      invld_prgmem_sweep = ~invalid_reg_sweep;
      `uvm_info(get_name, $sformatf(
                "Generating invalid address for progmem=%0d for reg_sweep=%0d",
                invld_prgmem_sweep,
                invalid_reg_sweep
                ), UVM_HIGH)
      common_prog_cfg(.p_smin(10), .p_smax(20), .invalid_reg_sweep(invalid_reg_sweep),
                      .invld_prgmem_sweep(invld_prgmem_sweep));
      prg_seq.start(env.axi_system_env.master[0].sequencer);

      this.cmd = prg_seq.get_cmd();

      fork
        common_run(.loop_len(this.cmd.loop_len), .loop_start(this.cmd.loop_start),
                   .loop_iter(this.cmd.loop_iter));

        begin
          //disable test when irq is asserted
          repeat (20) @(posedge env.axi_system_env.vif.common_aclk);

          `uvm_info("run_phase", "sent invalid accesses exiting test", UVM_LOW)
        end
      join_any
      disable fork;
      data_seq.kill();
      iau_cmd_seq.kill();
      `uvm_info("run_phase", "Reset", UVM_HIGH)
      rst_seq.start(env.sequencer);
    end
    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : iau_invalid_access_test
