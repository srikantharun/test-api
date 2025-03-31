/**
* Same steps as iau_standard_test , 2 iterations
* Generates invalid programs to generate input and output irq
* 1st iteration: gen input irq by adding more data in the input stream than needed by program
* 2nd iteration: gen output irq by sending last instruction with dst = PUSH instead of PUSH-LAST
*/
class iau_irq_test extends iau_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(iau_irq_test)

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
    bit [63:0] irq_data;
    int rand_idx;
    irq_t gen_irq[$] = {
      ERR_ACT_STREAM_IN,
      ERR_ACT_STREAM_OUT,
      ERR_EARLY_TLAST_STREAM_IN,
      ERR_EARLY_TLAST_STREAM_OUT,
      ERR_PRG_SEGFAULT,
      ERR_PRG_LEN_ZERO,
      ERR_LOOP_ITER_ZERO,
      ERR_ILLEGAL_RFS_INSTR,
      ERR_PRG_SEGFAULT
    };
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(1ms, 1);  // set the timeout
    foreach (gen_irq[i]) begin
      `uvm_info(get_name, $sformatf("Generating %s interruption", gen_irq[i].name), UVM_HIGH)
      common_prog_cfg(.p_smin(10), .p_smax(20), .gen_out_irq(gen_irq[i] == ERR_ACT_STREAM_OUT),
                      .gen_segfault_irq(gen_irq[i] == ERR_PRG_SEGFAULT),
                      .gen_early_out_irq(gen_irq[i] == ERR_EARLY_TLAST_STREAM_OUT),
                      .gen_early_in_irq(gen_irq[i] == ERR_EARLY_TLAST_STREAM_IN),
                      .gen_rfs_irq(gen_irq[i] == ERR_ILLEGAL_RFS_INSTR),
                      .ignore_segfault   ( i > 6 ? 1 : 0                            ) //last execution generates prog segfault irq with ignore_segfault = 1
      );
      prg_seq.start(env.axi_system_env.master[0].sequencer);

      this.cmd = prg_seq.get_cmd();

      if (gen_irq[i] == ERR_ACT_STREAM_IN) begin
        //add more data in one of the streams
        //invalid program: not all input data consumed
        rand_idx = $urandom_range(0, data_stream_len.size - 1);
        data_stream_len[rand_idx] += $urandom_range(1, 10);
        data_seq.set_data_stream_length(data_stream_len);
      end

      if (gen_irq[i] == ERR_ACT_STREAM_OUT) begin
        //generate more push with tlast in the same output stream
        data_seq.set_data_stream_length(data_stream_len);
      end


      if (gen_irq[i] == ERR_PRG_LEN_ZERO) begin
        //invalid program: command with length = 0
        cmd.loop_len = 0;
      end

      if (gen_irq[i] == ERR_LOOP_ITER_ZERO) begin
        //invalid program: command with length = 0
        cmd.loop_iter = 0;
      end

      common_run(.gen_segfault_irq(gen_irq[i] == ERR_PRG_SEGFAULT), .loop_len(this.cmd.loop_len),
                 .loop_start(this.cmd.loop_start), .loop_iter(this.cmd.loop_iter), .reset_en(0));

      env.regmodel.irq_status.read(status, irq_data);
      `uvm_info(get_name, $sformatf(
                "Checking %s interruption, value: %b", gen_irq[i].name, irq_data[gen_irq[i]]),
                UVM_LOW)

      repeat (10) @(posedge env.axi_system_env.vif.common_aclk);
      `uvm_info("run_phase", "Reset", UVM_HIGH)
      rst_seq.start(env.sequencer);
    end

    //testing dbg_sw_interrupt
    if (!csr_cfg_seq.randomize() with {
      irq_en.dbg_sw_interrupt == 1;
    }) `uvm_fatal(get_name, "Randomization Failed!")
    csr_cfg_seq.start(env.sequencer);

    //writing into dp_ctrl.dbg_sw_irq and reading from irq_status.dbg_sw_interrupt
    for (int itr = 0; itr < 8; itr++) begin
      bit i = $urandom_range(0, 1);
      //write 0 and 1 randomly, but only 1 should trigger dbg_sw_interrupt
      env.regmodel.dp_ctrl.write(status, {i, 32'h0});

      repeat (80) @(posedge env.axi_system_env.vif.common_aclk);
      env.regmodel.irq_status.read(status, irq_data);
      `uvm_info(get_name, $sformatf(
                "write into dp_ctrl.dbg_sw_irq: %b, read from irq_status.dbg_sw_interrupt: %b",
                i,
                irq_data[DBG_SW_INTERRUPT]
                ), UVM_HIGH)
      //write 1 to clear dbg_sw_interrupt signal
      if (itr > 5) begin
        env.regmodel.irq_status.write(status, {1'b1, 32'h0});
        repeat (50) @(posedge env.axi_system_env.vif.common_aclk);
        env.regmodel.irq_status.read(status, irq_data);
      end
    end

    `uvm_info("run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : iau_irq_test

