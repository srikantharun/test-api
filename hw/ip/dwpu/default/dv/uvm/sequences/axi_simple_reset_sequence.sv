
/**
 * Abstract:
 * class axi_simple_reset_sequence defines a virtual sequence.
 *
 * The axi_simple_reset_sequence drives the reset pin through one
 * activation cycle.
 *
 * The axi_simple_reset_sequence is configured as the default sequence for the
 * reset_phase of the testbench environment virtual sequencer, in the axi_base_test.
 *
 * The reset sequence obtains the handle to the reset interface through the
 * virtual sequencer. The reset interface is set in the virtual sequencer using
 * configuration database, in file top.sv.
 *
 * Execution phase: reset_phase
 * Sequencer: dwpu_axi_virtual_sequencer in testbench environment
 */

`ifndef GUARD_AXI_SIMPLE_RESET_SEQUENCE_SV
`define GUARD_AXI_SIMPLE_RESET_SEQUENCE_SV

class axi_simple_reset_sequence extends uvm_sequence;

  ai_core_dwpu_env_cfg m_env_cfg_h;

  // Random delays to shape the reset, defaults chosen to a sane value at 800MHz

  // Time in ps after the clock edge the reset signal is asserted `1->0` transition
  // This should be randomized to emulate asynchronous application
  rand int unsigned async_rst_delay = 10;

  // The number of full cycles the reset is kept at 0
  // Has to be long enought to ensure all flops have been reset
  rand int unsigned rst_down_cycles = 13;

  // Time in ps after the clock edge the reset signal is deasserted, `0->1` transition
  // This should be randomized to emulate a synchronous deassertion
  rand int unsigned sync_rst_delay = 21;

  // The application is asynchronous, so can arrive anytime during a clock cycle
  constraint async_rst_delay_c {
    0 <= async_rst_delay;
    async_rst_delay < 100;
  }

  // Keep the reset at 0 for a long enought number of cycles
  constraint rst_down_cycles_c {
    12  < rst_down_cycles;
    142 > rst_down_cycles;
  }

  // Reset application is synchronous, this value emulates some jitter on the reset
  constraint sync_rst_delay_c {
    20 < sync_rst_delay;
    sync_rst_delay < 200;
  }

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_simple_reset_sequence)

  /** Declare a typed sequencer object that the sequence can access */
  `uvm_declare_p_sequencer(dwpu_axi_virtual_sequencer)

  /** Class Constructor */
  function new(string name = "axi_simple_reset_sequence");
    super.new(name);
  endfunction : new

  /** Raise an objection if this is the parent sequence */
  virtual task pre_body();
    uvm_phase starting_phase_for_curr_seq;
    super.pre_body();
`ifdef SVT_UVM_12_OR_HIGHER
    starting_phase_for_curr_seq = get_starting_phase();
`else
    starting_phase_for_curr_seq = starting_phase;
`endif
    if (starting_phase_for_curr_seq != null) begin
      starting_phase_for_curr_seq.raise_objection(this);
    end
    if (!uvm_config_db #(ai_core_dwpu_env_cfg)::get(null, "", "AI_CORE_DWPU_ENV_CFG", m_env_cfg_h)) begin
        `uvm_fatal(get_name(), "Unable to get ENV AI_CORE_DWPU_ENV_CFG")
    end
  endtask : pre_body

  /** Drop an objection if this is the parent sequence */
  virtual task post_body();
    uvm_phase starting_phase_for_curr_seq;
    super.post_body();
`ifdef SVT_UVM_12_OR_HIGHER
    starting_phase_for_curr_seq = get_starting_phase();
`else
    starting_phase_for_curr_seq = starting_phase;
`endif
    if (starting_phase_for_curr_seq != null) begin
      starting_phase_for_curr_seq.drop_objection(this);
    end
  endtask : post_body

  virtual task body();
    `uvm_info("body", "Entered...", UVM_HIGH)

    p_sequencer.reset_mp.reset <= 1'b1;

    repeat (10) @(posedge p_sequencer.reset_mp.clk);
    repeat (async_rst_delay) #1ns;
    `uvm_info("body", $sformatf("Async Reset application 1 -> 0 (%0d ns after posedge)", async_rst_delay), UVM_MEDIUM)
    m_env_cfg_h.en_tvalid_during_rst_check = 0;
    p_sequencer.reset_mp.reset <= 1'b0;

    `uvm_info("body", $sformatf("Reset down for %0d cycles", rst_down_cycles), UVM_MEDIUM)
    repeat (rst_down_cycles) @(posedge p_sequencer.reset_mp.clk);

    repeat (sync_rst_delay) #1ns;
    `uvm_info("body", $sformatf("Sync Reset release 0 -> 1 (%0d ns after posedge)", sync_rst_delay), UVM_MEDIUM)
    p_sequencer.reset_mp.reset <= 1'b1;
    m_env_cfg_h.en_tvalid_during_rst_check = 1;
    repeat (10) @(posedge p_sequencer.reset_mp.clk);

    `uvm_info("body", "Exiting...", UVM_HIGH)
  endtask : body

endclass : axi_simple_reset_sequence

`endif  // GUARD_AXI_SIMPLE_RESET_SEQUENCE_SV
