
/**
 * Abstract:
 * Defines a virtual sequencer for the testbench ENV.  This sequencer obtains
 * a handle to the reset interface using the config db.  This allows
 * reset sequences to be written for this sequencer.
 */

`ifndef AI_CORE_TOP_GUARD_AXI_VIRTUAL_SEQUENCER_SV
`define AI_CORE_TOP_GUARD_AXI_VIRTUAL_SEQUENCER_SV


//typedef  ai_core_top block RAL;
typedef ai_core_env;

class ai_core_top_axi_virtual_sequencer extends uvm_sequencer;

  /** Typedef of the reset modport to simplify access */
  typedef virtual axi_reset_if.axi_reset_modport AXI_RESET_MP;

  /** Reset modport provides access to the reset signal */
  AXI_RESET_MP reset_mp;

  ai_core_env env;
  ai_core_top_reg_block regmodel;
  ai_core_top_reg_block regmodel_core_ctrl;
  `uvm_component_utils(ai_core_top_axi_virtual_sequencer)

  function new(string name="ai_core_top_axi_virtual_sequencer", uvm_component parent=null);
    super.new(name,parent);
  endfunction // new


  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)

    super.build_phase(phase);

    if (!uvm_config_db#(AXI_RESET_MP)::get(this, "", "reset_mp", reset_mp)) begin
      `uvm_fatal("build_phase", "An axi_reset_modport must be set using the config db.");
    end

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction

endclass

`endif // AI_CORE_TOP_GUARD_AXI_VIRTUAL_SEQUENCER_SV
