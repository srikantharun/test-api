/**
* This test has the aim of testing the clock gate enable from the DWPU
*/
class ai_core_dwpu_clk_gate_test extends ai_core_dwpu_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_clk_gate_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    `uvm_info ("build_phase", "Exiting...",UVM_LOW)
  endfunction : build_phase



  virtual task main_phase(uvm_phase phase);
    int counter = 0;
    bit clk_gated_val;
    `uvm_info ("main_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    if (!uvm_hdl_force("hdl_top.dwpu_cg_en", 0)) begin
      `uvm_fatal(get_name(), "Force failed for hdl_top.dwpu_cg_en")
    end
    fork
      begin
        forever begin
          #1;
          if (!uvm_hdl_read("hdl_top.dut.clk_gated", clk_gated_val)) begin
            `uvm_fatal(get_name(), $sformatf("Read failed for %s", "hdl_top.dut.clk_gated"))
          end
          `uvm_info ("build_phase", $sformatf("read value %0d", clk_gated_val),UVM_LOW)
          if(clk_gated_val !== 0) counter++;
        end
      end
      begin
        //spend some time
        #10ns;
      end
    join_any
    disable fork;

    //if (!uvm_hdl_release("hdl_top.dwpu_cg_en")) begin
    //  `uvm_fatal(get_name(), $sformatf("Release failed for %s", "hdl_top.dwpu_cg_en"))
    //end
    
    //spend some time
    #10ns;
    
    if(counter!=0) begin
      `uvm_error(get_type_name(), $sformatf("Clock gate was disable but it countinues to drive clock to the submodules. Counter is %0d and should be equal to 0", counter))
    end
    `uvm_info ("main_phase", "Exiting...",UVM_LOW)
    phase.drop_objection(this);
  endtask
endclass : ai_core_dwpu_clk_gate_test

