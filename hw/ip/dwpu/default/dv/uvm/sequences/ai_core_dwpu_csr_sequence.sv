/**
 * CSR sequences for DWPU subip
 */
class ai_core_dwpu_csr_config_sequence extends ai_core_dwpu_base_sequence;
  // Uvm object Utility macro
  bit dwpu_exe = 1;
  bit only_update_exe_ctrl = 0;

  rand bit image_sign;
  rand bit weight_sign;
  rand bit skip_illegal_prog;
  rand bit sw_bypass_en;
  rand bit ptr_rst;

  rand bit irq_en;

  constraint ct_defaul_sw_bypass_en {
    soft sw_bypass_en == 1'b0;
  }
  constraint ct_defaul_ptr_rst {
    soft ptr_rst == 1'b0;
  }

  `uvm_object_utils(ai_core_dwpu_csr_config_sequence)

  // Class Constructor
  function new (string name = "ai_core_dwpu_csr_config_sequence");
    super.new(name);
  endfunction

  extern virtual task body();
  /** Function to compare data */
  extern virtual function bit compare_data(bit [AXI_LT_DATA_WIDTH-1:0] read_data, bit [AXI_LT_DATA_WIDTH-1:0] expected_data, string reg_name);

endclass

task ai_core_dwpu_csr_config_sequence::body();
  uvm_status_e status; // uvm status for write and read
  bit [AXI_LT_DATA_WIDTH-1:0] reg_data;
  bit [AXI_LT_DATA_WIDTH-1:0] reg_mask;
  `uvm_info("body", $sformatf("Entering on csr config sequence body..."), UVM_HIGH)
  if (sw_bypass_en == 0) begin
    p_sequencer.regmodel.cmdblk_ctrl.write(status, dwpu_exe);
    p_sequencer.regmodel.cmdblk_ctrl.read(status, reg_data);
    compare_data(reg_data, dwpu_exe, "cmdblk_ctrl");
  end

  if(only_update_exe_ctrl==0) begin
    p_sequencer.regmodel.dp_ctrl.write(status, {skip_illegal_prog,image_sign,weight_sign});
    p_sequencer.regmodel.dp_ctrl.read(status, reg_data);
    compare_data(reg_data, {skip_illegal_prog,image_sign,weight_sign}, "dp_ctrl");

    p_sequencer.regmodel.irq_en.write(status, {32{irq_en}});
    p_sequencer.regmodel.irq_en.read(status, reg_data);
    reg_mask = 64'h1ffff;
    compare_data(reg_data, ({32{irq_en}} & reg_mask), "irq_en");
  end

  `uvm_info("body", $sformatf("Finished csr config sequence body..."), UVM_HIGH)
endtask : body

function bit ai_core_dwpu_csr_config_sequence::compare_data(bit [AXI_LT_DATA_WIDTH-1:0] read_data, bit [AXI_LT_DATA_WIDTH-1:0] expected_data, string reg_name);
  if(read_data != expected_data) begin
    `uvm_error("dwpu_scb",  $sformatf("Value of read_data is different from expected data for reg %s. read_data = 0x%0x and expected_data = 0x%0x", reg_name,read_data, expected_data) );
  end
endfunction : compare_data
