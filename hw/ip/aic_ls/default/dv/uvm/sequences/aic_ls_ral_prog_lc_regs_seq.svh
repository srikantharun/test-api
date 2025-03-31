// ==========================================================================================================
// Program through RAL sequence
// ==========================================================================================================
class aic_ls_ral_prog_lc_regs_seq extends uvm_sequence;

  `uvm_object_utils(aic_ls_ral_prog_lc_regs_seq)

   // Declare p sequencer
   `uvm_declare_p_sequencer(axi_virtual_sequencer)

  function new(string name = "");
    super.new(name);
  endfunction: new

  task body;
    uvm_status_e   status;
    uvm_reg_data_t write_data;
    bit     [63:0] rand_wrdata;
    bit     [63:0] rd_data;
    int            ii=0;

   repeat (10)
   begin
     rand_wrdata = {$urandom(), $urandom()};
     p_sequencer.regmodel.tkn_regmod.swep_prod_0.write(status, rand_wrdata);
     if (status == UVM_NOT_OK)
       uvm_report_error("LSCSRSEQS", $psprintf("WriteStatus: RAL model could not be written"));
     #10ns;
     p_sequencer.regmodel.tkn_regmod.swep_prod_0.read(status, rd_data);
     if (status == UVM_NOT_OK)
       uvm_report_error("LSCSRSEQS", $psprintf("ReadStatus: RAL model could not be read"));
     
     `uvm_info("PRG_LC", $sformatf("Loop Number = %d Random Write Data = 64'h%0h, Random Exp Data = 64'h%0h", ii, rand_wrdata, rd_data), UVM_LOW)
     ii++;
     #20ns;
   end
  endtask : body

  // Pre-body task
  task pre_body;
    if (starting_phase != null)
      starting_phase.raise_objection(this);
  endtask : pre_body

  // Post-body task
  task post_body;
    if (starting_phase != null)
      starting_phase.drop_objection(this);
  endtask : post_body
endclass : aic_ls_ral_prog_lc_regs_seq
