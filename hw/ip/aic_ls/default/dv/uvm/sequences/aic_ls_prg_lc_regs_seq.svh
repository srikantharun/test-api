// ==========================================================================================================
// SWDP control register programming
// ==========================================================================================================
class aic_ls_prg_lc_regs_seq extends uvm_reg_sequence;
   rand bit  [2:0] cfg_csr_blk;
   rand bit [63:0] cfg_csr_val;

    `uvm_object_utils(aic_ls_prg_lc_regs_seq)

   function new(string name="aic_ls_prg_lc_regs_seq");
     super.new(name);
   endfunction : new

   virtual task body();
    uvm_status_e   status;
    
    // Create an instance variable for the register model
    aic_ls_subsys_reg_block ral_model;

    // Using the variable you just defined above for the
    // register model, downcast the sequence's model reference.
    assert($cast(ral_model, this.model) ) else
       `uvm_fatal("LSCSRSEQS", "Cannot get register model!");

    // RAL model reset and update
    //ral_model.reset("HARD");
    //ral_model.update(status, .parent(this));
    // Check status
    if (status == UVM_NOT_OK)
      uvm_report_error("LSRALSEQ", $psprintf("LS RAL model could not be updated"), UVM_LOW);
    else
      uvm_report_info("LSRALSEQ", $psprintf("LS RAL model updated"));

    #100ns;

    // SWDP control register programming
    case (cfg_csr_blk)
      3'd0: ral_model.m_ifd0_regmod.swdp_ctrl.write(status, cfg_csr_val);
      3'd1: ral_model.m_ifd1_regmod.swdp_ctrl.write(status, cfg_csr_val);
      3'd2: ral_model.m_ifdw_regmod.swdp_ctrl.write(status, cfg_csr_val);
      3'd3: ral_model.d_ifd0_regmod.swdp_ctrl.write(status, cfg_csr_val);
      3'd4: ral_model.d_ifd1_regmod.swdp_ctrl.write(status, cfg_csr_val);
      3'd5: ral_model.m_odr_regmod.swdp_ctrl.write (status, cfg_csr_val);
      3'd6: ral_model.d_odr_regmod.swdp_ctrl.write (status, cfg_csr_val);
    endcase
   endtask : body
endclass : aic_ls_prg_lc_regs_seq
