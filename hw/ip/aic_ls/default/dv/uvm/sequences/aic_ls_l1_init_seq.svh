// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS L1 Init Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

class aic_ls_l1_init_seq#(type T = aic_ls_env) extends aic_ls_ifd_seq#(T);
  `uvm_object_param_utils(aic_ls_l1_init_seq#(T))

  function new(string name = "aic_ls_l1_init_seq");
    super.new(name);
  endfunction

  virtual task body();
     write_to_l1();
  endtask : body

endclass : aic_ls_l1_init_seq
