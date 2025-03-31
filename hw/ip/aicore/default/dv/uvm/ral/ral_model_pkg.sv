`include "uvm_macros.svh"

package ral_model_pkg;
  import uvm_pkg::*;

  class r1_typ extends uvm_reg;
    rand uvm_reg_field data;
    
    function new(string name = "r1_typ");
      super.new(name,32,UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
      data = uvm_reg_field::type_id::create("data");
      data.configure(this, 8, 0, "RW", 1, `UVM_REG_DATA_WIDTH'h8>>0, 1, 1, 1);
    endfunction
    
    `uvm_object_utils(r1_typ)
  endclass
  
  class b1_typ extends uvm_reg_block;
    rand r1_typ r1;
    
    function new(string name = "b1_typ");
      super.new(name,UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
      r1 = r1_typ::type_id::create("r1");
      r1.configure(this,null,"r1");
      r1.build();
      default_map=create_map("default_map",0,4,UVM_LITTLE_ENDIAN);
      default_map.add_reg(r1,'h4,"RW");
    endfunction
    
    `uvm_object_utils(b1_typ)
  endclass
  
  class top_blk extends uvm_reg_block;
    rand b1_typ b1;
  
    function new(string name = "top_blk");
      super.new(name,UVM_NO_COVERAGE);
    endfunction
  
    virtual function void build();
      b1 = b1_typ::type_id::create("b1");
      b1.configure(this,"b1");
      b1.build();
  
      default_map=create_map("default_map",0,4,UVM_LITTLE_ENDIAN);
      default_map.add_submap(b1.get_default_map(), 'h40);
    endfunction
  
    `uvm_object_utils(top_blk)
  endclass

endpackage

