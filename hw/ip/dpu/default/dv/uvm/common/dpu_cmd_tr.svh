/**
 * Sequence item that adds the header information to the command information
 */
class dpu_cmd_tr extends ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb;
  
  dpu_cmd_header_t header;

  `uvm_object_utils_begin(dpu_cmd_tr)
    `uvm_field_int(  header,         UVM_DEFAULT | UVM_NOPRINT)
  `uvm_object_utils_end

  function new(string name = "dpu_cmd_tr");
    super.new(name);
  endfunction

  function void do_print(uvm_printer printer);
    super.do_print(printer);
    printer.print_string("header.config"     , $sformatf("%s", header.h_config      ));
    printer.print_string("header.rsvd_format", $sformatf("%s", header.rsvd_format   ));
    printer.print_string("header.format"     , $sformatf("%s", header.format.name() ));
    printer.print_string("header.token_cons" , $sformatf("%s", header.token_cons    ));
    printer.print_string("header.token_prod" , $sformatf("%s", header.token_prod    ));
    printer.print_string("header.rsvd"       , $sformatf("%s", header.rsvd          ));
    printer.print_string("header.triggers"   , $sformatf("%s", header.triggers      ));
  endfunction : do_print

  function void do_copy_from_base(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb aux);
    super.do_copy(aux);
    this.valid             = aux.valid;
    this.format            = aux.format;
    this.nested_1_map_main = aux.nested_1_map_main;
    this.nested_1          = aux.nested_1;
    this.nested_0_map_main = aux.nested_0_map_main;
    this.nested_0          = aux.nested_0;
    this.reserved_1        = aux.reserved_1;
    this.main_2            = aux.main_2;
    this.reserved_0        = aux.reserved_0;
    this.main_1            = aux.main_1;
    this.extra             = aux.extra;
    this.main_0            = aux.main_0;
    this.errors            = aux.errors;
    this.base              = aux.base;
    this.top               = aux.top;

  endfunction : do_copy_from_base
endclass : dpu_cmd_tr

