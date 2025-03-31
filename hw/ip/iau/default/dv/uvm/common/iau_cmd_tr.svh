/**
 * Sequence item that adds the header information to the command information
 */
class iau_cmd_tr extends ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb;
  
  iau_cmd_header_t header;

  `uvm_object_utils_begin(iau_cmd_tr)
    `uvm_field_int(  header,         UVM_DEFAULT | UVM_NOPRINT)
  `uvm_object_utils_end

  function new(string name = "iau_cmd_tr");
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

endclass : iau_cmd_tr

