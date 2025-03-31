
/**
 *UVM Report Catcher to catch UVM_WARNING  [UVM/RSRC/NOREGEX] a resource with meta characters in the field name  has been created "regmodel.slave_blk"
 */
class warning_catcher extends uvm_report_catcher;

  function new(string name="warning_catcher");
   super.new(name);
  endfunction

  function action_e catch();
    string str;
    string scope;
    int err;
    scope = "/a resource with meta characters in the field name has been created/";

    str = get_message();

    err = uvm_re_match(scope, str);

    if(!err) begin
      set_verbosity(UVM_LOW);	//<-- Do not display the message if caught
      return CAUGHT;
    end
    else begin
      return THROW;		//<-- Display the message if not caught
    end
  endfunction
endclass

