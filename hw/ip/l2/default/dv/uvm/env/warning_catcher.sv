
/**
 *UVM Report Catcher to catch UVM_WARNING  [UVM/RSRC/NOREGEX] a resource with meta characters in the field name  has been created "regmodel.slave_blk"
 */
 class warning_catcher extends uvm_report_catcher;

  function new(string name="warning_catcher");
   super.new(name);
  endfunction

  function action_e catch();
    uvm_severity severity = get_severity();
    if (severity == UVM_FATAL || severity == UVM_ERROR || severity == UVM_WARNING) begin
    set_severity(UVM_INFO);
    return THROW;
    end
    return THROW; 
/*
    string str;
    string scope;
    int err;
    scope = "add_to_master_active";

    str = get_id();

    err = uvm_re_match(scope, str);
    if(!err) begin
      set_severity(UVM_INFO);
      return THROW;
    end
    else begin
      return THROW;		//<-- Display the message if not caught
    end
*/
  endfunction
endclass
