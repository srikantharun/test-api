// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

/**
 *UVM Report Catcher to catch UVM_WARNING  
**/

class warning_catcher extends uvm_report_catcher;

  function new(string name="warning_catcher");
   super.new(name);
  endfunction

  //This example demotes "MY_ID" errors to an info message
  function action_e catch();
    if(get_severity() == UVM_WARNING && (get_id() == "[is_valid]"))
      set_severity(UVM_INFO);
    
    return THROW;
  endfunction

endclass

