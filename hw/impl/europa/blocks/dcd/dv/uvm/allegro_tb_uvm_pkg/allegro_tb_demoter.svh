
class allegro_tb_demoter extends uvm_report_catcher;
  `uvm_object_utils(allegro_tb_demoter)

  function new(string name="allegro_tb_demoter");
    super.new(name);
  endfunction : new

  function action_e catch();
    if((get_severity() == UVM_ERROR) &&
       ((get_id() == "register_fail:AMBA:AXI3:signal_valid_rdata_when_rvalid_high_check") ||
        (get_id() == "register_fail:AMBA:AXI3:signal_valid_wdata_when_wvalid_high_check")) )begin
      set_severity(UVM_WARNING);
    end
    return THROW;
  endfunction : catch

endclass : allegro_tb_demoter
