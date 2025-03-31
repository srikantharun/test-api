

class cust_svt_axi_monitor_callback extends svt_axi_port_monitor_callback;

  ai_core_cd_mem_manager mem_mngr_p;

  function new(string name = "cust_svt_axi_monitor_callback");
    super.new(name);
  endfunction

  virtual function void new_transaction_started(svt_axi_port_monitor axi_monitor,
                                                svt_axi_transaction item);

    `uvm_info("SVT_MONITOR_CALLBACK", "Entered transaction started", UVM_LOW)
    super.new_transaction_started(axi_monitor, item);


    `uvm_info("SVT_MONITOR_CALLBACK", "Finished transaction started", UVM_LOW)
  endfunction


  virtual function void transaction_ended(svt_axi_port_monitor axi_monitor,
                                          svt_axi_transaction item);                                      
    bit[64-1:0] addr_range[$];
    string pstr;

    `uvm_info("SVT_MONITOR_CALLBACK", "Entered transaction ended", UVM_LOW)
    super.transaction_ended(axi_monitor, item);
    
    //num_outstanding_xact--;
    //if (item.xact_type == svt_axi_transaction::READ) begin
    //  num_read_outstanding_xact--;
    //end else if (item.xact_type == svt_axi_transaction::WRITE) begin
    //  num_write_outstanding_xact--;
    //end

    //for i from start address to calculated address length 
    //fill address range array to send to the mem manager 

    //addr range size = number of bytes 
    //addr_range_size=2^burst_size/8*length + addr%8


    //`uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item: %p", item), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item: %p", item.sprint()), UVM_LOW)

    
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.Start---------------------------------------------------------"), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.xact_type: %0p", item.xact_type), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.id: %0d", item.id), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.port_id: %0d", item.port_id), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.addr: %0h", item.addr), UVM_LOW)


    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.burst_size: %0d", item.get_burst_size()), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.burst_length: %0d", item.get_burst_length()), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.burst_boundary: %0h", item.get_burst_boundary()), UVM_LOW)

    
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.data.size(): %0d", item.data.size()), UVM_LOW)
    $swriteh(pstr,"%0p", item.data);
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.data: %0s", pstr), UVM_LOW)
    `uvm_info("SVT_MONITOR_CALLBACK", $sformatf("Mon Item.End: ----------------------------------------------------------"), UVM_LOW)


    //compute the targetted addresses 
    for (int i=0; i<item.data.size(); i++ ) begin
      addr_range.push_back(item.addr+i*8);
    end
    

    //send addresses to the right expected queue
    mem_mngr_p.receive_addr_from_svt(item.xact_type, item.id, item.bresp, addr_range);


    `uvm_info("SVT_MONITOR_CALLBACK", "Finished transaction ended", UVM_LOW)

  endfunction


endclass
