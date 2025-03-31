class aic_ls_axi_slverr_adapter extends svt_axi_reg_adapter;

  `uvm_object_utils(aic_ls_axi_slverr_adapter)

  extern function new(string name= "aic_ls_axi_slverr_adapter");

  extern virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
endclass

function aic_ls_axi_slverr_adapter::new(string name= "aic_ls_axi_slverr_adapter");
    super.new(name);
endfunction

// -----------------------------------------------------------------------------
function void aic_ls_axi_slverr_adapter::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
  svt_axi_master_transaction bus_trans;
  if (!$cast(bus_trans,bus_item)) begin
     `uvm_fatal("bus2reg", "aic_ls_axi_slverr_adapter::bus2reg: Provided bus_item is not of the correct type");
    return;
  end

  if (bus_trans!= null) begin
    rw.addr = bus_trans.addr;
    rw.data = bus_trans.data[0] ;
    if (bus_trans.xact_type == svt_axi_master_reg_transaction::READ) begin
      rw.kind = UVM_READ;           
      `uvm_info("bus2reg" , $sformatf("bus_trans.data = %0h (READ)", bus_trans.data[0]), UVM_FULL)
      if (bus_trans.rresp[0] inside {svt_axi_transaction::OKAY, svt_axi_transaction::SLVERR})
        rw.status = UVM_IS_OK;
      else
        rw.status  = UVM_NOT_OK;
    end 
    else begin
      if (bus_trans.xact_type == svt_axi_master_reg_transaction::WRITE) begin
        rw.kind = UVM_WRITE;
        if (bus_trans.bresp inside {svt_axi_transaction::OKAY, svt_axi_transaction::SLVERR})
          rw.status = UVM_IS_OK;
        else
          rw.status  = UVM_NOT_OK;
      end
    end
  end
  else
    rw.status  = UVM_NOT_OK;
endfunction
