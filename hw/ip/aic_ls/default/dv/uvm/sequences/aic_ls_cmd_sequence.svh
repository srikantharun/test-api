class aic_ls_cmd_sequence extends svt_axi_master_base_sequence;
  rand addr_gen_cmd_t cmd;
  rand aic_ls_device_t dev;
  `uvm_object_utils(aic_ls_cmd_sequence)
  
  function new(string name = "aic_ls_cmd_sequence");
    super.new(name);
  endfunction

  task body();
  
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    bit status;
    
    
    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_info("body", $sformatf("writing CMDB of %s, cmd: %p", dev.name, cmd), UVM_HIGH)
    `uvm_create(write_tran)
    write_tran.port_cfg    = cfg;
    write_tran.xact_type   = svt_axi_transaction::WRITE;
    write_tran.addr        = dev + CMDB_BASE_ADDR;
    write_tran.burst_type  = svt_axi_transaction::INCR;
    write_tran.burst_size  = svt_axi_transaction::BURST_SIZE_64BIT;
    write_tran.atomic_type = svt_axi_transaction::NORMAL;
    write_tran.burst_length = LS_CMD_NUM_ROWS+1; //+1: including header
    write_tran.data         = new[write_tran.burst_length];
    write_tran.wstrb        = new[write_tran.burst_length];
    write_tran.data_user    = new[write_tran.burst_length];
    write_tran.wvalid_delay = new[write_tran.burst_length];
      
    for (int i = 0; i < LS_CMD_NUM_ROWS+1; i++) begin
      //header or cmd
      write_tran.data[i]         = i == 0 ? {AXI_LP_DATA_WIDTH{1'b0}} : cmd[(i-1) * AXI_LP_DATA_WIDTH +: AXI_LP_DATA_WIDTH];
      write_tran.wstrb[i]        = 8'hff;
      write_tran.wvalid_delay[i] = $urandom_range(0,5);

    end
    /** Send the write transaction */
    `uvm_send(write_tran)

    /** Wait for the write transaction to complete */
    get_response(rsp);
  endtask

endclass
