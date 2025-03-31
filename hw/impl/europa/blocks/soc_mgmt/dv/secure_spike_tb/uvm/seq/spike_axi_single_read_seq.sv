`ifndef SPIKE_AXI_SINGLE_READ_SEQ_SV
`define SPIKE_AXI_SINGLE_READ_SEQ_SV

// AXI master read sequence
class axi_master_single_read_seq extends svt_axi_master_base_sequence;

  bit [63:0] addr;
  bit [63:0] data;
  svt_axi_transaction::resp_type_enum rresp;

  //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_single_read_seq)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::resp_type_enum, rresp, UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "axi_master_single_read_seq");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction read_tran;
    svt_configuration get_cfg;

    `uvm_info(get_type_name(), "Entered ...", UVM_HIGH)

    super.body();

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal(get_type_name(),
                 "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_create(read_tran)
    read_tran.port_cfg        = cfg;
    read_tran.xact_type       = svt_axi_transaction::READ;
    read_tran.addr            = addr;
    read_tran.burst_type      = svt_axi_transaction::INCR;
    read_tran.burst_size      = svt_axi_transaction::BURST_SIZE_64BIT;
    read_tran.atomic_type     = svt_axi_transaction::NORMAL;
    read_tran.burst_length    = 1;
    read_tran.rresp           = new[1];
    read_tran.data            = new[1];
    read_tran.rready_delay    = new[1];
    read_tran.rready_delay[0] = 1;

    /** Send the read transaction */
    `uvm_send(read_tran)

    /** Wait for the read transaction to complete */
    get_response(rsp);

    data  = read_tran.data[0];
    rresp = read_tran.rresp[0];

    `uvm_info(get_type_name(), "AXI READ transaction completed", UVM_HIGH);

  endtask : body

endclass : axi_master_single_read_seq

`endif  // SPIKE_AXI_SINGLE_READ_SEQ_SV
