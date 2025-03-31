`ifndef AXI_MASTER_SINGLE_WRITE_SEQ_SV
`define AXI_MASTER_SINGLE_WRITE_SEQ_SV

// AXI master write sequence
class axi_master_single_write_seq extends svt_axi_master_base_sequence;

  bit [63:0] addr;
  bit [63:0] data;
  int len;
  svt_axi_transaction::resp_type_enum bresp;

  //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_single_write_seq)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(len, UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::resp_type_enum, bresp, UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "axi_master_single_write_seq");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    bit status;
    `uvm_info(get_type_name(), "Entered ...", UVM_HIGH)

    super.body();

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal(get_type_name(),
                 "Unable to $cast the configuration to a svt_axi_port_configuration class")
    end

    /** Set up the write transaction */
    `uvm_create(write_tran)
    write_tran.port_cfg        = cfg;
    write_tran.xact_type       = svt_axi_transaction::WRITE;
    write_tran.addr            = addr;
    write_tran.burst_type      = svt_axi_transaction::INCR;
    write_tran.burst_size      = svt_axi_transaction::BURST_SIZE_64BIT;
    write_tran.atomic_type     = svt_axi_transaction::NORMAL;
    write_tran.burst_length    = 1;
    write_tran.data            = new[1];
    write_tran.data[0]         = data;
    write_tran.wvalid_delay    = new[1];
    write_tran.wvalid_delay[0] = 1;

    if ((len > 8) || (len < 1))
      `uvm_fatal(get_type_name(), $sformatf("Access length must be between 1 and 8! Got: %d", len))
    write_tran.wstrb    = new[1];
    write_tran.wstrb[0] = 0;
    for (int i = 0; i < len; i++) begin
      write_tran.wstrb[0] += (8'h1 << i);
    end

    /** Send the write transaction */
    `uvm_send(write_tran)

    /** Wait for the write transaction to complete */
    get_response(rsp);

    bresp = write_tran.bresp[0];

    `uvm_info(get_type_name(), "AXI WRITE transaction completed", UVM_HIGH)
  endtask : body

endclass : axi_master_single_write_seq

`endif  // AXI_MASTER_SINGLE_WRITE_SEQ_SV
