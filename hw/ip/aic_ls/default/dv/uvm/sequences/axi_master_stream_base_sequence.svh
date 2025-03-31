`ifndef GUARD_AXI_MASTER_STREAM_BASE_SEQUENCE_SV
`define GUARD_AXI_MASTER_STREAM_BASE_SEQUENCE_SV

// AXI Master Stream base sequence
class axi_master_stream_base_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 10;
  logic     [511:0] data [$];
  logic      [31:0] burst_length;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_stream_base_sequence)

  /** Class Constructor */
  function new(string name="axi_master_stream_base_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction transaction;
    svt_configuration          get_cfg;
    longint                    offset_in;
    longint                    offset_out;

    `uvm_info("axi_master_stream_base_sequence: Body", "Entered", UVM_LOW)

    super.body();

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    `uvm_create(transaction)
    transaction.port_cfg            = cfg;
    transaction.xact_type           = svt_axi_transaction::DATA_STREAM;
    transaction.stream_burst_length = burst_length;
    transaction.enable_interleave   = 0;
    transaction.tdata               = new[transaction.stream_burst_length];
    transaction.tvalid_delay        = new[transaction.stream_burst_length];
    transaction.interleave_pattern  = svt_axi_transaction::RANDOM_BLOCK;

    foreach (transaction.tdata[i]) begin
       transaction.tdata[i] = data[i];
       uvm_report_info("AXI-S MSTSEQ", $psprintf("Loop Number = %d  Stream Data[%d] = %h", i, i, data[i]), UVM_LOW);
    end

    foreach (transaction.tvalid_delay[i]) begin
      transaction.tvalid_delay[i] = 0;
      uvm_report_info("AXI-S MSTSEQ", $psprintf("Loop Number = %d  TVALID-DELAY[%d] = %h", i, i, transaction.tvalid_delay[i]), UVM_LOW);
    end

    `uvm_send(transaction)
    get_response(rsp);
    //rsp.print(); 
    `uvm_info("axi_master_stream_base_sequence: Body", "Exiting", UVM_LOW)

  endtask: body

endclass: axi_master_stream_base_sequence


`endif // GUARD_AXI_MASTER_STREAM_BASE_SEQUENCE_SV
