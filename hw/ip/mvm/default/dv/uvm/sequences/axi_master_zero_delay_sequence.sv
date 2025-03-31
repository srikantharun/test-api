`ifndef GUARD_AXI_MASTER_ZERO_DELAY_SEQUENCE_SV
`define GUARD_AXI_MASTER_ZERO_DELAY_SEQUENCE_SV

// AXI Master Stream base sequence
class axi_master_zero_delay_sequence  extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 10;
  rand logic    [PWORD_SIZE-1:0] data [$];
  rand logic      [31:0] burst_length;

  constraint data_c {data.size == burst_length;}

 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_zero_delay_sequence)
    `uvm_field_int(sequence_length,UVM_ALL_ON)
    `uvm_field_queue_int(data,UVM_ALL_ON)
    `uvm_field_int(burst_length,UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name="axi_master_zero_delay_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction transaction;
    svt_configuration          get_cfg;
    longint                    offset_in;
    longint                    offset_out;

    `uvm_info("body", "Entered ...", UVM_HIGH)

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
    end

    foreach (transaction.tvalid_delay[i]) begin
      transaction.tvalid_delay[i] = 0;
    end

    `uvm_send(transaction)
    get_response(rsp);
    `uvm_info("body", "Exiting...", UVM_HIGH)
    uvm_report_info(get_type_name(), $psprintf("transaction = \n %s", transaction.sprint()), UVM_HIGH);
  endtask: body

endclass: axi_master_zero_delay_sequence


`endif // GUARD_AXI_MASTER_ZERO_DELAY_SEQUENCE_SV
