`ifndef DPU_RANDOM_STREAM_SEQUENCE_SV
`define DPU_RANDOM_STREAM_SEQUENCE_SV

class dpu_random_stream_sequence extends svt_axi_master_base_sequence;
  `uvm_object_utils(dpu_random_stream_sequence)
  
  rand int  data_stream_len;
  rand bit [PWORD_SIZE-1:0][IN_IFD0_WORD_DW-1:0] data_q [$];

  constraint c_data_len {
    data_stream_len inside {[1:5]};
    data_q.size() == data_stream_len;
  }


  function new(string name="dpu_random_stream_sequence");
    super.new(name);
  endfunction


  virtual task body();
    bit status;
    svt_axi_master_transaction trans;
    svt_configuration get_cfg;

    super.body();

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) 
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");

    `uvm_create(trans)
    trans.port_cfg            = cfg;
    trans.xact_type           = svt_axi_transaction::DATA_STREAM;
    trans.enable_interleave   = 0;
    trans.interleave_pattern  = svt_axi_transaction::RANDOM_BLOCK;
    trans.stream_burst_length = data_q.size();
    trans.tdata               = new[trans.stream_burst_length];
    trans.tvalid_delay        = new[trans.stream_burst_length];
    trans.tdata               = data_q;

    `uvm_send(trans)
    get_response(rsp);
  endtask: body

endclass: dpu_random_stream_sequence
`endif
