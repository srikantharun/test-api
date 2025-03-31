`ifndef IAU_STREAM_SEQUENCE_SV
`define IAU_STREAM_SEQUENCE_SV

class iau_stream_sequence extends svt_axi_master_base_sequence;

  int_index_arr_t data_stream_len;
  bit high_value;
  bit [PWORD_SIZE-1:0][IN_WORD_DW-1:0] data;
  int prog_iteration = 1;
  
  `uvm_object_utils(iau_stream_sequence)

  function new(string name="iau_stream_sequence");
    super.new(name);
  endfunction

  function void set_data_stream_length(int_index_arr_t arr);
    data_stream_len = arr;
  endfunction

  virtual task body();
    bit status;
    bit icdf_enable;
    svt_axi_master_transaction trans;
    svt_configuration get_cfg;
    `uvm_info("body", "Entered ...", UVM_LOW)

    super.body();

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end
    if (data_stream_len.size == 0) begin
      `uvm_fatal("body", "data_stream_len array not set! Please set it in the test.");
    end
    repeat (prog_iteration) begin
      foreach (data_stream_len[i]) begin
        `uvm_info("body", $sformatf("Sending data stream %0d of %0d with length: %0d",i+1, data_stream_len.size(), data_stream_len[i]), UVM_HIGH)
        `uvm_create(trans)
        trans.port_cfg            = cfg;
        trans.xact_type           = svt_axi_transaction::DATA_STREAM;
        trans.enable_interleave   = 0;
        trans.interleave_pattern  = svt_axi_transaction::RANDOM_BLOCK;

        trans.stream_burst_length = data_stream_len[i];
        trans.tdata               = new[trans.stream_burst_length];
        trans.tvalid_delay        = new[trans.stream_burst_length];
        foreach (trans.tdata[i]) begin
          trans.tvalid_delay[i] = 0;
          foreach (data[j]) begin
            if (high_value)
              //2**24-1 to 2**26-1
              data[j] = $urandom_range(16777215, 67108863);
            else
              data[j] = $urandom_range(0, 67108863);
          end
          trans.tdata[i] = data;
        end

        `uvm_send(trans)

        get_response(rsp);
      end
    end
    `uvm_info("body", "Exiting...", UVM_LOW)
    data_stream_len.delete();
  endtask: body

endclass: iau_stream_sequence
`endif
