/**
 * Sequence that is responsible to randomize and write the AXIS input stream into DWPU
 */
class ai_core_dwpu_stream_sequence extends svt_axi_master_base_sequence;

  svt_axi_master_transaction trans;
  /** Parameter that controls the number of transactions that will be generated */
  ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t stream_cfg;
  bit bypass_data;
  rand bit high_value;
  bit [AIC_PWORD_SIZE-1:0][DWPU_IN_WORD_DW-1:0] data;
  rand bit allow_split_len;
  rand bit enable_tvalid_delay;

  constraint c_sanity_allow_split_len {
    soft allow_split_len == 1;
  }

  /** UVM Object Utility macro */
  `uvm_object_utils(ai_core_dwpu_stream_sequence)

  /** Class Constructor */
  function new(string name="ai_core_dwpu_stream_sequence");
    super.new(name);
  endfunction

  function void set_data_stream_length(ai_core_dp_cmd_gen_uvm_pkg::data_stream_cfg_t s_cfg);
    stream_cfg = s_cfg;
  endfunction

  extern task send_write(string str, int len);
  extern task send_write_split(string str, int len);
  extern virtual task body();

endclass: ai_core_dwpu_stream_sequence


task ai_core_dwpu_stream_sequence::send_write(string str, int len);
  `uvm_create(trans)
  trans.port_cfg            = cfg;
  trans.xact_type           = svt_axi_transaction::DATA_STREAM;
  trans.enable_interleave   = 0;
  trans.stream_burst_length = len;
  trans.tdata               = new[trans.stream_burst_length];
  trans.tvalid_delay        = new[trans.stream_burst_length];
  foreach (trans.tdata[i]) begin
    if(enable_tvalid_delay && (i<5)) begin
      std::randomize(trans.tvalid_delay[i]) with { trans.tvalid_delay[i] inside {[0:16]};};
    end
    else begin
      trans.tvalid_delay[i] = 0;
    end
    foreach (data[j]) begin
      if (high_value)
        data[j] = $urandom_range(127,255);
      else
        data[j] = $urandom_range(0, 255);
    end
    trans.tdata[i] = data;
  end

  `uvm_info("body", $sformatf("Sending %s data stream w/ len: %0d \n %s", str, len,trans.sprint()), UVM_HIGH)
  `uvm_send(trans)

  get_response(rsp);
  repeat ($urandom_range(0,10))
    @(posedge cfg.master_if.common_aclk);
endtask : send_write

task ai_core_dwpu_stream_sequence::send_write_split(string str, int len);
  int l_success;
  int l_split_len;
  int l_remain_len;

  `uvm_info("body", $sformatf("Sending %s data stream w/ len: %0d in several transactions", str, len), UVM_HIGH)
  //set remain_len to be equal to initial len
  l_remain_len = len;
  if(allow_split_len) begin
    while(l_remain_len != 0)
    begin
      l_success = std::randomize (l_split_len) with {
        l_split_len inside {[1:l_remain_len]};
      };
      if(l_success) begin
        send_write(str, l_split_len);
        l_remain_len -= l_split_len;
      end
      else begin
        `uvm_fatal(get_name(), "Unable to $cast the configuration to a svt_axi_port_configuration class");
      end
    end
  end
  else begin
    send_write(str, len);
  end
endtask : send_write_split

task ai_core_dwpu_stream_sequence::body();
  bit status;
  svt_configuration get_cfg;
  int rand_len;
  int avail_len;
  `uvm_info("body", "Entered ...", UVM_LOW)

  super.body();

  /** Obtain a handle to the port configuration */
  p_sequencer.get_cfg(get_cfg);
  if (!$cast(cfg, get_cfg)) begin
    `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end

  //send random data streams
  if (bypass_data) begin
    `uvm_info("bypass_data", $sformatf("Start sending data for bypass"), UVM_HIGH)
    send_write("bypass", $urandom_range(1,20));
    `uvm_info("bypass_data", $sformatf("Finish sending data for bypass"), UVM_HIGH)
  end else begin
    /** send the data with random length for each transaction */
    avail_len=stream_cfg.main_dt_cnt.sum() + stream_cfg.nested_dt_cnt.sum();
    `uvm_info("body", $sformatf("It will send %0d words | main_dt_cnt[0]= %0d | main_dt_cnt[1]= %0d | main_dt_cnt[2]= %0d | nested_dt_cnt[0]= %0d | nested_dt_cnt[1]",avail_len, stream_cfg.main_dt_cnt[0], stream_cfg.main_dt_cnt[1], stream_cfg.main_dt_cnt[2], stream_cfg.nested_dt_cnt[0], stream_cfg.nested_dt_cnt[1]), UVM_HIGH)
    if(avail_len !=0)
      send_write_split("full_data", avail_len);
  end
  `uvm_info("body", "Exiting...", UVM_HIGH)
endtask: body

