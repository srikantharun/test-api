/**
 * Sequence that is used to random writes to DWPU configuration AXI interface
 */
class axi_master_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned                   sequence_length = 1;
  /** Variable that controls if the cfg_data will be partitioned into several transactions or not. By default it does not split. */
  rand bit                            split_burst;
  /** Variable that controls if the cfg_addr will be updated (incremented) between bursts. By default it will increment. */
  rand bit                            incr_addr_between_bursts;
  /** Variable that controls if the cfg_addr and the number of data that is configured to send will be crossing the 4k boundary from AXI.
  * By default this value is equal to 0, which means that the transaction will not cross the 4k boundary.
  * If the user wants to, by purpose, send a transaction that cross the 4k boundary, then needs to assign this variable to 1. Otherwise the randomization of axi transaction will fail.*/
  rand bit                            burst_cross_4k_boundary;
  /** variable that controls if the write is a back-to-back write (without delays) */
  rand bit                            back_to_back_en;
  /** variable that controls if the write is a back-to-back write will have bready with delay */
  rand bit                            bready_delay_on_back_to_back_en;
  rand bit[AXI_LT_ADDR_WIDTH-1:0]     cfg_addr;
  rand bit[AXI_LT_DATA_WIDTH-1:0]     cfg_data[];
  rand burst_size_t                   burst_size;
  rand burst_type_t                   burst_type;
  rand axi_lp_wstrb_t                 wstrb[];
  rand bit                            fixed_wstrb_en;
  cust_svt_axi_master_transaction write_tran;

  /** Constrain the sequence length to a reasonable value */
  constraint c_reasonable_sequence_length {sequence_length <= 100;}
  constraint c_data {
    soft cfg_data.size inside {[1:16]};
  }
  constraint c_wstrb{
    wstrb.size == cfg_data.size;
    soft fixed_wstrb_en == 1;
    if(fixed_wstrb_en) {
      foreach (wstrb[i]) {
        soft wstrb[i] == 8'hff;
      }
    }
  }
  constraint c_split_burst {
    soft split_burst == 0;
  }
  constraint c_incr_addr_between_bursts {
    soft incr_addr_between_bursts == 1;
  }
  constraint c_burst_cross_4k_boundary{
    soft burst_cross_4k_boundary== 0;
  }
  constraint c_back_to_back_en{
    soft back_to_back_en== 0;
  }
  constraint c_bready_delay_on_back_to_back_en{
    soft bready_delay_on_back_to_back_en== 0;
  }

  //Utility and Field macros,
  `uvm_object_utils(axi_master_write_sequence)

  /** Class Constructor */
  function new(string name = "axi_master_write_sequence");
    super.new(name);
  endfunction

  extern virtual task body();
  extern task create_and_send_transaction(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);
  extern function void split_len(int a_len, ref int a_lengths[]);
  extern task send_write_split(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);
  extern task send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);

endclass : axi_master_write_sequence


task axi_master_write_sequence::body();
  svt_configuration get_cfg;
  bit status;
  `uvm_info("axi_master_write_sequence: Body", "Entered", UVM_MEDIUM)

  super.body();

  status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",
                                             sequence_length);
  `uvm_info("body", $sformatf(
            "sequence_length is %0d as a result of %0s.",
            sequence_length,
            status ? "config DB" : "randomization"
            ), UVM_MEDIUM);

  /** Obtain a handle to the port configuration */
  p_sequencer.get_cfg(get_cfg);
  if (!$cast(cfg, get_cfg)) begin
    `uvm_fatal("axi_master_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end

  for (int i = 0; i < sequence_length; i++) begin
    //uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);

    send_write_split(cfg_addr, cfg_data, wstrb);
  end // end for
  `uvm_info("axi_master_write_sequence: Body", "Exiting", UVM_MEDIUM)
endtask : body


task axi_master_write_sequence::create_and_send_transaction(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);
    /** Set up the write transaction */
    `uvm_create(write_tran)
    write_tran.port_cfg    = cfg;
    foreach (a_data_da[i])`uvm_info("create_and_send_transaction", $sformatf("Sending for addr 0x%0x data[%0d] = 0x%0x | wstrb[%0d] = 0x%0x", a_addr, i, a_data_da[i], i, a_wstrb_da[i]), UVM_HIGH)
    //randomize transaction
    if(!write_tran.randomize() with {
      if(burst_cross_4k_boundary) {
        (addr % 8) == 0; //this is necessary because, otherwise the value of data and strobe can be truncated by a unaligned address
      }
      else {
        addr == a_addr;
      }
      xact_type   == svt_axi_transaction::WRITE;
      burst_type  == int'(local::burst_type);
      burst_size  == int'(local::burst_size);
      atomic_type == svt_axi_transaction::NORMAL;
      burst_length == a_data_da.size;
      foreach (data[i]) {
        data[i] == a_data_da[i];
        wstrb[i] == a_wstrb_da[i];
        wvalid_delay[i] inside {[0:5]};
      }
      allow_4k_bound_cross == burst_cross_4k_boundary;
      if(back_to_back_en) {
        data_before_addr == 0;
        addr_valid_delay == 0;
        foreach(wvalid_delay[i]) {
          wvalid_delay[i] == 0;
        }
        if (bready_delay_on_back_to_back_en) {
          bready_delay inside {[1:16]};
        }
        else {
          bready_delay == 0;
        }
      }
    }) `uvm_fatal(get_name, "write_tran randomization error!");

    //fix address to a_addr. This is necessary because otherwise is not possible to randomize error conditions. For example, cross boundary error situation
    if(burst_cross_4k_boundary) begin
      write_tran.addr = a_addr;
    end

    /** Send the write transaction */
    `uvm_send(write_tran)
    /** Wait for the write transaction to complete */
    get_response(rsp);

endtask : create_and_send_transaction

task axi_master_write_sequence::send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);
  int l_init_burst_length = a_data_da.size();
  int l_curr_burst_length;
  int l_remain_burst_length;
  axi_lp_addr_t l_curr_addr;
  axi_lp_data_t l_data_burst_da[];
  axi_lp_wstrb_t l_wstrb_burst_da[];

  //initialization of the variable that saves the length of the burst that needs to be sent
  l_remain_burst_length = l_init_burst_length;
  l_curr_addr = a_addr;
  `uvm_info ("send_write", $sformatf("init: l_init_burst_length= %0d", l_init_burst_length), UVM_MEDIUM)
  `uvm_info ("send_write", $sformatf("init: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_MEDIUM)

  //while the burst length was not all consumed send transactions with data
  while(l_remain_burst_length>0) begin
    //verify if the burst will cross the 2K boundary constraint by the burst length of 8 bits
    if( (((l_curr_addr[10:0]+(l_remain_burst_length*8) )<= 2048) || (burst_cross_4k_boundary))
        && (l_remain_burst_length<256))  begin
      //get the new burst length to make sure the new transactions will not cross  the 4k boundary
      l_curr_burst_length = l_remain_burst_length;
      `uvm_info ("send_write", $sformatf("not_crossing: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_MEDIUM)
      l_data_burst_da = new[l_curr_burst_length];
      l_wstrb_burst_da= new[l_curr_burst_length];
      for (int i = 0; i < l_remain_burst_length; i++) begin
        `uvm_info ("send_write", $sformatf("not_crossing: l_data_burst_da[%0d] = a_data_da[%0d]", i, i+(l_init_burst_length-l_remain_burst_length)), UVM_HIGH)
        l_data_burst_da[i] = a_data_da[i+(l_init_burst_length-l_remain_burst_length)];
        l_wstrb_burst_da[i] = a_wstrb_da[i+(l_init_burst_length-l_remain_burst_length)];
      end
      //if the burst do no cross 4k boundary, then create and send the transaction
      create_and_send_transaction(l_curr_addr, l_data_burst_da, l_wstrb_burst_da);
      l_curr_addr += l_curr_burst_length*8;
      l_remain_burst_length -= l_curr_burst_length;
    end
    else begin
      `uvm_info ("send_write", $sformatf("crossing begin: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_MEDIUM)
      //get the new burst length to make sure the new transactions will not cross  the 4k boundary
      l_curr_burst_length = (2048-l_curr_addr[10:0])/8;
      `uvm_info ("send_write", $sformatf("crossing begin: l_curr_burst_length= %0d", l_curr_burst_length), UVM_HIGH)

      //fill the data for first part of the transaction
      l_data_burst_da = new[l_curr_burst_length];
      l_wstrb_burst_da= new[l_curr_burst_length];
      for (int i = 0; i < l_curr_burst_length; i++) begin
        `uvm_info ("send_write", $sformatf("crossing: l_data_burst_da[%0d] = a_data_da[%0d]", i, i+(l_init_burst_length-l_remain_burst_length)), UVM_HIGH)
        l_data_burst_da[i] = a_data_da[i+l_init_burst_length-l_remain_burst_length];
        l_wstrb_burst_da[i] = a_wstrb_da[i+l_init_burst_length-l_remain_burst_length];
      end
      //send the transaction for first part of the burst
      create_and_send_transaction(l_curr_addr, l_data_burst_da, l_wstrb_burst_da);
      l_curr_addr += l_curr_burst_length*8;
      l_remain_burst_length -= l_curr_burst_length;
      `uvm_info ("send_write", $sformatf("crossing end: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_MEDIUM)
    end
  end

endtask : send_write

function void axi_master_write_sequence::split_len(int a_len, ref int a_lengths[]);
  int l_success;
  int l_split_len;
  int l_remain_len;

  //reset a_lengths
  a_lengths.delete();

  //set remain_len to be equal to initial len
  l_remain_len = a_len;
  while(l_remain_len != 0)
  begin
    l_success = std::randomize (l_split_len) with {
      if(split_burst) l_split_len inside {[1:l_remain_len]};
      else l_split_len == l_remain_len;
    };
    if(l_success) begin
      //construct new data array
      a_lengths = new[a_lengths.size+1](a_lengths);
      a_lengths[a_lengths.size-1] = l_split_len;
      l_remain_len -= l_split_len;
    end
    else begin
      `uvm_fatal(get_name(), "Unable to randomize a new len");
    end
  end
endfunction : split_len

task axi_master_write_sequence::send_write_split(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[], axi_lp_wstrb_t a_wstrb_da[]);
  axi_lp_data_t l_data_da[];
  axi_lp_wstrb_t l_wstrb_da[];
  int l_lengths[];
  int l_offset;

  `uvm_info("send_write_split", $sformatf("Sending transaction starting on address: 0x%0x w/ len: %0d in several transactions", a_addr, a_data_da.size), UVM_HIGH)
  //request the lengths
  split_len(a_data_da.size, l_lengths);
  l_offset=0;
  for (int i=0; i<l_lengths.size; i++) begin
    `uvm_info("send_write_split", $sformatf("Construct new data array with len %0d", l_lengths[i]), UVM_HIGH)
    //construct new data array
    l_data_da = new[l_lengths[i]];
    l_wstrb_da= new[l_lengths[i]];
    for(int data_idx=0; data_idx<l_lengths[i]; data_idx++) begin
      l_data_da[data_idx] = a_data_da[data_idx+l_offset];
      l_wstrb_da[data_idx] = a_wstrb_da[data_idx+l_offset];
    end
    //update the offset
    l_offset += l_lengths[i];

    foreach(l_data_da[data_idx]) `uvm_info("send_write_split", $sformatf("writing data[%0d]: 0x%0x | wstrb[%0d] = 0x%0x", data_idx, l_data_da[data_idx], data_idx, l_wstrb_da[data_idx]), UVM_HIGH)

    //call send_write with new address and new data array
    send_write(a_addr, l_data_da, l_wstrb_da);
    //update the address with length*8 (64 bits per transaction which is the same as 8 bytes) if the variable incr_addr_between_bursts is active.
    if(incr_addr_between_bursts) a_addr += (l_lengths[i]*8);
  end

endtask : send_write_split

/**
 * Sequence that is used to random writes to DWPU configuration AXI interface
 */
class axi_master_write_split_sequence extends axi_master_write_sequence;

  /** Soft constrain the sequence length to be 1 */
  constraint c_sequence_length_1 {
    soft sequence_length == 1;
  }
  /** Overwrite the split_burst constraint in axi_master_write_sequence */
  constraint c_split_burst {
    soft split_burst == 1;
  }
  /** Soft constrain the burst_type to be INCR */
  constraint c_burst_type {
    soft burst_type == int'(svt_axi_transaction::INCR);
  }
  /** Soft constrain the burst_size to be 64 bits */
  constraint c_burst_size {
    soft burst_size == int'(svt_axi_transaction::BURST_SIZE_64BIT);
  }

  `uvm_object_utils(axi_master_write_split_sequence)

  /** Class Constructor */
  function new(string name = "axi_master_write_split_sequence");
    super.new(name);
  endfunction

endclass : axi_master_write_split_sequence
