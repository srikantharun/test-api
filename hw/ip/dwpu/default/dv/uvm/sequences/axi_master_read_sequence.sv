/**
 * Sequence that is used to random reads to DWPU configuration AXI interface
 */
class axi_master_read_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[AXI_LT_ADDR_WIDTH-1:0]    cfg_addr;
  rand burst_size_t burst_size;
  rand burst_type_t burst_type;
  rand int          burst_length;
  /** Variable that controls if the cfg_data will be partitioned into several transactions or not. By default it does not split. */
  rand bit          split_burst;
  /** Variable that controls if the cfg_addr will be updated (incremented) between bursts. By default it will increment. */
  rand bit          incr_addr_between_bursts;
  /** Variable that controls if the cfg_addr and the number of data that is configured to send will be crossing the 4k boundary from AXI.
  * By default this value is equal to 0, which means that the transaction will not cross the 4k boundary.
  * If the user wants to, by purpose, send a transaction that cross the 4k boundary, then needs to assign this variable to 1. Otherwise the randomization of axi transaction will fail.*/
  rand bit    burst_cross_4k_boundary;
  /** variable that controls if the read is a back-to-back read (without delays) */
  rand bit    back_to_back_en;
  /** variable that controls if the read is a back-to-back read that will have rready with delay */
  rand bit                            rready_delay_on_back_to_back_en;

  cust_svt_axi_master_transaction  read_transaction;

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}

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
  constraint c_rready_delay_on_back_to_back_en{
    soft rready_delay_on_back_to_back_en== 0;
  }
  cust_svt_axi_master_transaction read_tran;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_read_sequence)

  /** Class Constructor */
  function new(string name = "axi_master_read_sequence");
    super.new(name);
  endfunction

  extern virtual task body();
  extern task create_and_send_transaction(axi_lp_addr_t a_addr, int a_burst_length);
  extern function void split_len(int a_len, ref int a_lengths[]);
  extern task send_read_split(axi_lp_addr_t a_addr, int a_burst_length);
  extern task send_read(axi_lp_addr_t a_addr, int a_burst_length);

endclass : axi_master_read_sequence

task axi_master_read_sequence::body();
  svt_configuration get_cfg;
  bit status;
  `uvm_info("axi_master_read_sequence: Body", "Entered", UVM_LOW)

  super.body();

  status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",
                                             sequence_length);
  `uvm_info("body", $sformatf(
            "sequence_length is %0d as a result of %0s.",
            sequence_length,
            status ? "config DB" : "randomization"
            ), UVM_LOW);

  /** Obtain a handle to the port configuration */
  p_sequencer.get_cfg(get_cfg);
  if (!$cast(cfg, get_cfg)) begin
    `uvm_fatal("axi_master_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end

  for (int i = 0; i < sequence_length; i++) begin

    send_read_split(cfg_addr, burst_length);
  end // end for
  `uvm_info("axi_master_read_sequence: Body", "Exiting", UVM_LOW)
endtask : body


task axi_master_read_sequence::create_and_send_transaction(axi_lp_addr_t a_addr, int a_burst_length);
    /** Set up the read transaction */
    `uvm_create(read_tran)
    read_tran.port_cfg    = cfg;
    `uvm_info("create_and_send_transaction", $sformatf("Reading from addr 0x%0x with length %0d", a_addr, a_burst_length), UVM_LOW)
    //randomize transaction
    if(!read_tran.randomize() with {
      if(burst_cross_4k_boundary) {
        (addr % 8) == 0; //this is necessary because, otherwise is not possible to randomize error conditions
      }
      else {
        addr == a_addr;
      }
      xact_type   == svt_axi_transaction::READ;
      burst_type  == int'(local::burst_type);
      burst_size  == int'(local::burst_size);
      atomic_type == svt_axi_transaction::NORMAL;
      burst_length == a_burst_length;
      foreach (rready_delay[i]) {
        rready_delay[i] inside {[0:5]};
      }
      allow_4k_bound_cross == burst_cross_4k_boundary;
      if(back_to_back_en) {
        addr_valid_delay == 0;
        foreach(rready_delay[i]) {
          if (rready_delay_on_back_to_back_en) {
            rready_delay[i] inside {[1:16]};
          }
          else {
            rready_delay[i] == 0;
          }
        }
      }
    }) `uvm_fatal(get_name, "read_tran randomization error!");

    //fix address to a_addr. This is necessary because otherwise is not possible to randomize error conditions. For example, cross boundary error situation
    if(burst_cross_4k_boundary) begin
      read_tran.addr = a_addr;
    end

    /** Send the read transaction */
    `uvm_send(read_tran)
    /** Wait for the read transaction to complete */
    get_response(rsp);
    
    read_transaction = read_tran;
    //read_transaction.print();

endtask : create_and_send_transaction


task axi_master_read_sequence::send_read(axi_lp_addr_t a_addr, int a_burst_length);
  int l_init_burst_length = a_burst_length;
  int l_curr_burst_length;
  int l_remain_burst_length;
  axi_lp_addr_t l_curr_addr;
  axi_lp_data_t l_data_burst_da[];

  //initialization of the variable that saves the length of the burst that needs to be sent
  l_remain_burst_length = l_init_burst_length;
  l_curr_addr = a_addr;
  `uvm_info ("send_read", $sformatf("init: l_init_burst_length= %0d", l_init_burst_length), UVM_LOW)
  `uvm_info ("send_read", $sformatf("init: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_LOW)

  //while the burst length was not all consumed send transactions with data
  while(l_remain_burst_length>0) begin
    //verify if the burst will cross the 2K boundary constraint by the burst length of 8 bits
    if( (((l_curr_addr[10:0]+(l_remain_burst_length*8) )<= 2048) || (burst_cross_4k_boundary))
        && (l_remain_burst_length<256))  begin
      //get the new burst length to make sure the new transactions will not cross  the 4k boundary
      l_curr_burst_length = l_remain_burst_length;
      `uvm_info ("send_read", $sformatf("not_crossing: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_LOW)
      //if the burst do no cross 4k boundary, then create and send the transaction
      create_and_send_transaction(l_curr_addr, l_curr_burst_length);
      l_curr_addr += l_curr_burst_length*8;
      l_remain_burst_length -= l_curr_burst_length;
    end
    else begin
      `uvm_info ("send_read", $sformatf("crossing begin: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_LOW)
      //get the new burst length to make sure the new transactions will not cross  the 4k boundary
      l_curr_burst_length = (2048-l_curr_addr[10:0])/8;
      `uvm_info ("send_read", $sformatf("crossing begin: l_curr_burst_length= %0d", l_curr_burst_length), UVM_LOW)

      //send the transaction for first part of the burst
      create_and_send_transaction(l_curr_addr, l_curr_burst_length);
      l_curr_addr += l_curr_burst_length*8;
      l_remain_burst_length -= l_curr_burst_length;
      `uvm_info ("send_read", $sformatf("crossing end: l_remain_burst_length= %0d | l_curr_burst_length= %0d | l_curr_addr= 0x%0x", l_remain_burst_length, l_curr_burst_length, l_curr_addr), UVM_LOW)
    end
  end

endtask : send_read


function void axi_master_read_sequence::split_len(int a_len, ref int a_lengths[]);
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
      //if(split_burst && back_to_back_en) l_split_len == 1;
      //else
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

task axi_master_read_sequence::send_read_split(axi_lp_addr_t a_addr, int a_burst_length);
  int l_lengths[];

  `uvm_info("send_read_split", $sformatf("Sending transaction starting on address: 0x%0x w/ len: %0d in several transactions", a_addr, a_burst_length), UVM_LOW)
  //request the lengths
  split_len(a_burst_length, l_lengths);
  for (int i=0; i<l_lengths.size; i++) begin
    `uvm_info("send_read_split", $sformatf("Construct new data array with len %0d", l_lengths[i]), UVM_LOW)

    //call send_read with new address and new data array
    send_read(a_addr, l_lengths[i]);
    //update the address with length*8 (64 bits per transaction which is the same as 8 bytes) if the variable incr_addr_between_bursts is active.
    if(incr_addr_between_bursts) a_addr += (l_lengths[i]*8);
  end

endtask : send_read_split
