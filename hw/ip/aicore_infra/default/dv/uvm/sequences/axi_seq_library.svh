// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

// AXI master write sequence
class axi_master_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[`AXI_LP_ADDR_WIDTH-1:0]    cfg_addr;
  rand bit[`AXI_LP_DATA_WIDTH-1:0]    cfg_data[];
  rand bit[8-1:0]    user_data[];
  rand bit[4-1:0]    user_addr;
  rand burst_size_t burst_size_enum_t;
  rand burst_type_t burst_type_enum_t;
  rand burst_length_t burst_length_enum_t;
  rand bit[4-1:0]    init;
  svt_axi_master_transaction write_transaction;
  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint data_c {cfg_data.size == int'(burst_length_enum_t);}
  constraint user_data_c {user_data.size == 1;}
 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_write_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_sarray_int(cfg_data,UVM_ALL_ON)
    `uvm_field_sarray_int(user_data,UVM_ALL_ON)
    `uvm_field_int(user_addr,UVM_ALL_ON)
    `uvm_field_enum(burst_size_t,burst_size_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_type_t,burst_type_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_length_t, burst_length_enum_t,UVM_ALL_ON)
  `uvm_object_utils_end
  /** Class Constructor */
  function new(string name = "axi_master_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
    svt_configuration get_cfg;
    bit status;
    int n_bytes, start_byte, end_byte;

    `uvm_info("axi_master_write_sequence: Body", "Entered", UVM_LOW)

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
      `uvm_fatal("axi_master_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin
      uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);
      /** Set up the write transaction */
      `uvm_create(write_tran)
      write_tran.port_cfg         = cfg;
      write_tran.xact_type        = svt_axi_transaction::WRITE;
      write_tran.addr             = this.cfg_addr;
      write_tran.burst_type       = svt_axi_transaction::INCR;
      write_tran.burst_size       = svt_axi_transaction::BURST_SIZE_64BIT;
      write_tran.atomic_type      = svt_axi_transaction::NORMAL;
      write_tran.burst_length     = 1;
      write_tran.data             = new[write_tran.burst_length];
      write_tran.wstrb            = new[write_tran.burst_length];
      write_tran.wvalid_delay     = new[write_tran.burst_length];
      write_tran.wstrb[0]         = 8'hFF;
      write_tran.wvalid_delay[0]  = 0;
      write_tran.data_before_addr = 0;
      write_tran.addr_valid_delay = 0;
      write_tran.bready_delay     = 0;
      
      foreach (write_tran.data[i]) begin
        write_tran.data[i]      = this.cfg_data[i];
      end

      /** Send the write transaction */
      `uvm_send(write_tran)
      /** Wait for the write transaction to complete */
      get_response(rsp);
      write_transaction = write_tran;
      `uvm_info("axi_master_write_sequence: Body", "AXI WRITE transaction completed", UVM_LOW);
       //xact.print()
    end // end for
    `uvm_info("axi_master_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_write_sequence

// AXI master read sequence
class axi_master_read_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[`AXI_LP_ADDR_WIDTH-1:0]    cfg_addr;
  rand bit[8-1:0]    user_data[];
  rand bit[4-1:0]    user_addr;
  rand int burst_length = 1;
  rand burst_size_t burst_size_enum_t;
  rand burst_type_t burst_type_enum_t;
  rand burst_length_t burst_length_enum_t;
  svt_axi_master_transaction  read_transaction;

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint user_data_c {user_data.size == 1;}
  //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_read_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_sarray_int(user_data,UVM_ALL_ON)
    `uvm_field_int(user_addr,UVM_ALL_ON)
    `uvm_field_enum(burst_size_t,burst_size_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_type_t,burst_type_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_length_t, burst_length_enum_t,UVM_ALL_ON)
  `uvm_object_utils_end

  /** Class Constructor */
  function new(string name = "axi_master_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
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

      uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);
     /** Set up the read transaction */
      `uvm_create(read_tran)
      read_tran.port_cfg        = cfg;
      read_tran.xact_type       = svt_axi_transaction::READ;
      read_tran.addr            = cfg_addr;
      read_tran.burst_type      = svt_axi_transaction::INCR;
      read_tran.burst_size      = svt_axi_transaction::BURST_SIZE_64BIT;
      read_tran.atomic_type     = svt_axi_transaction::NORMAL;
      read_tran.rresp           = new[read_tran.burst_length];
      read_tran.data            = new[read_tran.burst_length];
      read_tran.rready_delay    = new[read_tran.burst_length];
            
      foreach (read_tran.rready_delay[i]) begin
        read_tran.rready_delay[i] = 0;
      end

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      get_response(rsp);
      read_transaction = read_tran;
      `uvm_info("axi_master_read_sequence: Body", "AXI READ transaction completed", UVM_LOW);
    end // end for
      rsp.print();
    `uvm_info("axi_master_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_sequence

// AXI master write sequence
class axi_master_write_random_sequence extends svt_axi_master_base_sequence;

  // Parameter that controls the number of transactions that will be generated
  rand int unsigned sequence_length;
  rand bit[`AXI_HP_ADDR_WIDTH-1:0]    cfg_addr;
  rand bit[`AXI_HP_DATA_WIDTH-1:0]    cfg_data[];
  rand svt_axi_transaction::burst_size_enum burst_size;
  rand svt_axi_transaction::burst_type_enum burst_type;
  rand int delay;
  rand int  burst_length;
  rand bit[3:0] trans_id;
  svt_axi_master_transaction write_transaction;

  // Constrain the sequence length to a reasonable value
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint delay_c {delay inside {[0: `AXI_MAX_DELAY]};}
  constraint burst_size_c {burst_size <= svt_axi_transaction::BURST_SIZE_512BIT;}
  // provide one piece of data of size "burst_size" for each transfer and for each sequence
  constraint data_c {cfg_data.size == sequence_length * burst_length;}
  constraint valid_operations_c {
    burst_type  dist {svt_axi_transaction::INCR :=50, svt_axi_transaction::WRAP:=50}; 
    // calculate 4KB addr limit
    cfg_addr % 4096 + sequence_length * burst_length * (1<<burst_size) <= 4096;
  }
  constraint normal_trans_c {
    solve burst_type before burst_length;
    if (burst_type == svt_axi_master_transaction::INCR) {
      burst_length inside {[1:256]};
    }
    else {
      //AXI protocol rule for WRAP bursts
      burst_length inside {2,4,8,16};
      (2** burst_size * burst_length) <= 4096;
    }
  }

  function void post_randomize();
    int size = 2**burst_size;
    if (burst_type == svt_axi_transaction::WRAP && cfg_addr % size) begin
      `uvm_info(get_name, $sformatf("WRAP access with unnaligned addr: %0h, new alligned addr: %0h", cfg_addr, (cfg_addr/size) * size ), UVM_LOW)
      cfg_addr = (cfg_addr/size) * size;
    end
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, blen: %0d", cfg_addr, burst_type, burst_size, burst_length), UVM_LOW)
  endfunction

 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_write_random_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_int(delay,UVM_ALL_ON)
    `uvm_field_sarray_int(cfg_data,UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::burst_size_enum,burst_size,UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::burst_type_enum,burst_type,UVM_ALL_ON)
    `uvm_field_int(burst_length,UVM_ALL_ON)
    `uvm_field_int(trans_id,UVM_ALL_ON)
  `uvm_object_utils_end
  // Class Constructor /
  function new(string name = "axi_master_write_random_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran;
    svt_configuration get_cfg;
    bit status;
    int n_bytes, offset, index;

    `uvm_info("axi_master_write_random_sequence: Body", "Entered", UVM_LOW)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW);

    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_write_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    fork begin
      for (int iter = 0; iter < sequence_length; iter++) begin
        uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", iter, sequence_length), UVM_LOW);
        // Set up the write transaction
        `uvm_create(write_tran)
        write_tran.port_cfg       = cfg;
        write_tran.xact_type      = svt_axi_transaction::WRITE;
        write_tran.addr           = this.cfg_addr;
        write_tran.burst_type     = this.burst_type;
        write_tran.burst_size     = this.burst_size;
        write_tran.burst_length   = this.burst_length;
        write_tran.atomic_type    = svt_axi_transaction::NORMAL;
        write_tran.data           = new[write_tran.burst_length];
        write_tran.wstrb          = new[write_tran.burst_length];
        write_tran.id             = trans_id;
       
        write_tran.data_before_addr = 0;
        write_tran.addr_valid_delay = 0;
        write_tran.bready_delay = 0;
        write_tran.wvalid_delay = new[write_tran.burst_length];

        for (int k = 0; k < write_tran.burst_length; k++) begin
          write_tran.wvalid_delay[k] = delay;
        end

        n_bytes = 2**write_tran.burst_size;

        //returns calculated wstrb
        get_wstrb(write_tran);
        foreach (write_tran.wstrb[i]) begin
          for (int unsigned b = 0; b < n_bytes; b++) begin
            write_tran.data[i][(b+1) *8-1 -: 8]  = this.cfg_data[i + iter*burst_length][(b+1)*8-1 -: 8];
            `uvm_info("body", $sformatf("wstrb[%0d]: %0h\nwrite_tran.data[%0d]= %0h\ncfg_data[%d]=%0h", i, write_tran.wstrb[i], i, write_tran.data[i], i + iter*burst_length,  this.cfg_data[i + iter*burst_length]) , UVM_HIGH) 
          end
        end

        `uvm_info("body", $sformatf("write_tran.xact_type = %s,  write_tran.addr = %0x, write_tran.burst_type = %s, write_tran.burst_size = %s, write_tran.burst_length = %d, write_tran.atomic_type = %s", write_tran.xact_type,  write_tran.addr, write_tran.burst_type, write_tran.burst_size, write_tran.burst_length, write_tran.atomic_type), UVM_LOW);

        `uvm_info(get_type_name(), $sformatf("sending write transaction = \n %s", write_tran.sprint()), UVM_MEDIUM);
        // Send the write transaction /
        `uvm_send(write_tran)

        // aligne and increment address for next transaction
        cfg_addr = cfg_addr/n_bytes*n_bytes + n_bytes*burst_length;
      end // end for
    end // send request
    begin //wait response
      for (int seq_cnt=0; seq_cnt < sequence_length; seq_cnt++) begin
        // Wait for the write transaction to complete /
        `uvm_info("axi_master_write_random_sequence: Body", $sformatf("AXI WRITE wait for response #%0d", seq_cnt), UVM_LOW);
        get_response(rsp);
        write_transaction = write_tran;
        `uvm_info("axi_master_write_random_sequence: Body", $sformatf("AXI WRITE transaction completed #%0d", seq_cnt), UVM_LOW);
      end
    end //wait response
    join
    `uvm_info("axi_master_write_random_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

  function void get_wstrb(ref svt_axi_master_transaction tr);
    int data_bytes;
    bit [63:0] lower_byte, upper_byte;
    bit [63:0] lower_lane_boundary, upper_lane_boundary;
    bit [`AXI_HP_ADDR_WIDTH-1:0] aligned_addr;
    bit [`AXI_HP_ADDR_WIDTH-1:0] addr;
    int dtsize;
    bit aligned;
    int size;

    data_bytes = `HP_STRB_WIDTH;

    size = 2 ** tr.burst_size;
    addr = tr.addr;
    //rounded down addr
    aligned_addr = (addr/size) * size;
    aligned = (aligned_addr == addr);
    dtsize = size * tr.burst_length;
    `uvm_info("get_wstrb", $sformatf("addr: %0h, btype: %s, bsize: %s dbytes: %0h", 
                                      tr.addr, tr.burst_type, tr.burst_size, data_bytes) , UVM_HIGH) 
    if (tr.burst_type == svt_axi_transaction::WRAP) begin
      lower_lane_boundary = ((addr/dtsize) * dtsize);
      upper_lane_boundary = lower_lane_boundary + dtsize;
    end
    foreach (tr.wstrb[i]) begin
      lower_byte = addr - ((addr/data_bytes) * data_bytes);
      if (aligned) 
        upper_byte = lower_byte + size -1;
      else 
        upper_byte = aligned_addr + size -1 - ((addr/data_bytes) * data_bytes);
      if (tr.burst_type != svt_axi_transaction::FIXED) begin
        if (aligned) begin
        addr = addr + size;
          if (tr.burst_type == svt_axi_transaction::WRAP && addr >= upper_lane_boundary) 
            addr = lower_lane_boundary;
        end
        else begin
          addr = aligned_addr + size;
          aligned = 1;
        end
      end

      for (int j = lower_byte; j <= upper_byte; j++)
        tr.wstrb[i][j] = 1;
    `uvm_info("get_wstrb", $sformatf("addr: %0h, wstrb[%0d]: %0h", addr, i, tr.wstrb[i]) , UVM_HIGH) 
    end
  endfunction

endclass : axi_master_write_random_sequence

// AXI master read sequence
class axi_master_read_random_sequence extends svt_axi_master_base_sequence;

  // Parameter that controls the number of transactions that will be generated
  rand int unsigned sequence_length;
  rand bit[`AXI_HP_ADDR_WIDTH-1:0]    cfg_addr;
  rand int burst_length;
  rand svt_axi_transaction::burst_size_enum burst_size;
  rand svt_axi_transaction::burst_type_enum burst_type;
  rand bit[3:0] trans_id;
  svt_axi_master_transaction  read_transaction;
  rand int delay;
  bit[`AXI_HP_DATA_WIDTH-1:0] rd_data[];
  bit  response_received[];

  svt_axi_master_transaction write_transaction;
  // Constrain the sequence length to a reasonable value /
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint delay_c {delay inside {[0 : `AXI_MAX_DELAY]};}
  constraint burst_size_c {burst_size <= svt_axi_transaction::BURST_SIZE_512BIT;}
  constraint valid_operations_c {
    burst_type  dist {svt_axi_transaction::INCR :=50, svt_axi_transaction::WRAP:=50}; 
    //calculate 4KB addr limit
    cfg_addr % 4096 + sequence_length * burst_length * (1<<burst_size) <= 4096;
  }
  constraint normal_trans_c {
    solve burst_type before burst_length;
    if (burst_type == svt_axi_master_transaction::INCR) {
      burst_length inside {[1:256]};
    }
    else {
      //AXI protocol rule for WRAP bursts
      burst_length inside {2,4,8,16};
      (2** burst_size * burst_length) <= 4096;
    }
  }

  function void post_randomize();
    int size = 2**burst_size;
    if (burst_type == svt_axi_transaction::WRAP && cfg_addr % size) begin
      `uvm_info(get_name, $sformatf("WRAP access with unnaligned addr: %0h, new alligned addr: %0h", cfg_addr, (cfg_addr/size) * size ), UVM_LOW)
      cfg_addr = (cfg_addr/size) * size;
    end
    response_received = new[sequence_length];
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, blen: %0d", cfg_addr, burst_type, burst_size, burst_length), UVM_LOW)
  endfunction

  //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_read_random_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_int(trans_id,UVM_ALL_ON)
    `uvm_field_int(delay,UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::burst_size_enum, burst_size,UVM_ALL_ON)
    `uvm_field_enum(svt_axi_transaction::burst_type_enum,burst_type,UVM_ALL_ON)
    `uvm_field_int(burst_length,UVM_ALL_ON)
  `uvm_object_utils_end

  // Class Constructor
  function new(string name = "axi_master_read_random_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
    svt_configuration get_cfg;
    bit status;
    `uvm_info("axi_master_read_random_sequence: Body", "Entered", UVM_LOW)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",sequence_length);
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.",sequence_length,status ? "config DB" : "randomization"), UVM_LOW);

    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_read_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    fork
    begin // transmit request
      for (int iter = 0; iter < sequence_length; iter++) begin

        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", iter, sequence_length), UVM_LOW);
        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("cfg_addr: %h, burst_size: %s, burst_length: %d", cfg_addr, burst_size, burst_length), UVM_LOW);
       // Set up the read transaction
        `uvm_create(read_tran)
        read_tran.port_cfg        = cfg;
        read_tran.xact_type       = svt_axi_transaction::READ;
        read_tran.addr            = cfg_addr;
        read_tran.burst_type      = this.burst_type;
        read_tran.burst_size      = this.burst_size;
        read_tran.burst_length    = this.burst_length;
        read_tran.id              = this.trans_id;
        read_tran.atomic_type     = svt_axi_transaction::NORMAL;
        read_tran.rresp           = new[read_tran.burst_length];
        read_tran.data            = new[read_tran.burst_length];
        read_tran.rready_delay    = new[read_tran.burst_length];
            
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = delay;
        end

        `uvm_info(get_type_name(), $sformatf("sending read transaction = \n %s", read_tran.sprint()), UVM_LOW);
        // Send the read transaction
        `uvm_send(read_tran)
        // increment address for next transaction
        cfg_addr = cfg_addr + 2**burst_size*burst_length;
      end // end for
    end // send request
    begin // wait for response
      rd_data = new[sequence_length * read_tran.burst_length];
      for (int seq_cnt = 0; seq_cnt < sequence_length; seq_cnt++) begin
        `uvm_info("axi_master_read_random_sequence: Body", $sformatf("AXI READ wait for response #%0d", seq_cnt), UVM_LOW);
        // Wait for the read transaction to complete
        get_response(rsp);
        response_received[seq_cnt] = 1;
        read_transaction = read_tran;
        foreach (rsp.data[i]) begin
          `uvm_info("axi_master_read_random_sequence: Body", $sformatf("rsp.data[%0d] = %0h", i, rsp.data[i]), UVM_LOW);
          rd_data[i+seq_cnt*read_tran.burst_length] = rsp.data[i];
        end
        `uvm_info("axi_master_read_random_sequence: Body", $sformatf("AXI READ transaction #%0d completed", seq_cnt), UVM_LOW);
      end
    end // wait for response
    join
      rsp.print();
    `uvm_info("axi_master_read_random_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_random_sequence

class axi_dma_write_sequence extends axi_master_write_random_sequence;
  
  // size of DMA write transfer in bytes
  rand int size;
  rand burst_size_t bandwidth;
  //int beat_num;

  constraint dma_size_c {size % bandwidth == 0;}
  constraint dma_burst_size_c {burst_size == bandwidth;}
  constraint dma_burst_type_c {burst_type == svt_axi_master_transaction::INCR;}
  constraint dma_data_size_c {cfg_data.size() == size/(2**bandwidth);}

  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, blen: %0d, cfg_data.size = %0d", cfg_addr, burst_type, burst_size, burst_length, cfg_data.size()), UVM_LOW)
  endfunction

  `uvm_object_utils(axi_dma_write_sequence)
  // Class Constructor
  function new(string name = "axi_dma_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("axi_dma_write_sequence: Body", "Entered", UVM_LOW)
    super.body();

    `uvm_info("axi_dma_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_dma_write_sequence

class axi_dma_read_sequence extends axi_master_read_random_sequence;

  // size of DMA read transfer in bytes
  rand int size;
  rand burst_size_t bandwidth;

  constraint dma_size_c {size % bandwidth == 0;}
  constraint dma_burst_size_c {burst_size == bandwidth;}
  constraint dma_burst_type_c {burst_type == svt_axi_master_transaction::INCR;}
  constraint dma_len_c {size == sequence_length * burst_length;}

  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, blen: %0d, size: %0d, sequence_length: %0d", cfg_addr, burst_type, burst_size, burst_length, size, sequence_length), UVM_LOW)
  endfunction

  `uvm_object_utils(axi_dma_read_sequence)
  // Class Constructor 
  function new(string name = "axi_dma_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("axi_dma_read_sequence: Body", "Entered", UVM_LOW)
    super.body();

    `uvm_info("axi_dma_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_dma_read_sequence

// AXI MASTER SEQUENCE TO GEN ALL WR/RD
//class axi_master_sequence extends svt_axi_master_base_sequence;
//
//  /** Parameter that controls the number of transactions that will be generated */
//  rand bit b2b_txn;
//
//  rand int unsigned sequence_length = 1;
//  rand bit[`AXI_HP_ADDR_WIDTH-1:0] addr;
//  rand bit[`AXI_HP_DATA_WIDTH-1:0] data[];
//  rand noc_init_e noc_init;
//  rand int burst_length;
//  rand svt_axi_transaction::burst_size_enum burst_size;
//  rand svt_axi_transaction::burst_type_enum burst_type;
//  rand svt_axi_transaction::xact_type_enum xact_type;
//  rand svt_axi_transaction::atomic_type_enum atomic_type;
//  rand svt_axi_transaction::coherent_xact_type_enum coherent_xact_type;
//  rand bit cache_modifiable;
//  rand svt_axi_transaction::prot_type_enum prot_type;
//  rand int id;
//
//  constraint valid_operations_c {
//    solve noc_init before burst_size, id;
//    solve atomic_type before xact_type, burst_type, burst_length, burst_size, prot_type;
//    atomic_type inside {svt_axi_transaction::NORMAL, svt_axi_transaction::EXCLUSIVE};
//    xact_type   inside {svt_axi_transaction::READ, svt_axi_transaction::WRITE, svt_axi_transaction::COHERENT};
//    burst_type  inside {svt_axi_transaction::INCR, svt_axi_transaction::WRAP}; 
//    prot_type   inside {svt_axi_transaction::DATA_SECURE_NORMAL, svt_axi_transaction::DATA_SECURE_PRIVILEGED};
//    if (atomic_type == svt_axi_transaction::NORMAL) {
//      xact_type != svt_axi_transaction::COHERENT;
//    }
// 
//    //calculate 4KB addr limit
//    addr % 4096 + burst_length * (1<<burst_size) <= 4096;
//
//
//    data.size() ==  burst_length;
//
//    if (noc_init inside {init_ai_core_0_hp, init_ai_core_1_hp,
//                         init_ai_core_2_hp, init_ai_core_3_hp,
//                         init_sys_dma_0_hp, init_sys_dma_1_hp}) {
//       burst_size <= svt_axi_transaction::BURST_SIZE_512BIT;
//    }
//    else {
//       burst_size <= svt_axi_transaction::BURST_SIZE_64BIT;
//    }
//
//
//    if (noc_init inside { init_pcie_hp, init_sys_ctrl_lp, 
//                          init_sys_dma_0_hp, init_sys_dma_1_hp }) {
//      id inside {[0:2**6-1]}; //id is 6b width
//    }
//    else {
//      id inside {[0:2**9-1]}; 
//    }
//
//  }
//
//  constraint normal_trans_c {
//    if (burst_type == svt_axi_master_transaction::INCR) {
//      burst_length inside {[1:256]};
//    }
//    else {
//      //AXI protocol rule for WRAP bursts
//      burst_length inside {2,4,8,16};
//      (2** burst_size * burst_length) <= 4096;
//    }
//  }
//
//  //based on AXI protocol section A7.3.3
//  constraint exclusive_trans_c {
//    if (atomic_type == svt_axi_transaction::EXCLUSIVE) {
//
//      //NOC restrictions:
//      //https://git.axelera.ai/ai-hw-team/triton/-/issues/2296#note_113280
//      burst_type   == svt_axi_transaction::INCR; 
//      burst_length == 1;
//      burst_size inside {svt_axi_transaction::BURST_SIZE_32BIT, svt_axi_transaction::BURST_SIZE_64BIT};
//
//      xact_type  == svt_axi_transaction::COHERENT;
//      coherent_xact_type inside {svt_axi_transaction::READNOSNOOP, svt_axi_transaction::WRITENOSNOOP};
//    }
//  }
//
//
//  function void post_randomize();
//    int size = 2**burst_size;
//    if (atomic_type == svt_axi_transaction::NORMAL && burst_type == svt_axi_transaction::WRAP && addr % size) begin
//      `uvm_info(get_name, $sformatf("WRAP access with unnaligned addr: %0h, new alligned addr: %0h", addr, (addr/size) * size ), UVM_HIGH)
//      addr = (addr/size) * size;
//    end
//
//    //address must be aligned to the total number of bytes in an EXCLUSIVE access transaction
//    else if (atomic_type == svt_axi_transaction::EXCLUSIVE) begin
//      size = burst_length * 2 ** burst_size * 8;
//      addr -= addr % size;
//
//      `uvm_info(get_name, $sformatf("Exclusive access, aligned addr: %0h", addr), UVM_HIGH)
//    end
//    `uvm_info(get_name, $sformatf("noc_init: %s atype: %s btype: %s, bsize: %s, blen: %0d", noc_init, atomic_type, burst_type, burst_size, burst_length), UVM_HIGH)
//  endfunction
//  //Utility and Field macros,
//  `uvm_object_utils(axi_master_sequence)
//
//  /** Class Constructor */
//  function new(string name = "axi_master_sequence");
//    super.new(name);
//  endfunction
//
//  virtual task body();
//    svt_axi_master_transaction trans; 
//    svt_configuration get_cfg;
//    bit status;
//    `uvm_info("axi_master_sequence: Body", "Entered", UVM_LOW)
//    super.body();
//
//    if($test$plusargs("B2B_TXN")) begin
//      $value$plusargs("B2B_TXN=%0d", b2b_txn);
//      `uvm_info(get_name, $sformatf("B2B_TXN comp param set to %0d", b2b_txn), UVM_HIGH)
//    end
//    else begin
//      `uvm_info(get_name, $sformatf("b2b_txn randomize to %0d", b2b_txn), UVM_HIGH)
//    end
//
//    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",
//                                               sequence_length);
//    `uvm_info("body", $sformatf(
//              "sequence_length is %0d as a result of %0s.",
//              sequence_length,
//              status ? "config DB" : "randomization"
//              ), UVM_LOW);
//
//    /** Obtain a handle to the port configuration */
//    p_sequencer.get_cfg(get_cfg);
//    if (!$cast(cfg, get_cfg)) begin
//      `uvm_fatal("axi_master_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
//    end
//
//    for (int i = 0; i < sequence_length; i++) begin
//
//      /** Set up the read transaction */
//      `uvm_create(trans)
//      trans.port_cfg            = cfg;
//      trans.id                  = this.id;
//      trans.xact_type           = this.xact_type;
//      trans.addr                = this.addr;
//      trans.burst_type          = this.burst_type;
//      trans.burst_size          = this.burst_size;
//      trans.burst_length        = this.burst_length;
//      trans.atomic_type         = this.atomic_type;
//      trans.coherent_xact_type  = this.coherent_xact_type;
//      trans.cache_type[1]       = cache_modifiable;
//      trans.prot_type           = this.prot_type;
//
//      trans.transmitted_channel = ( (trans.atomic_type == svt_axi_transaction::NORMAL) ? trans.xact_type :
//         ((coherent_xact_type == svt_axi_transaction::WRITENOSNOOP) ? svt_axi_transaction::WRITE : svt_axi_transaction::READ)
//      );
//
//      trans.data                = new[trans.burst_length];
//      if (b2b_txn) trans.addr_valid_delay = 0;
//     
//      if (trans.transmitted_channel == svt_axi_transaction::READ) begin
//        trans.rresp           = new[trans.burst_length];
//        trans.rready_delay    = new[trans.burst_length];
//        foreach (trans.rready_delay[i])
//          trans.rready_delay[i] = b2b_txn ? 0 : $urandom_range(0,10);
//      end 
//      else if (trans.transmitted_channel == svt_axi_transaction::WRITE) begin
//        trans.wstrb          = new[trans.burst_length];
//        foreach (trans.data[i])
//          trans.data[i]      = this.data[i];
//
//        //manual generation of wstrb since wysiwyg_enable is set to 1 in axi_cfg
//        //returns calculated wstrb
//        get_wstrb(trans, noc_init);
//
//        trans.wvalid_delay   = new[trans.burst_length];
//        foreach (trans.wvalid_delay[i]) 
//          trans.wvalid_delay[i] = b2b_txn ? 0 : $urandom_range(0,10);
//      end
//
//      `uvm_info(get_type_name(), $sformatf("sending transaction = \n %s", trans.sprint()), UVM_HIGH);
//      `uvm_send(trans)
//
//      if (!b2b_txn) begin 
//        get_response(rsp);
//        //rsp.print();
//      end
//    end // end for
//
//    `uvm_info("axi_master_sequence: Body", "Exiting", UVM_LOW)
//  endtask : body
//
//  //took from AXI Protocol Section A4.1.7
//  //calculates wstrb according data_width and burst type
//  //allows narrow transfers and fix unaligned addr for wrapping burst 
//  function void get_wstrb(ref svt_axi_master_transaction tr ,noc_init_e init);
//    int data_bytes;
//    bit [63:0] lower_byte, upper_byte;
//    bit [63:0] lower_lane_boundary, upper_lane_boundary;
//    bit [`AXI_HP_ADDR_WIDTH-1:0] aligned_addr;
//    bit [`AXI_HP_ADDR_WIDTH-1:0] addr;
//    int dtsize;
//    bit aligned;
//    int size;
//
//
//    case (init)
//      init_ai_core_0_hp, init_ai_core_1_hp,
//      init_ai_core_2_hp, init_ai_core_3_hp,
//      init_sys_dma_0_hp, init_sys_dma_1_hp : data_bytes = `HP_STRB_WIDTH;
//
//      default: data_bytes = `LP_STRB_WIDTH;
//    endcase
//
//    size = 2 ** tr.burst_size;
//    addr = tr.addr;
//    //rounded down addr
//    aligned_addr = (addr/size) * size;
//    aligned = (aligned_addr == addr);
//    dtsize = size * tr.burst_length;
//    `uvm_info("get_wstrb", $sformatf("noc_init: %s, addr: %0h, btype: %s, bsize: %s dbytes: %0h", 
//                                      init, tr.addr, tr.burst_type, tr.burst_size, data_bytes) , UVM_HIGH) 
//    if (tr.burst_type == svt_axi_transaction::WRAP) begin
//      lower_lane_boundary = ((addr/dtsize) * dtsize);
//      upper_lane_boundary = lower_lane_boundary + dtsize;
//    end
//    foreach (tr.wstrb[i]) begin
//      lower_byte = addr - ((addr/data_bytes) * data_bytes);
//      if (aligned) 
//        upper_byte = lower_byte + size -1;
//      else 
//        upper_byte = aligned_addr + size -1 - ((addr/data_bytes) * data_bytes);
//      if (tr.burst_type != svt_axi_transaction::FIXED) begin
//        if (aligned) begin
//          addr = addr + size;
//          if (tr.burst_type == svt_axi_transaction::WRAP && addr >= upper_lane_boundary) 
//            addr = lower_lane_boundary;
//        end
//        else begin
//          addr = aligned_addr + size;
//          aligned = 1;
//        end
//      end
//
//      for (int j = lower_byte; j <= upper_byte; j++)
//        tr.wstrb[i][j] = 1;
//      `uvm_info("get_wstrb", $sformatf("addr: %0h, wstrb[%0d]: %0h", addr, i, tr.wstrb[i]) , UVM_HIGH) 
//    end
//  endfunction
//
//
//
//
//endclass : axi_master_sequence

