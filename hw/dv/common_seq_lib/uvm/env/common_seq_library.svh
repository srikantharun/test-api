// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //

// AXI master write sequence
class axi_master_write_random_sequence extends svt_axi_master_base_sequence;

  // Parameter that controls the number of transactions that will be generated
  rand int unsigned sequence_length;
  rand bit[`AXI_HP_ADDR_WIDTH-1:0]    cfg_addr;
`ifndef AXI_DATA_WIDTH
  rand bit[`AXI_HP_DATA_WIDTH-1:0] cfg_data[];
`else
  rand bit[`AXI_DATA_WIDTH-1:0]    cfg_data[];
`endif
  rand svt_axi_transaction::burst_size_enum burst_size;
  rand svt_axi_transaction::burst_type_enum burst_type;

  rand svt_axi_transaction::xact_type_enum xact_type;
  rand svt_axi_transaction::atomic_type_enum atomic_type;
  rand svt_axi_transaction::coherent_xact_type_enum coherent_xact_type;

  rand bit cache_bufferable;
  rand bit cache_modifiable;
  rand bit cache_allocate;
  rand bit cache_other_allocate;
  rand bit[2:0] burst_prot;

  rand bit[`AXI_MAX_ADDR_USER_WIDTH  - 1 : 0] addr_user;
  rand bit[`AXI_MAX_DATA_USER_WIDTH  - 1 : 0] data_user;
  rand bit[`AXI_MAX_DATA_USER_WIDTH  - 1 : 0] physical_data_user;
  rand bit[`AXI_MAX_BRESP_USER_WIDTH - 1 : 0] resp_user;

  rand bit[`AXI_QOS_WIDTH - 1 : 0] qos;

  rand int delay;
  rand int unsigned min_addr_valid_delay;
  rand int unsigned max_addr_valid_delay;
  rand int unsigned min_bready_delay;
  rand int unsigned max_bready_delay;
  rand int  burst_length;
`ifndef AXI_ID_WIDTH
  rand bit[3 : 0] trans_id;
`else
  rand bit[`AXI_ID_WIDTH - 1 : 0] trans_id;
`endif
  int written_bytes = 0;
  int prev_burst_bytes;
  rand bit outstanding_req;

  rand int max_bw;
  rand bit wait_rsp;

  svt_axi_master_transaction response;
  rand bit inj_err;

  constraint c_addr_valid_delay {
                                       max_addr_valid_delay >= min_addr_valid_delay;
                                  soft min_addr_valid_delay == 0; 
                                  soft max_addr_valid_delay == 0;
  }
   constraint c_bready_delay {
                                       max_bready_delay >= min_bready_delay;
                                  soft min_bready_delay == 0;
                                  soft max_bready_delay == 0;
  }

  constraint max_bw_c{
`ifndef AXI_DATA_WIDTH
    soft max_bw == 64;
`else
    soft max_bw == `AXI_DATA_WIDTH / 8;
`endif
  }

  constraint wait_rsp_c{
    soft wait_rsp == 1;
  }
  // default access type will be NORMAL/WRITE, but we can use the same sequence for atomic op
  constraint normal_access_c{
    soft atomic_type == svt_axi_transaction::NORMAL;
    soft xact_type   == svt_axi_transaction::WRITE;
    soft qos == 0;
    soft outstanding_req == 0;
    soft inj_err == 0;
  }

  // Constrain the sequence length to a reasonable value
  constraint reasonable_sequence_length {soft sequence_length <= 100;}
  constraint delay_c {delay inside {[0: `AXI_MAX_DELAY]};}
  // provide one piece of data of size "burst_size" for each transfer and for each sequence
  constraint data_c {
    //solve burst_length before cfg_data.size();
    //solve burst_size before cfg_data.size();
    //solve burst_type before cfg_data.size();
    //solve cfg_addr before cfg_data.size();
    cfg_data.size >= sequence_length * burst_length;
    cfg_data.size < 3000;}
  constraint valid_operations_c {
    solve atomic_type before xact_type, burst_type, burst_length, burst_size;
    atomic_type inside {svt_axi_transaction::NORMAL, svt_axi_transaction::EXCLUSIVE};
    xact_type   inside {svt_axi_transaction::WRITE, svt_axi_transaction::COHERENT};
    // calculate 4KB addr limit
    cfg_addr % 4096 + burst_length * (1<<burst_size) <= 4096;
    if (atomic_type == svt_axi_transaction::NORMAL) {
      xact_type != svt_axi_transaction::COHERENT;
    }
  }
  constraint normal_trans_c {
    solve burst_type before burst_length;
    if (atomic_type == svt_axi_transaction::NORMAL) {
      burst_type  dist {svt_axi_transaction::INCR :=50, svt_axi_transaction::WRAP:=50, svt_axi_transaction::FIXED:=50}; 
      burst_size <= $clog2(max_bw); //svt_axi_transaction::BURST_SIZE_512BIT;
      if (burst_type == svt_axi_master_transaction::INCR) {
        burst_length inside {[1:256]};
      }
      else {
        //AXI protocol rule for WRAP bursts
        burst_length inside {2,4,8,16};
        (2** burst_size * burst_length) <= 4096;
      }
    }
  }

  //based on AXI protocol section A7.3.3
  constraint exclusive_trans_c {
    if (atomic_type == svt_axi_transaction::EXCLUSIVE) {
      burst_type inside {svt_axi_transaction::INCR, svt_axi_transaction::FIXED, svt_axi_transaction::WRAP};
      if (burst_type == svt_axi_transaction::WRAP)
        burst_length inside {2,4,8,16};
      else
        burst_length inside {[1: 16]};
      burst_size <= svt_axi_transaction::BURST_SIZE_128BIT;
      burst_size <=  $clog2(max_bw);
      burst_length * (1 << burst_size) <= 128;

      xact_type  == svt_axi_transaction::COHERENT;
      coherent_xact_type == svt_axi_transaction::WRITENOSNOOP;
    }
  }

  function void post_randomize();
    int size = 2**burst_size;
    if (atomic_type == svt_axi_transaction::NORMAL && burst_type == svt_axi_transaction::WRAP && cfg_addr % size) begin
      `uvm_info(get_name, $sformatf("WRAP access with unaligned addr: %0h, new alligned addr: %0h", cfg_addr, (cfg_addr/size) * size ), UVM_LOW)
      cfg_addr = (cfg_addr/size) * size;
    end
    //address must be aligned to the total number of bytes in an EXCLUSIVE access transaction
    else if (atomic_type == svt_axi_transaction::EXCLUSIVE) begin
      size = burst_length * 2 ** burst_size * 8;
      cfg_addr -= cfg_addr % size;
      `uvm_info(get_name, $sformatf("Exclusive access, aligned addr: %0h", cfg_addr), UVM_LOW)
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
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_DEBUG);

    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_write_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end


    fork begin
      if (outstanding_req == 0) 
        m_sequencer.lock(this);
      for (int iter = 0; iter < sequence_length; iter++) begin
        int unsigned _bready_delay, _addr_valid_delay;
        _bready_delay     = $urandom_range(max_bready_delay,     min_bready_delay);
        _addr_valid_delay = $urandom_range(max_addr_valid_delay, min_addr_valid_delay);

        uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", iter, sequence_length), UVM_LOW);

        // Set up the write transaction
        `uvm_create(write_tran)
        write_tran.port_cfg       = cfg;
        write_tran.xact_type      = this.xact_type;
        write_tran.addr           = this.cfg_addr;
        write_tran.burst_type     = this.burst_type;
        write_tran.burst_size     = this.burst_size;
        write_tran.burst_length   = this.burst_length;
        write_tran.atomic_type    = this.atomic_type;
        write_tran.coherent_xact_type  = this.coherent_xact_type;
        write_tran.data           = new[write_tran.burst_length];
        write_tran.wstrb          = new[write_tran.burst_length];
        write_tran.id             = trans_id;
        write_tran.cache_type[0]  = cache_bufferable;
        write_tran.cache_type[1]  = cache_modifiable;
        if (write_tran.cache_type[1]) begin
          write_tran.cache_type[2]  = cache_allocate;
          write_tran.cache_type[3]  = cache_other_allocate;
        end else begin
          write_tran.cache_type[2]  = 0;
          write_tran.cache_type[3]  = 0;
        end

        write_tran.prot_type      = burst_prot;
`ifdef SVT_ACE5_ENABLE
        write_tran.mpam_ns        = burst_prot[1]; //TODO: remove after SolvNet issue #01760068 is resolved
`endif
        write_tran.data_user           = new[write_tran.burst_length];
        write_tran.physical_data_user  = new[write_tran.burst_length];
        write_tran.addr_user           = this.addr_user;
        foreach (write_tran.data_user[i])
          write_tran.data_user[i]      = this.data_user;
        foreach (write_tran.physical_data_user[i])
          write_tran.physical_data_user[i]  = this.physical_data_user;
        write_tran.resp_user           = this.resp_user;
        write_tran.qos                 = this.qos; 

        write_tran.data_before_addr = 0;
        write_tran.addr_valid_delay = _addr_valid_delay;
        write_tran.bready_delay = _bready_delay;
        write_tran.wvalid_delay = new[write_tran.burst_length];

        for (int k = 0; k < write_tran.burst_length; k++) begin
          write_tran.wvalid_delay[k] = delay;
        end

        n_bytes = 2**write_tran.burst_size;

        //returns calculated wstrb
        get_wstrb(write_tran, max_bw);

        foreach(write_tran.data[i])
          write_tran.data[i] = cfg_data[i+burst_length*iter];

        `uvm_info("body", $sformatf("write_tran.xact_type = %s,  write_tran.addr = %0x, write_tran.burst_type = %s, write_tran.burst_size = %s, write_tran.burst_length = %d, write_tran.atomic_type = %s", write_tran.xact_type,  write_tran.addr, write_tran.burst_type, write_tran.burst_size, write_tran.burst_length, write_tran.atomic_type), UVM_HIGH);

        `uvm_info(get_type_name(), $sformatf("sending write transaction = \n %s", write_tran.sprint()), UVM_DEBUG);
        // Send the write transaction
        `uvm_send(write_tran)

        written_bytes = written_bytes + write_tran.burst_length * (1 << write_tran.burst_size);
        // aligne and increment address for next transaction
        if (write_tran.burst_type == svt_axi_transaction::FIXED)
          prev_burst_bytes = n_bytes;
        else
          prev_burst_bytes = n_bytes*burst_length;

        cfg_addr = cfg_addr/n_bytes*n_bytes + prev_burst_bytes;
        if (iter + 1 < sequence_length) begin
          if (cfg_addr % 4096 + prev_burst_bytes > 4096) begin
            // adapt burst_len for new address in case address goes out of 4K boundary
            assert(randomize(burst_length) with {
              if (burst_type == svt_axi_master_transaction::FIXED)
                cfg_addr % 4096 + (1<<burst_size) <= 4096;
              else
                cfg_addr % 4096 + burst_length * (1<<burst_size) <= 4096;
              if (burst_type == svt_axi_master_transaction::WRAP) {
                burst_length inside {2,4,8,16};
              }
              else {
                burst_length inside {[1:256]};
              }
            });
          end
        end
      end // end for
      if (outstanding_req == 0) 
        m_sequencer.unlock(this);
    end // send request
    begin //wait response
      if (wait_rsp) begin
        for (int seq_cnt=0; seq_cnt < sequence_length; seq_cnt++) begin
          // Wait for the write transaction to complete /
          `uvm_info("axi_master_write_random_sequence: Body", $sformatf("AXI WRITE wait for response #%0d", seq_cnt), UVM_HIGH);
          get_response(rsp);
          response = rsp;
          if (rsp.get_response_status() == svt_axi_transaction::OKAY)
            `uvm_info("axi_master_write_random_sequence: wait response", $sformatf("AXI WRITE transaction completed #%0d", seq_cnt), UVM_HIGH)
          else if (inj_err == 0)
            `uvm_error("axi_master_write_random_sequence: wait response", $sformatf("RSP %s received for transaction with atomic_type: %s",rsp.get_response_status(), rsp.atomic_type));
        end
      end
    end //wait response
    join
    `uvm_info("axi_master_write_random_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

  function void get_wstrb(ref svt_axi_master_transaction tr, int data_bytes);
    //int data_bytes;
    bit [63:0] lower_byte, upper_byte;
    bit [63:0] lower_lane_boundary, upper_lane_boundary;
    bit [`AXI_HP_ADDR_WIDTH-1:0] aligned_addr;
    bit [`AXI_HP_ADDR_WIDTH-1:0] addr;
    int dtsize;
    bit aligned;
    int size;

    //data_bytes = `HP_STRB_WIDTH;

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

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length;
  rand bit[`AXI_HP_ADDR_WIDTH-1:0]    cfg_addr;
  rand int burst_length;
  rand svt_axi_transaction::burst_size_enum burst_size;
  rand svt_axi_transaction::burst_type_enum burst_type;

  rand svt_axi_transaction::xact_type_enum xact_type;
  rand svt_axi_transaction::atomic_type_enum atomic_type;
  rand svt_axi_transaction::coherent_xact_type_enum coherent_xact_type;

  rand bit cache_bufferable;
  rand bit cache_modifiable;
  rand bit cache_allocate;
  rand bit cache_other_allocate;
  rand bit[2:0] burst_prot;

  rand bit[`AXI_MAX_ADDR_USER_WIDTH  - 1 : 0] addr_user;
  rand bit[`AXI_MAX_DATA_USER_WIDTH  - 1 : 0] data_user;
  rand bit[`AXI_MAX_DATA_USER_WIDTH  - 1 : 0] physical_data_user;
  rand bit[`AXI_MAX_BRESP_USER_WIDTH - 1 : 0] resp_user;

  rand bit[`AXI_QOS_WIDTH - 1 : 0] qos;

`ifndef AXI_ID_WIDTH
  rand bit[3 : 0] trans_id;
`else
  rand bit[`AXI_ID_WIDTH - 1 : 0] trans_id;
`endif
  rand int delay;
  bit  response_received[int];
  int  prev_burst_bytes;

  rand bit wait_rsp;

  svt_axi_master_transaction  response;

  rand bit inj_err;

  // Constrain the sequence length to a reasonable value /
  constraint reasonable_sequence_length {soft sequence_length <= 100;}
  constraint delay_c {delay inside {[0 : `AXI_MAX_DELAY]};}
  constraint wait_rsp_c {soft wait_rsp == 1;}

  // default access type will be NORMAL/READ, but we can use the same sequence for atomic op
  constraint normal_access_c{
    soft atomic_type == svt_axi_transaction::NORMAL;
    soft xact_type   == svt_axi_transaction::READ;
    soft qos == 0;
    soft inj_err == 0;
  }

  constraint valid_operations_c {
    solve atomic_type before xact_type, burst_type, burst_length, burst_size;
    atomic_type inside {svt_axi_transaction::NORMAL, svt_axi_transaction::EXCLUSIVE};
    xact_type   inside {svt_axi_transaction::READ, svt_axi_transaction::COHERENT};
    // calculate 4KB addr limit
    cfg_addr % 4096 + burst_length * (1<<burst_size) <= 4096;
    if (atomic_type == svt_axi_transaction::NORMAL) {
      xact_type != svt_axi_transaction::COHERENT;
    }

  }
  constraint normal_trans_c {
    solve burst_type before burst_length;
    if (atomic_type == svt_axi_transaction::NORMAL) {
`ifndef AXI_DATA_WIDTH
      burst_size <=  svt_axi_transaction::BURST_SIZE_512BIT;
`else
      burst_size <=  $clog2(`AXI_DATA_WIDTH/8);
`endif
      burst_type  dist {svt_axi_transaction::INCR :=50, svt_axi_transaction::WRAP:=50, svt_axi_transaction::FIXED:=50};
      if (burst_type == svt_axi_master_transaction::INCR) {
        burst_length inside {[1:256]};
      }
      else {
        //AXI protocol rule for WRAP bursts
        burst_length inside {2,4,8,16};
        (2** burst_size * burst_length) <= 4096;
      }
    }
  }

  //based on AXI protocol section A7.3.3
  constraint exclusive_trans_c {
    if (atomic_type == svt_axi_transaction::EXCLUSIVE) {
      burst_type inside {svt_axi_transaction::INCR, svt_axi_transaction::FIXED, svt_axi_transaction::WRAP};
      if (burst_type == svt_axi_transaction::WRAP)
        burst_length inside {2,4,8,16};
      else
        burst_length inside {[1: 16]};
      burst_size <= svt_axi_transaction::BURST_SIZE_128BIT;
`ifdef AXI_DATA_WIDTH
      burst_size <= $clog2(`AXI_DATA_WIDTH/8);
`endif
      burst_length * (1 << burst_size) <= 128;

      xact_type  == svt_axi_transaction::COHERENT;
      coherent_xact_type == svt_axi_transaction::READNOSNOOP;
    }
  }

  function void post_randomize();
    int size = 2**burst_size;
    if (atomic_type == svt_axi_transaction::NORMAL && burst_type == svt_axi_transaction::WRAP && cfg_addr % size) begin
      `uvm_info(get_name, $sformatf("WRAP access with unnaligned addr: %0h, new alligned addr: %0h", cfg_addr, (cfg_addr/size) * size ), UVM_LOW)
      cfg_addr = (cfg_addr/size) * size;
    end
    //address must be aligned to the total number of bytes in an EXCLUSIVE access transaction
    else if (atomic_type == svt_axi_transaction::EXCLUSIVE) begin
      size = burst_length * 2 ** burst_size * 8;
      cfg_addr -= cfg_addr % size;
      `uvm_info(get_name, $sformatf("Exclusive access, aligned addr: %0h", cfg_addr), UVM_LOW)
    end


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

  /** Class Constructor */
  function new(string name = "axi_master_read_random_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction read_tran;
    svt_configuration get_cfg;
    bit status;
    `uvm_info("axi_master_read_random_sequence: Body", "Entered", UVM_LOW)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length",sequence_length);
    `uvm_info("body", $sformatf("sequence_length is %0d as a result of %0s.",sequence_length,status ? "config DB" : "randomization"), UVM_DEBUG);

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_read_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    fork
    begin // transmit request
      for (int iter = 0; iter < sequence_length; iter++) begin

        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", iter, sequence_length), UVM_LOW);
        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("cfg_addr: %h, burst_size: %s, burst_length: %d", cfg_addr, burst_size, burst_length), UVM_LOW);
       /** Set up the read transaction */
        `uvm_create(read_tran)
        read_tran.port_cfg        = cfg;
        read_tran.xact_type       = this.xact_type;
        read_tran.addr            = cfg_addr;
        read_tran.burst_type      = this.burst_type;
        read_tran.burst_size      = this.burst_size;
        read_tran.burst_length    = this.burst_length;
        read_tran.id              = this.trans_id;
        read_tran.atomic_type     = this.atomic_type;
        read_tran.coherent_xact_type  = this.coherent_xact_type;
        read_tran.rresp           = new[read_tran.burst_length];
        read_tran.data            = new[read_tran.burst_length];
        read_tran.rready_delay    = new[read_tran.burst_length];
        read_tran.cache_type[0]   = cache_bufferable;
        read_tran.cache_type[1]   = cache_modifiable;
        if (read_tran.cache_type[1]) begin
          read_tran.cache_type[2]   = cache_allocate;
          read_tran.cache_type[3]   = cache_other_allocate;
        end else begin
          read_tran.cache_type[2]   = 0;
          read_tran.cache_type[3]   = 0;
        end

        read_tran.prot_type       = burst_prot;
`ifdef SVT_ACE5_ENABLE
        read_tran.mpam_ns        = burst_prot[1]; //TODO: remove after SolvNet issue #01760068 is resolved
`endif

        read_tran.addr_user           = this.addr_user;
        foreach (read_tran.data_user[i])
          read_tran.data_user[i]      = this.data_user;
        foreach (read_tran.physical_data_user[i])
          read_tran.physical_data_user[i]  = this.physical_data_user;
        read_tran.resp_user           = this.resp_user;
        read_tran.qos                 = this.qos; 

        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = delay;
        end

        `uvm_info(get_type_name(), $sformatf("sending read transaction = \n %s", read_tran.sprint()), UVM_DEBUG);
        /** Send the read transaction */
        `uvm_send(read_tran)
        // increment address for next transaction
        if (read_tran.burst_type == svt_axi_transaction::FIXED)
          prev_burst_bytes = (1<<burst_size);
        else
          prev_burst_bytes = (1<<burst_size)*burst_length;

        cfg_addr = cfg_addr + prev_burst_bytes;
        if (cfg_addr % 4096 + prev_burst_bytes > 4096) begin
          // adapt burst_len for new address in case address goes out of 4K boundary
          if (iter + 1 < sequence_length) begin
            assert(randomize(burst_length) with {
              if (burst_type == svt_axi_master_transaction::FIXED)
                cfg_addr % 4096 + (1<<burst_size) <= 4096;
              else
                cfg_addr % 4096 + burst_length * (1<<burst_size) <= 4096;
              if (burst_type == svt_axi_master_transaction::WRAP) {
                burst_length inside {2,4,8,16};
              }
              else {
                burst_length inside {[1:256]};
              }
            });
          end
        end
      end // end for
    end // send request
    begin // wait for response
      if (wait_rsp == 1) begin
        for (int seq_cnt = 0; seq_cnt < sequence_length; seq_cnt++) begin
          `uvm_info("axi_master_read_random_sequence: Body", $sformatf("AXI READ wait for response #%0d", seq_cnt), UVM_LOW);
          // Wait for the read transaction to complete
          get_response(rsp);
          response = rsp;
          if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
            response_received[seq_cnt] = 1;
            foreach (rsp.data[i]) begin
              `uvm_info("axi_master_read_random_sequence: wait response", $sformatf("rsp.data[%0d] = %0h", i, rsp.data[i]), UVM_DEBUG);
            end
            `uvm_info("axi_master_read_random_sequence: wait response", $sformatf("AXI READ transaction #%0d completed", seq_cnt), UVM_LOW);
          end
          else if (inj_err == 0)
            `uvm_error("axi_master_read_random_sequence: wait response", $sformatf("RSP %s received for transaction with atomic_type: %s",rsp.get_response_status(), rsp.atomic_type));
        end
      end
    end // wait for response
    join
      //rsp.print();
    `uvm_info("axi_master_read_random_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_random_sequence

class axi_dma_write_sequence extends axi_master_write_random_sequence;
  
  // size of DMA write transfer in bytes
  rand int size;
  int delay=0;
 
  rand bit[3:0] trans_id;
  rand bit [`AXI_HP_DATA_WIDTH -1 : 0] axi_data[];
  svt_axi_master_transaction write_tran;

  constraint dma_burst_type_c {this.burst_type == svt_axi_master_transaction::INCR;}
  constraint seq_len_c {sequence_length == 1;}
  constraint dma_axi_data_size_c {
    solve size before axi_data;
    solve burst_size before axi_data;
    axi_data.size == this.size / (1 << this.burst_size);}

  function void post_randomize();
    `uvm_info(get_name, $sformatf("size in bytes: %0d, addr: %x btype: %s, bsize: %s, axi_data.size = %0d",size, cfg_addr, burst_type, burst_size, axi_data.size()), UVM_LOW)
    foreach (axi_data[i])
      `uvm_info(get_name, $sformatf("axi_data[%0d] = %0h", i, axi_data[i]), UVM_DEBUG)
  endfunction

  `uvm_object_utils(axi_dma_write_sequence)
  /** Class Constructor */
  function new(string name = "axi_dma_write_sequence");
    super.new(name);
  endfunction

  virtual task body();

    int written_bytes = 0;
    int n_bytes;
    int write_req_cnt, write_rsp_cnt, burst_length_wr;

    svt_configuration get_cfg;
    bit status;
    `uvm_info("axi_dma_write_sequence: Body", "Entered", UVM_LOW)

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_dma_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    n_bytes = 1 << burst_size;

    fork
      begin // send write request
        while (written_bytes < size) begin
          write_req_cnt++;

          if (cfg_addr % 4096 + axi_data.size() * n_bytes > 4096)
            burst_length_wr = (4096 - cfg_addr % 4096) / n_bytes;
          else
            burst_length_wr = axi_data.size();
          this.cfg_data = new[burst_length_wr];
          for (int i=0; i<burst_length_wr; i++)
            cfg_data[i] = axi_data[i+written_bytes/n_bytes];
          `uvm_info("axi_dma_write_sequence: send write request", $sformatf("Write to address %0h, with burst_size: %0h and burst_length: %0d", cfg_addr,burst_size, burst_length_wr), UVM_LOW)

          // Set up the write transaction
          `uvm_create(write_tran)
          write_tran.port_cfg       = cfg;
          write_tran.xact_type      = svt_axi_transaction::WRITE;
          write_tran.addr           = cfg_addr;
          write_tran.burst_type     = svt_axi_transaction::INCR;
          write_tran.burst_size     = this.burst_size;
          write_tran.burst_length   = burst_length_wr;
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

          //returns calculated wstrb
          get_wstrb(write_tran, max_bw);
          foreach (write_tran.wstrb[i]) begin
            for (int unsigned b = 0; b < n_bytes; b++) begin
              write_tran.data[i][(b+1) *8-1 -: 8]  = cfg_data[i][(b+1)*8-1 -: 8];
            end
            `uvm_info("axi_dma_write_sequence: send write request", $sformatf("wstrb[%0d]: %0h\nwrite_tran.data[%0d]= %0h\ndata[%d]=%0h", i, write_tran.wstrb[i], i, write_tran.data[i], i ,  cfg_data[i]) , UVM_DEBUG) 
          end

          `uvm_info("axi_dma_write_sequence: send write request", $sformatf("write_tran.xact_type = %s,  write_tran.addr = %0x, write_tran.burst_type = %s, write_tran.burst_size = %s, write_tran.burst_length = %d, write_tran.atomic_type = %s", write_tran.xact_type,  write_tran.addr, write_tran.burst_type, write_tran.burst_size, write_tran.burst_length, write_tran.atomic_type), UVM_DEBUG);

          `uvm_info(get_type_name(), $sformatf("sending write transaction = \n %s", write_tran.sprint()), UVM_DEBUG);
          `uvm_send(write_tran)

          // aligne and increment address for next transaction and increment written_bytes
          written_bytes = written_bytes + write_tran.burst_length * (1 << write_tran.burst_size);
          cfg_addr = cfg_addr/n_bytes*n_bytes + n_bytes*write_tran.burst_length;
          `uvm_info("axi_dma_write_sequence: send write request", $sformatf("written %0d bytes of %0d, next address is %0h", written_bytes, size, cfg_addr), UVM_LOW);
        end // end while 
      end // send write request

      begin //wait write response
        while (write_rsp_cnt < write_req_cnt || write_rsp_cnt == 0) begin
          // Wait for the write transaction to complete
          `uvm_info("axi_dma_write_sequence: wait write response", $sformatf("AXI WRITE wait for response #%0d", write_rsp_cnt + 1), UVM_LOW);
          get_response(rsp);
          if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
            write_rsp_cnt++;
            `uvm_info("axi_dma_write_sequence: wait write response", $sformatf("AXI WRITE transaction completed #%0d", write_rsp_cnt), UVM_LOW);
          end
          else
            `uvm_error("axi_dma_write_sequence: wait write response", "Error reponse received!");
        end
      end //wait write response
    join
    `uvm_info("axi_dma_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_dma_write_sequence

class axi_dma_read_sequence extends axi_master_read_random_sequence;

  // size of DMA read transfer in bytes
  rand int size;

  constraint dma_burst_type_c {this.burst_type == svt_axi_master_transaction::INCR;}
  constraint seq_len_c {sequence_length == 1;}

  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, size: %0d", cfg_addr, burst_type, burst_size, size), UVM_LOW)
  endfunction

  `uvm_object_utils(axi_dma_read_sequence)
  /** Class Constructor */
  function new(string name = "axi_dma_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction read_tran;
    svt_configuration get_cfg;
    bit status;
    int rd_req_cnt = 0;
    int rd_rsp_cnt = 0;
    `uvm_info("axi_dma_read_sequence: Body", "Entered", UVM_LOW)

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_dma_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    fork
    begin // transmit request
      while (this.size > 0) begin

        if (size > 4096 || (cfg_addr % 4096 + size >= 4096))
          burst_length = (4096 - cfg_addr % 4096) / (1 << this.burst_size);
        else
          burst_length = size/(1<<this.burst_size);
        if (burst_length > 256)
          burst_length = 256; 

        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d", (rd_req_cnt+1)), UVM_LOW);
        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("size: %0d, cfg_addr: %h, burst_size: %s, burst_length: %d", this.size, this.cfg_addr, this.burst_size, this.burst_length), UVM_LOW);
       // Set up the read transaction
        `uvm_create(read_tran)
        read_tran.port_cfg        = cfg;
        read_tran.xact_type       = svt_axi_transaction::READ;
        read_tran.addr            = cfg_addr;
        read_tran.burst_type      = svt_axi_transaction::INCR;
        read_tran.burst_size      = this.burst_size;
        read_tran.burst_length    = this.burst_length;
        read_tran.id              = this.trans_id;
        read_tran.atomic_type     = svt_axi_transaction::NORMAL;
        read_tran.rresp           = new[read_tran.burst_length];
        read_tran.data            = new[read_tran.burst_length];
        read_tran.rready_delay    = new[read_tran.burst_length];

        read_tran.data_before_addr = 0;
        read_tran.addr_valid_delay = 0;
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = this.delay;
        end

        `uvm_info(get_type_name(), $sformatf("sending read transaction = \n %s", read_tran.sprint()), UVM_DEBUG);
        // Send the read transaction
        `uvm_send(read_tran)
        // increment address for next transaction
        cfg_addr = cfg_addr + 2**read_tran.burst_size*read_tran.burst_length;
        this.size = this.size - 2**read_tran.burst_size*read_tran.burst_length;
        rd_req_cnt++;
      end // end while
    end // send request
    begin // wait for response
      while (rd_rsp_cnt < rd_req_cnt || rd_rsp_cnt == 0) begin
        `uvm_info("axi_dma_read_sequence: Body", $sformatf("AXI READ wait for response #%0d", rd_rsp_cnt+1), UVM_LOW);
        /** Wait for the read transaction to complete */
        get_response(rsp);
        if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          response_received[rd_rsp_cnt] = 1;
          rd_rsp_cnt++;
          foreach (rsp.data[i]) begin
            `uvm_info("axi_dma_read_sequence: wait response", $sformatf("rsp.data[%0d] = %0h", i, rsp.data[i]), UVM_DEBUG);
          end
          `uvm_info("axi_dma_read_sequence: wait response", $sformatf("AXI READ transaction #%0d completed", rd_rsp_cnt), UVM_LOW);
        end
        else
          `uvm_error("axi_dma_read_sequence: wait response", "Error reponse received!");
      end
    end // wait for response
    join

    `uvm_info("axi_dma_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_dma_read_sequence

///////////////////////////////////////////////////////////////////
// axi_dma_sequence
// 1. send number of increment burst read transactions
//    staring from src_addr until size bytes of data is read
// 2. wait for read response and put data into buffer
// 3. get data from buffer and send number of write transactions
//    to dst_addr until size bytes of data are written
///////////////////////////////////////////////////////////////////

class axi_dma_sequence extends svt_axi_master_base_sequence;

  axi_dma_read_sequence rd_seq;
  rand bit [`AXI_HP_ADDR_WIDTH-1:0] src_addr;
  rand bit [`AXI_HP_ADDR_WIDTH-1:0] dst_addr;
  rand int size;
  rand int delay;
  rand bit [3:0] trans_id;
  rand svt_axi_transaction::burst_size_enum burst_size;

  bit [`AXI_HP_DATA_WIDTH-1:0] read_buffer[$];
  bit [`AXI_HP_DATA_WIDTH-1:0] rd_data[];

  svt_axi_master_transaction write_tran;

  `uvm_object_utils(axi_dma_sequence)

  constraint delay_c {delay inside {[0: `AXI_MAX_DELAY]};}

  // Class Constructor 
  function new(string name = "axi_dma_sequence");
    super.new(name);
    rd_seq = axi_dma_read_sequence::type_id::create("rd_seq");
  endfunction

  virtual task body();
    int written_bytes = 0;
    int n_bytes;
    int write_req_cnt, write_rsp_cnt, rd_rsp_cnt, burst_length_wr;

    `uvm_info("axi_dma_sequence: Body", "Entered", UVM_LOW)

    `uvm_info("axi_dma_sequence: Body",$sformatf("size: %0h, burst_size: %0h, src_addr: %0h, dst_addr: %0h", size, this.burst_size,this.src_addr, this.dst_addr), UVM_LOW)
    n_bytes = 1 << burst_size;

    fork : dma_seq
    begin
      assert(rd_seq.randomize() with {
          cfg_addr        == local::src_addr;
          delay           == local::delay;
          burst_size      == local::burst_size;
          size            == local::size;
        });
      rd_seq.start(null,this);
    end
    begin
      while (1) begin
        @rd_seq.response_received[rd_rsp_cnt]; // FIXME: check ID
        if (rd_seq.rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          foreach (rd_seq.rsp.data[i]) begin
            read_buffer.push_back(rd_seq.rsp.data[i]);
            `uvm_info("axi_dma_sequence: Body",$sformatf("Push back data: %0h", rd_seq.rsp.data[i]), UVM_DEBUG)
          end
        end else begin
          `uvm_error("axi_dma_sequence: get read response", "Error reponse received!");
        end
        rd_rsp_cnt++;
      end
    end

    begin // send write request
      while (written_bytes < size) begin
        write_req_cnt++;
        `uvm_info("axi_dma_sequence: send write request", "Wait for read data!", UVM_LOW);
        wait (read_buffer.size() > 0);

        if (this.dst_addr % 4096 + read_buffer.size() * (1 << burst_size) > 4096)
          burst_length_wr = (4096 - this.dst_addr % 4096) / (1 << burst_size);
        else
          burst_length_wr = read_buffer.size();

        `uvm_info("axi_dma_sequence: send write request", $sformatf("Address increment would cross 4K boundary! New address is %0h, and burst_length is %0h", dst_addr, burst_length_wr), UVM_DEBUG);

        rd_data = new[burst_length_wr];

        foreach (rd_data[i]) //FIXME: add limitation so we don't cross 4K boundary
          rd_data[i] = read_buffer.pop_front();
        `uvm_info("axi_dma_sequence: send write request", "Received read data!", UVM_LOW);
        `uvm_info("axi_dma_sequence: send write request", $sformatf("Rd buffer size: %0d, Rd_data size: %0d",read_buffer.size(), rd_data.size()) , UVM_DEBUG);

        // Set up the write transaction
        `uvm_create(write_tran)
        write_tran.port_cfg       = cfg;
        write_tran.xact_type      = svt_axi_transaction::WRITE;
        write_tran.addr           = this.dst_addr;
        write_tran.burst_type     = svt_axi_transaction::INCR;
        write_tran.burst_size     = this.burst_size;
        write_tran.burst_length   = burst_length_wr;
        write_tran.atomic_type    = svt_axi_transaction::NORMAL;
        write_tran.data           = new[write_tran.burst_length];
        write_tran.wstrb          = new[write_tran.burst_length];
        write_tran.id             = trans_id;
       
        write_tran.data_before_addr = 0;
        write_tran.addr_valid_delay = 0;
        write_tran.bready_delay = 0;
        write_tran.wvalid_delay = new[write_tran.burst_length];

        for (int k = 0; k < write_tran.burst_length; k++) begin
          write_tran.wvalid_delay[k] = this.delay;
        end

        n_bytes = 2**write_tran.burst_size;

        //returns calculated wstrb
        get_wstrb(write_tran);
        foreach (write_tran.wstrb[i]) begin
          for (int unsigned b = 0; b < n_bytes; b++) begin
            write_tran.data[i][(b+1) *8-1 -: 8]  = rd_data[i][(b+1)*8-1 -: 8];
          end
          `uvm_info("axi_dma_sequence: send write request", $sformatf("wstrb[%0d]: %0h\nwrite_tran.data[%0d]= %0h\ndata[%d]=%0h", i, write_tran.wstrb[i], i, write_tran.data[i], i ,  rd_data[i]) , UVM_DEBUG) 
        end

        `uvm_info("axi_dma_sequence: send write request", $sformatf("write_tran.xact_type = %s,  write_tran.addr = %0x, write_tran.burst_type = %s, write_tran.burst_size = %s, write_tran.burst_length = %d, write_tran.atomic_type = %s", write_tran.xact_type,  write_tran.addr, write_tran.burst_type, write_tran.burst_size, write_tran.burst_length, write_tran.atomic_type), UVM_DEBUG);

        `uvm_info(get_type_name(), $sformatf("sending write transaction = \n %s", write_tran.sprint()), UVM_DEBUG);
        `uvm_send(write_tran)

        // aligne and increment address for next transaction and increment written_bytes
        written_bytes = written_bytes + write_tran.burst_length * (1 << write_tran.burst_size);
        dst_addr = dst_addr/n_bytes*n_bytes + n_bytes*write_tran.burst_length;
        `uvm_info("axi_dma_sequence: send write request", $sformatf("written %0d bytes of %0d, next address is %0h", written_bytes, size, dst_addr), UVM_LOW);

      end // end while 
    end // send write request

    begin //wait write response
      while (write_rsp_cnt < write_req_cnt || write_rsp_cnt == 0) begin
        // Wait for the write transaction to complete
        `uvm_info("axi_dma_sequence: wait write response", $sformatf("AXI WRITE wait for response #%0d", write_rsp_cnt + 1), UVM_LOW);
        get_response(rsp);
        if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          write_rsp_cnt++;
          `uvm_info("axi_dma_sequence: wait write response", $sformatf("AXI WRITE transaction completed #%0d", write_rsp_cnt), UVM_LOW);
        end
        else
          `uvm_error("axi_dma_sequence: wait write response", "Error reponse received!");
      end
      disable dma_seq;
    end //wait write response

    join

    `uvm_info("axi_dma_sequence: Body", "Exiting", UVM_LOW)
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

endclass : axi_dma_sequence

class axi_cac_read_sequence extends axi_master_read_random_sequence;

  // size of cache in bytes
  rand int size;
  rand svt_axi_transaction::burst_size_enum bandwidth;

  int rd_req_cnt = 0;
  int rd_rsp_cnt = 0;

  constraint cac_burst_size_c {this.burst_size == this.bandwidth;}
  constraint cac_burst_type_c {this.burst_type == svt_axi_master_transaction::WRAP;}

  function void post_randomize();
    super.post_randomize();
    `uvm_info(get_name, $sformatf("addr: %x btype: %s, bsize: %s, blen: %0d, size: %0d", cfg_addr, burst_type, burst_size, burst_length, size), UVM_LOW)
  endfunction

  `uvm_object_utils(axi_cac_read_sequence)
  /** Class Constructor */
  function new(string name = "axi_cac_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
    svt_configuration get_cfg;
    bit status;
    `uvm_info("axi_cac_read_sequence: Body", "Entered", UVM_LOW)

    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_cac_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    fork
    begin // transmit request
      while (this.size > 0) begin

        burst_length = 16; // set max possible value
        while (this.cfg_addr % 4096 + burst_length * (1 << bandwidth) > 4096 || this.size < burst_length * (1 << bandwidth))
          burst_length = burst_length / 2;
        if (this.cfg_addr % 4096 + burst_length * (1 << bandwidth) > 4096) begin
            `uvm_info("axi_cac_read_sequence: ", $sformatf("Can not solve address(%0h) bandwidth(%s) and size(%0h)", this.cfg_addr, bandwidth, this.size), UVM_LOW);
            `uvm_fatal("axi_cac_read_sequence: ", "Address is not properlly aligned! Can not solve burst length!");
        end

        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d", (rd_req_cnt+1)), UVM_LOW);
        uvm_report_info("AXI_MST_RD_SEQ", $psprintf("size: %0d, cfg_addr: %h, burst_size: %s, burst_length: %d", this.size, this.cfg_addr, this.burst_size, this.burst_length), UVM_LOW);
       // Set up the read transaction
        `uvm_create(read_tran)
        read_tran.port_cfg        = cfg;
        read_tran.xact_type       = svt_axi_transaction::READ;
        read_tran.addr            = cfg_addr;
        read_tran.burst_type      = svt_axi_transaction::WRAP;
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

        `uvm_info(get_type_name(), $sformatf("sending read transaction = \n %s", read_tran.sprint()), UVM_DEBUG);
        // Send the read transaction
        `uvm_send(read_tran)
        // increment address for next transaction
        cfg_addr = cfg_addr + 2**read_tran.burst_size*read_tran.burst_length;
        this.size = this.size - 2**read_tran.burst_size*read_tran.burst_length;
        rd_req_cnt++;
      end // end while
    end // send request
    begin // wait for response
      while (rd_rsp_cnt < rd_req_cnt || rd_rsp_cnt == 0) begin
        `uvm_info("axi_cac_read_sequence: Body", $sformatf("AXI READ wait for response #%0d", rd_rsp_cnt+1), UVM_LOW);
        // Wait for the read transaction to complete
        get_response(rsp);
        if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          response_received[rd_rsp_cnt] = 1;
          rd_rsp_cnt++;
          foreach (rsp.data[i]) begin
            `uvm_info("axi_cac_read_sequence: wait response", $sformatf("rsp.data[%0d] = %0h", i, rsp.data[i]), UVM_DEBUG);
          end
          `uvm_info("axi_cac_read_sequence: wait response", $sformatf("AXI READ transaction #%0d completed", rd_rsp_cnt), UVM_LOW);
        end
        else
          `uvm_error("axi_cac_read_sequence: wait response", "Error reponse received!");
      end
    end // wait for response
    join

    `uvm_info("axi_cac_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_cac_read_sequence

///////////////////////////////////////////////////////////////////
// axi_cac_sequence
// 1. send number of wrap burst read transactions
//    staring from src_addr until size bytes of data is read
// 2. wait for read response and put data into buffer
// 3. get data from buffer and send number of write transactions
//    to dst_addr until size bytes of data are written
///////////////////////////////////////////////////////////////////

class axi_cac_sequence extends svt_axi_master_base_sequence;

  rand bit [`AXI_HP_ADDR_WIDTH-1:0] src_addr;
  rand bit [`AXI_HP_ADDR_WIDTH-1:0] dst_addr;
  rand svt_axi_transaction::burst_size_enum bandwidth;
  rand int burst_length;
  rand int size;
  rand int delay;
  rand bit [3:0] trans_id;
  rand bit reorder_data;
 
  bit [`AXI_HP_DATA_WIDTH-1:0] read_buffer[$];
  bit [`AXI_HP_DATA_WIDTH-1:0] tmp[];
  bit [`AXI_HP_DATA_WIDTH-1:0] rd_data[];
  bit [`AXI_HP_DATA_WIDTH-1:0] addrN;
  int written_bytes = 0;
  int n_bytes, wb, wrap_index;
  int write_req_cnt, write_rsp_cnt, rd_rsp_cnt, burst_length_wr;

  axi_cac_read_sequence rd_seq;

  svt_axi_master_transaction write_tran;

  `uvm_object_utils(axi_cac_sequence)

  // cache size must be mutilple of burst size 
  // cache line size is multiple of burst size

  constraint cac_size_c {
    size % (1 <<  bandwidth) == 0;
  }

  constraint cac_size_len_bw_c {
    burst_length inside {2,4,8,16};
    (src_addr % 4096 + (1 << bandwidth) * burst_length) <= 4096;
  }
  constraint delay_c {delay inside {[0: `AXI_MAX_DELAY]};}

  // Class Constructor 
  function new(string name = "axi_cac_sequence");
    super.new(name);
    rd_seq = axi_cac_read_sequence::type_id::create("rd_seq");
  endfunction

  virtual task body();
    `uvm_info("axi_cac_sequence: Body", "Entered", UVM_LOW)

    `uvm_info("axi_cac_sequence: Body",$sformatf("burst_length: %0h, size: %0h, bandwidth: %0h, src_addr: %0h, dst_addr: %0h, delay: %0d",  this.burst_length, size, bandwidth,this.src_addr, this.dst_addr, delay), UVM_LOW)
    n_bytes = 1 << bandwidth;

    fork : cac_seq
    begin
      assert(rd_seq.randomize() with {
          cfg_addr        == local::src_addr;
          delay           == local::delay;
          burst_size      == local::bandwidth;
          size            == local::size;
        });
      rd_seq.start(null,this);
    end
    begin
      while (1) begin
        @rd_seq.response_received[rd_rsp_cnt];
        if (rd_seq.rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          wb = (rd_seq.rsp.addr / (n_bytes * rd_seq.rsp.burst_length)) * n_bytes * rd_seq.rsp.burst_length;
          addrN = wb + n_bytes * rd_seq.rsp.burst_length;
          wrap_index = rd_seq.rsp.burst_length - ((addrN - rd_seq.rsp.addr) / n_bytes);
          `uvm_info("axi_cac_sequence: send write request", $sformatf("Reorder buffer data! Wrap boundary: %0h, Start Addr: %0h, AddrN %0h, wrap index: %0d", wb, rd_seq.rsp.addr, addrN, wrap_index) , UVM_DEBUG)
          tmp = new[rd_seq.rsp.burst_length]; 
          if (reorder_data && wrap_index < rd_seq.rsp.burst_length) begin
            //reorder data in buffer
            foreach (rd_seq.rsp.data[k]) begin
              if (k < rd_seq.rsp.burst_length - wrap_index)
                tmp[k+wrap_index] = rd_seq.rsp.data[k];
              else
                tmp[k-rd_seq.rsp.burst_length+wrap_index] = rd_seq.rsp.data[k];
            end
            foreach (tmp[i]) begin
              read_buffer.push_back(tmp[i]);
              `uvm_info("axi_cac_sequence: Body" , $sformatf("Push back data: %0h, read_buffer size is: %0d", read_buffer[i], read_buffer.size()), UVM_DEBUG)
            end
          end
          else
            foreach (rd_seq.rsp.data[i]) begin
              read_buffer.push_back(rd_seq.rsp.data[i]);
              `uvm_info("axi_cac_sequence: Body" , $sformatf("Push back data: %0h, read_buffer size is: %0d", rd_seq.rsp.data[i], read_buffer.size()), UVM_DEBUG)
            end
        end else begin
          `uvm_error("axi_cac_sequence: get read response", "Error reponse received!");
        end
        rd_rsp_cnt++;
      end
    end

    begin // send write request
      while (written_bytes < size) begin
        write_req_cnt++;
        `uvm_info("axi_cac_sequence: send write request", "Wait for read data!", UVM_LOW);
        wait (read_buffer.size() >= 2);

        burst_length_wr = 16; // set max possible value
        while (burst_length_wr > read_buffer.size()) begin
          burst_length_wr = burst_length_wr / 2;
        end
        while (burst_length_wr > 2 && (this.dst_addr % 4096 + burst_length_wr * (1 << bandwidth) > 4096)) begin
            burst_length_wr = burst_length_wr / 2;
        end
        if (this.dst_addr % 4096 + burst_length_wr * (1 << bandwidth) > 4096)
          `uvm_fatal("axi_cac_sequence: write data ", "Destination address is not properlly aligned! Can not solve burst length!");

        `uvm_info("axi_cac_sequence: send write request", $sformatf("Received data! read_buffer size is %0d, burst length is %0d", read_buffer.size(), burst_length_wr) , UVM_LOW) 
        rd_data = new[this.burst_length_wr];

        foreach (rd_data[i]) begin 
          rd_data[i] = read_buffer.pop_front();
          `uvm_info("axi_cac_sequence: send write request", $sformatf("Received read data! rd_data[%0d] = %0h",i, rd_data[i]), UVM_DEBUG);
        end

        // Set up the write transaction
        `uvm_create(write_tran)
        write_tran.port_cfg       = cfg;
        write_tran.xact_type      = svt_axi_transaction::WRITE;
        write_tran.addr           = this.dst_addr;
        write_tran.burst_type     = svt_axi_transaction::WRAP;
        write_tran.burst_size     = this.bandwidth;
        write_tran.burst_length   = this.burst_length_wr;
        write_tran.atomic_type    = svt_axi_transaction::NORMAL;
        write_tran.data           = new[write_tran.burst_length];
        write_tran.wstrb          = new[write_tran.burst_length];
        write_tran.id             = trans_id;
       
        write_tran.data_before_addr = 0;
        write_tran.addr_valid_delay = 0;
        write_tran.bready_delay = 0;
        write_tran.wvalid_delay = new[write_tran.burst_length];

        for (int k = 0; k < write_tran.burst_length; k++) begin
          write_tran.wvalid_delay[k] = this.delay;
        end

        n_bytes = 2**write_tran.burst_size;

        //returns calculated wstrb
        get_wstrb(write_tran);
        foreach (write_tran.wstrb[i]) begin
          for (int unsigned b = 0; b < n_bytes; b++) begin
            write_tran.data[i][(b+1) *8-1 -: 8]  = rd_data[i][(b+1)*8-1 -: 8];
          end
          `uvm_info("axi_cac_sequence: send write request", $sformatf("wstrb[%0d]: %0h\nwrite_tran.data[%0d]= %0h\ndata[%d]=%0h", i, write_tran.wstrb[i], i, write_tran.data[i], i ,  rd_data[i]) , UVM_DEBUG) 
        end

        `uvm_info("axi_cac_sequence: send write request", $sformatf("write_tran.xact_type = %s,  write_tran.addr = %0x, write_tran.burst_type = %s, write_tran.burst_size = %s, write_tran.burst_length = %d, write_tran.atomic_type = %s", write_tran.xact_type,  write_tran.addr, write_tran.burst_type, write_tran.burst_size, write_tran.burst_length, write_tran.atomic_type), UVM_LOW);

        `uvm_info(get_type_name(), $sformatf("sending write transaction = \n %s", write_tran.sprint()), UVM_DEBUG);
        `uvm_send(write_tran)

        // aligne and increment address for next transaction and increment written_bytes
        written_bytes = written_bytes + write_tran.burst_length * (1 << write_tran.burst_size);
        dst_addr = dst_addr/n_bytes*n_bytes + n_bytes*write_tran.burst_length;
        `uvm_info("axi_cac_sequence: send write request", $sformatf("written %0d bytes of %0d, next address is %0h", written_bytes, size, dst_addr), UVM_LOW);

      end // end while 
    end // send write request

    begin //wait write response
      while (write_rsp_cnt < write_req_cnt || write_rsp_cnt == 0) begin
        // Wait for the write transaction to complete /
        `uvm_info("axi_cac_sequence: wait write response", $sformatf("AXI WRITE wait for response #%0d", write_rsp_cnt + 1), UVM_LOW);
        get_response(rsp);
        if (rsp.get_response_status() == svt_axi_transaction::OKAY) begin
          write_rsp_cnt++;
          `uvm_info("axi_cac_sequence: wait write response", $sformatf("AXI WRITE transaction completed #%0d", write_rsp_cnt), UVM_LOW);
        end
        else
          `uvm_error("axi_cac_sequence: wait write response", "Error reponse received!");
      end
      disable cac_seq;
    end //wait write response

    join

    `uvm_info("axi_cac_sequence: Body", "Exiting", UVM_LOW)
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

endclass : axi_cac_sequence

`ifdef SVT_ACE5_ENABLE
class cust_atomic_seq extends svt_axi_master_base_sequence;
  svt_axi_master_transaction at_tran;
  rand svt_axi_transaction::atomic_transaction_type_enum atomic_transaction_type;

  rand svt_axi_transaction::atomic_xact_op_type_enum atomic_xact_load_type;
  rand svt_axi_transaction::atomic_xact_op_type_enum atomic_xact_store_type;

  rand svt_axi_transaction::atomic_xact_op_type_enum atomic_xact_op_type;

  rand bit[`SVT_AXI_MAX_ADDR_WIDTH -1:0] _addr;

  bit [`SVT_AXI_MAX_DATA_WIDTH - 1:0] orig_data[int];
  bit [`SVT_AXI_MAX_DATA_WIDTH - 1:0] res_data[int], atomic_data[int];
  bit [`SVT_AXI_MAX_DATA_WIDTH / 8 -1 : 0] atomic_wstrb[int];

  /** UVM Object Utility macro */
  `uvm_object_utils(cust_atomic_seq)

  /** Constrain the atomic_xact_op_type to a reasonable value for atomicstore */
  constraint atomic_xact_op_type_for_atomicstore {
    atomic_xact_store_type inside {
       svt_axi_transaction::ATOMICSTORE_ADD,
       svt_axi_transaction::ATOMICSTORE_CLR,
       svt_axi_transaction::ATOMICSTORE_EOR,
       svt_axi_transaction::ATOMICSTORE_SET,
       svt_axi_transaction::ATOMICSTORE_SMAX,
       svt_axi_transaction::ATOMICSTORE_SMIN,
       svt_axi_transaction::ATOMICSTORE_UMAX,
       svt_axi_transaction::ATOMICSTORE_UMIN
    };
  }
  /** Constrain the atomic_xact_op_type to a reasonable value for atomicload */
  constraint atomic_xact_op_type_for_atomicload {
    atomic_xact_load_type inside {
       svt_axi_transaction::ATOMICLOAD_ADD,
       svt_axi_transaction::ATOMICLOAD_CLR,
       svt_axi_transaction::ATOMICLOAD_EOR,
       svt_axi_transaction::ATOMICLOAD_SET,
       svt_axi_transaction::ATOMICLOAD_SMAX,
       svt_axi_transaction::ATOMICLOAD_SMIN,
       svt_axi_transaction::ATOMICLOAD_UMAX,
       svt_axi_transaction::ATOMICLOAD_UMIN
    };
  }

  /** Class Constructor */
  function new(string name="cust_atomic_seq");
    super.new(name);
  endfunction

  virtual task body();
    bit status;
    svt_configuration get_cfg;
    int unsigned atomic_xact_type=0;
    `uvm_info("cust_atomic_seq", "Entered...", UVM_LOW);
    super.body();
    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_write_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    case (this.atomic_transaction_type)
       svt_axi_transaction::LOAD    : begin
                   `uvm_info("cust_atomic_seq",$sformatf( "operation: LOAD (%s)", this.atomic_xact_load_type), UVM_LOW);
                   atomic_xact_op_type = this.atomic_xact_load_type;
                 end
       svt_axi_transaction::STORE   : begin
                   `uvm_info("cust_atomic_seq", $sformatf( "operation: STORE (%s)", this.atomic_xact_store_type), UVM_LOW);
                   atomic_xact_op_type = this.atomic_xact_store_type;
                 end
       svt_axi_transaction::SWAP    : begin
                   `uvm_info("cust_atomic_seq", "SWAP", UVM_LOW);
                   atomic_xact_op_type = svt_axi_transaction::ATOMICSWAP;
                   `uvm_info("cust_atomic_seq", $sformatf( "operation: SWAP (%s)", this.atomic_xact_op_type), UVM_LOW);
                 end
       svt_axi_transaction::COMPARE : begin
                   `uvm_info("cust_atomic_seq", "COMPARE", UVM_LOW);
                   atomic_xact_op_type = svt_axi_transaction::ATOMICCOMPARE;
                   `uvm_info("cust_atomic_seq", $sformatf( "operation: COMPARE (%s)", this.atomic_xact_op_type), UVM_LOW);
                 end
    endcase

    `uvm_do_with(req,
       {
         xact_type == svt_axi_transaction::WRITE;
         burst_size == svt_axi_transaction::BURST_SIZE_32BIT;
         addr == _addr;
         burst_length == 2;
         data_before_addr == 0;
         cache_type == 0;
         atomic_type == svt_axi_transaction::NORMAL;
       })
    get_response(rsp);
    `uvm_do_with(req,
       {
         xact_type == svt_axi_transaction::READ;
         burst_size == svt_axi_transaction::BURST_SIZE_32BIT;
         addr == _addr;
         burst_length == 2;
         data_before_addr == 0;
         cache_type == 0;
         atomic_type == svt_axi_transaction::NORMAL;
       })
    get_response(rsp);

    foreach(rsp.data[i])
      orig_data[i] = rsp.data[i];

    `uvm_do_with(req,
       {
         xact_type == svt_axi_transaction::ATOMIC;
         atomic_transaction_type == local::atomic_transaction_type;
         atomic_xact_op_type == local::atomic_xact_op_type;
         addr == _addr;
         data_before_addr == 0;
       })

    foreach (req.data[i]) begin
      `uvm_info("cust_atomic_seq", $sformatf("req.wdata[%0d] = %0h\nreq.wstrb[%0d] = %0h", i, req.data[i], i, req.wstrb[i]), UVM_LOW);
      atomic_data[i] = req.data[i];
      atomic_wstrb[i] = req.wstrb[i];
    end

    `uvm_info("cust_atomic_seq", "Wait for atomic resp...", UVM_LOW);
    get_response(rsp);
    if (atomic_transaction_type != svt_axi_transaction::STORE) begin
      `uvm_info("cust_atomic_seq", "Wait for atomic resp again...", UVM_LOW);
      get_response(rsp);
    end

    `uvm_do_with(req,
       {
         xact_type == svt_axi_transaction::READ;
         burst_size == svt_axi_transaction::BURST_SIZE_32BIT;
         addr == _addr;
         burst_length == 2;
         data_before_addr == 0;
         cache_type == 0;
         atomic_type == svt_axi_transaction::NORMAL;
       })
    get_response(rsp);
    foreach(rsp.data[i])
      res_data[i] = rsp.data[i];

    `uvm_info("cust_atomic_seq", "Exiting...", UVM_LOW);
  endtask: body

endclass: cust_atomic_seq
`endif
