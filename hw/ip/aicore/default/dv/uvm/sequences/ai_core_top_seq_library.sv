// AXI master write sequence
class axi_master_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[`AXI_LP_ADDR_WIDTH-1:0]    cfg_addr;
  rand bit[`AXI_LP_DATA_WIDTH-1:0]    cfg_data[];
  rand bit[3:0]    cache_type;
  rand burst_size_enum burst_size_enum_t;
  rand burst_type_enum burst_type_enum_t;
  rand burst_lenght_enum burst_lenght_enum_t;
  rand bit wait_for_response_for_write = 1;
  svt_axi_master_transaction write_transaction;
  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint data_c {cfg_data.size == int'(burst_lenght_enum_t);}
   /** Constrain the wait_for_response_for_write */
  constraint default_wait_for_response_for_write {soft wait_for_response_for_write == 1;}

 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_write_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_int(cache_type,UVM_ALL_ON)
    `uvm_field_sarray_int(cfg_data,UVM_ALL_ON)
    `uvm_field_enum(burst_size_enum,burst_size_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_type_enum,burst_type_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_lenght_enum, burst_lenght_enum_t,UVM_ALL_ON)
  `uvm_object_utils_end
  /** Class Constructor */
  function new(string name = "axi_master_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
    svt_configuration get_cfg;
    bit status;
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
      write_tran.port_cfg    = cfg;
      write_tran.xact_type   = svt_axi_transaction::WRITE;
      write_tran.addr        = cfg_addr;
      write_tran.cache_type  = this.cache_type;
      write_tran.burst_type  = int'(burst_type_enum_t);
      write_tran.burst_size  = int'(burst_size_enum_t);
      write_tran.burst_length = int'(burst_lenght_enum_t);
      write_tran.data      = new[write_tran.burst_length];
      write_tran.wstrb     = new[write_tran.burst_length];
      write_tran.data_user = new[write_tran.burst_length];
      foreach (write_tran.data[i]) begin
        write_tran.data[i] = this.cfg_data[i];
      end
      foreach (write_tran.wstrb[i]) begin
        if(write_tran.burst_type==svt_axi_transaction::FIXED)
         write_tran.wstrb[i] = '1;
         else 
         write_tran.wstrb[i] = 'hFF;
        end 
      write_tran.wvalid_delay = new[write_tran.burst_length];
      foreach (write_tran.wvalid_delay[i]) begin
        write_tran.wvalid_delay[i] = wait_for_response_for_write ? $urandom_range(0,10):0;
      end

      /** Send the write transaction */
      `uvm_send(write_tran)
      /** Wait for the write transaction to complete */
       if(wait_for_response_for_write==1)begin
       get_response(rsp); 
      end

       write_transaction = write_tran;
       uvm_report_info(get_type_name(), $psprintf("axi_master_write_sequence: Body write_transaction = \n %s", write_transaction.sprint()), UVM_LOW);
    end // end for
    `uvm_info("axi_master_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_write_sequence

// AXI master read sequence
class axi_master_read_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[`AXI_LP_ADDR_WIDTH-1:0]    cfg_addr;
  rand int burst_length = 1;
  rand burst_size_enum burst_size_enum_t;
  rand burst_type_enum burst_type_enum_t;
  rand burst_lenght_enum burst_lenght_enum_t;
  rand bit wait_for_response_for_read = 1;
  svt_axi_master_transaction  read_transaction;

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
   /** Constrain the wait_for_response_for_read */
  constraint default_wait_for_response_for_read {soft wait_for_response_for_read == 1;}


  /** UVM Object Utility macro */
  `uvm_object_utils(axi_master_read_sequence)

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
      read_tran.port_cfg    = cfg;
      read_tran.xact_type   = svt_axi_transaction::READ;
      read_tran.addr        = cfg_addr;
      read_tran.burst_type  = int'(burst_type_enum_t);
      read_tran.burst_size  = int'(burst_size_enum_t);
      read_tran.atomic_type = svt_axi_transaction::NORMAL;
      read_tran.burst_length = int'(burst_lenght_enum_t);
      read_tran.rresp        = new[read_tran.burst_length];
      read_tran.data         = new[read_tran.burst_length];
      read_tran.rready_delay = new[read_tran.burst_length];
      read_tran.data_user    = new[read_tran.burst_length];

      foreach (read_tran.rready_delay[i]) begin
        read_tran.rready_delay[i] = wait_for_response_for_read ? $urandom_range(0,10):0;
      end

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      if(wait_for_response_for_read==1)begin
       get_response(rsp); 
      end

    end // end for
      read_transaction = read_tran;
       uvm_report_info(get_type_name(), $psprintf("axi_master_read_sequence: Body read_transaction = \n %s", read_transaction.sprint()), UVM_LOW);
    `uvm_info("axi_master_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_sequence

// AXI configuration interface write sequence
class axi_cfg_if_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[35:0] cfg_addr;
  rand bit[63:0] cfg_data;
  rand bit wait_for_response_for_cfg_if_write = 1;

  /** Constrain the sequence length to a reasonable value */
  //constraint reasonable_sequence_length {sequence_length <= 100;}
   /** Constrain the wait_for_response_for_cfg_if_write */
  constraint default_wait_for_response_for_cfg_if_write {soft wait_for_response_for_cfg_if_write == 1;}
  /** UVM Object Utility macro */
  `uvm_object_utils(axi_cfg_if_write_sequence)

  /** Class Constructor */
  function new(string name = "axi_cfg_if_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_axi_master_transaction write_tran, read_tran;
    svt_configuration get_cfg;
    bit status;
    `uvm_info("axi_cfg_if_write_sequence: Body", "Entered", UVM_LOW)

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
      `uvm_fatal("axi_cfg_if_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin
      uvm_report_info("AXI_CFG_IF", $psprintf("Cfg Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);

      /** Set up the write transaction */
      `uvm_create(write_tran)
      write_tran.port_cfg    = cfg;
      write_tran.xact_type   = svt_axi_transaction::WRITE;
      write_tran.addr        = cfg_addr;
      write_tran.burst_type  = svt_axi_transaction::INCR;
      write_tran.burst_size  = svt_axi_transaction::BURST_SIZE_64BIT;
      write_tran.atomic_type = svt_axi_transaction::NORMAL;
      `ifdef SVT_AXI_MAX_BURST_LENGTH_WIDTH_1
      write_tran.burst_length = 1;
      `elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_2
      write_tran.burst_length = 2;
      `elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_3
      write_tran.burst_length = 4;
      `elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_4
      write_tran.burst_length = 8;
      `else
      write_tran.burst_length = 16;
      `endif
      write_tran.data      = new[write_tran.burst_length];
      write_tran.wstrb     = new[write_tran.burst_length];
      write_tran.data_user = new[write_tran.burst_length];
      foreach (write_tran.data[i]) begin
        write_tran.data[i] = cfg_data;
      end
      foreach (write_tran.wstrb[i]) begin
        if(write_tran.burst_type==svt_axi_transaction::FIXED)
         write_tran.wstrb[i] = '1;
         else 
         write_tran.wstrb[i] = 'hFF;
      end
      write_tran.wvalid_delay = new[write_tran.burst_length];
      foreach (write_tran.wvalid_delay[i]) begin
        write_tran.wvalid_delay[i] = wait_for_response_for_cfg_if_write ? $urandom_range(0,10):0;
      end

      /** Send the write transaction */
      `uvm_send(write_tran)

      /** Wait for the write transaction to complete */
       if(wait_for_response_for_cfg_if_write==1)begin
       get_response(rsp); 
      end

      `uvm_info("axi_cfg_if_write_sequence: Body", "AXI WRITE transaction completed", UVM_LOW);
    end // end for

    `uvm_info("axi_cfg_if_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_cfg_if_write_sequence


