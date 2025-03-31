// AXI master write sequence
class axi_master_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand chip_axi_addr_t   cfg_addr;
  rand l2_axi_data_t    cfg_data[];
  rand burst_size_enum burst_size_enum_t;
  rand burst_type_enum burst_type_enum_t;
  rand burst_lenght_enum burst_lenght_enum_t;
  svt_axi_master_transaction write_transaction;
  rand int delay;
  rand bit[63:0] write_strobe;
  bit [63:0] strobe;
  int strobe_bytes;
  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint data_c {cfg_data.size == int'(burst_lenght_enum_t);}
  constraint delay_range { delay >=1 && delay <=16;}
 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_write_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
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
      write_tran.port_cfg     = cfg;
      write_tran.xact_type    = svt_axi_transaction::WRITE;
      write_tran.addr         = cfg_addr;
      write_tran.burst_type   = int'(burst_type_enum_t);
      write_tran.burst_size   = int'(burst_size_enum_t);
      write_tran.atomic_type  = svt_axi_transaction::NORMAL;
      write_tran.burst_length = int'(burst_lenght_enum_t);
      write_tran.data         = new[write_tran.burst_length];
      write_tran.wstrb        = new[write_tran.burst_length];
      write_tran.data_user    = new[write_tran.burst_length];
      write_tran.wready_delay = new[write_tran.burst_length];

      foreach (write_tran.data[i]) begin
        write_tran.data[i] = this.cfg_data[i];
      end
     
    strobe_bytes = 1 << write_tran.burst_size;
    strobe = 64'b0;

   foreach(write_tran.wstrb[i]) begin
     for ( int j= 0;j<strobe_bytes; j++) begin
        strobe = strobe | (1 << j);
     end
    write_tran.wstrb[i] = strobe;
   end
/*
      if ($test$plusargs("WSTRB")) begin
        foreach (write_tran.wstrb[i]) begin
          write_tran.wstrb[i] = write_strobe;
        end
      end
*/
      write_tran.addr_valid_delay = 0;
      write_tran.wvalid_delay = new[write_tran.burst_length];
      if ($test$plusargs("BCK_BCK_TRANS")) begin
        foreach (write_tran.wvalid_delay[i]) begin
          write_tran.wvalid_delay[i] = 0;
        end
        foreach (write_tran.wready_delay[i]) begin
          write_tran.wready_delay[i] = 0;
        end
      end else begin
        foreach (write_tran.wvalid_delay[i]) begin
          write_tran.wvalid_delay[i] = i;
        end
      end
      if ($test$plusargs("DELAY_VALID")) begin
        foreach (write_tran.wvalid_delay[i]) begin
          write_tran.wvalid_delay[i] = delay;
        end
      end

      /** Send the write transaction */
      `uvm_send(write_tran)

      /** Wait for the write transaction to complete */
      if(!($test$plusargs("BCK_BCK_TRANS"))) begin
        get_response(rsp);
      end

      write_transaction = write_tran;
           uvm_report_info(get_type_name(), $psprintf("axi_master_write_sequence: Body write_transaction = \n %s", write_transaction.sprint()), UVM_LOW);
    end
    `uvm_info("axi_master_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_write_sequence

// AXI master read sequence
class axi_master_read_sequence extends svt_axi_master_base_sequence;

  // Parameter that controls the number of transactions that will be generated
  rand int unsigned sequence_length = 1;
  rand chip_axi_addr_t    cfg_addr;
  chip_axi_addr_t readaddr;
  rand int burst_length = 1;
  rand burst_size_enum burst_size_enum_t;
  rand burst_type_enum burst_type_enum_t;
  rand burst_lenght_enum burst_lenght_enum_t;
  svt_axi_master_transaction  read_transaction;
  bit[`AXI_LP_DATA_WIDTH-1:0]  cfg_read_data[8];
  rand int delay;
  // Constrain the sequence length to a reasonable value
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint delay_range {delay >=1 && delay <=16;}

  // UVM Object Utility macro
  `uvm_object_utils(axi_master_read_sequence)

  // Class Constructor
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

    // Obtain a handle to the port configuration
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_master_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end


    for (int i = 0; i < sequence_length; i++) begin

      uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);
      // Set up the read transaction
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
      read_tran.rvalid_delay =  new[read_tran.burst_length];
      read_tran.addr_valid_delay = 0;
      //Providing 0 dealy for the back to back transaction
      if ($test$plusargs("BCK_BCK_TRANS")) begin
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = 0;
        end
        foreach (read_tran.rvalid_delay[i]) begin
          read_tran.rvalid_delay[i] = 0;
        end
      end else begin
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = i;
        end
      end
      // Providing a valid dealy when the length is above 16
      if ($test$plusargs("DELAY_VALID")) begin
        foreach (read_tran.rready_delay[i]) begin
          read_tran.rready_delay[i] = delay;
        end
      end

      // Send the read transaction
      `uvm_send(read_tran)

      // Wait for the read transaction to complete
      if(!($test$plusargs("BCK_BCK_TRANS"))) begin
        get_response(rsp);
      end

      read_transaction = read_tran;
      readaddr = read_transaction.addr;
      foreach (read_transaction.data[i]) begin
        cfg_read_data [i] = read_transaction.data[i];
      end
    end
    uvm_report_info(get_type_name(), $psprintf("axi_master_read_sequence: Body read_transaction = \n %s", read_transaction.sprint()), UVM_LOW);
    `uvm_info("axi_master_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_sequence
