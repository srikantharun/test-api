//`define LOOP_CNT 20

// ==========================================================================================================
// Base class for all MVM sequences
// ==========================================================================================================
class dma_ip_base_sequence extends uvm_sequence;
  // Register
  `uvm_object_utils(dma_ip_base_sequence)

  // Declare p sequencer
 `uvm_declare_p_sequencer(axi_virtual_sequencer)

  // Class constructor
  function new (string name = "dma_ip_base_sequence");
    super.new(name);
  endfunction
endclass:dma_ip_base_sequence

// ==========================================================================================================
// RAL single write/read test-case
// ==========================================================================================================
 //class ral_access_single_write_read_seq extends dma_ip_base_sequence;

 //   `uvm_object_utils(ral_access_single_write_read_seq)

 //  // Declare p sequencer
 //  `uvm_declare_p_sequencer(axi_virtual_sequencer)

 //  function new(string name="ral_access_single_write_read_seq");
 //    super.new(name);
 //  endfunction : new

 //  virtual task body();
 //     //ai_core_mvm_subsys_reg_block mvm_regmodel;
 //     uvm_status_e  status;
 //     bit [63:0]    write_data;
 //     bit [63:0]    read_data;
 //     `uvm_info("ral_access_single_write_read_seq","Write and read", UVM_LOW);
 //     // Check status
 //     // Write/read back from one register of all CSR blocks
 //     // 1. MVM
 //     write_data = 64'h000_0003;
 //     read_data   = 64'h000_0003;
 //     `uvm_info("MVM_CSR", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", write_data, read_data), UVM_LOW)
 //     // Perform writes and reads
 //     p_sequencer.regmodel.m_mvmexe_regmod.cmdblk_ctrl.write(status, write_data);
 //     p_sequencer.regmodel.m_mvmexe_regmod.cmdblk_ctrl.read (status, read_data);
 //     // Comparison between the expected and the actual value
 //     if(read_data != write_data)
 //       `uvm_error("MVM_CSR:SINGLE_WRRD: FAILED", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", write_data, read_data))
 //     else
 //      `uvm_info("MVM_CSR:SINGLE_WRRD: PASSED", $sformatf("Write Data = 64'h%0h, Read Data = 64'h%0h", write_data, read_data), UVM_LOW)

 //     #100ns;
 //  endtask : body
 //endclass : ral_access_single_write_read_seq


// -----------------------------------------------------------------------------------------------
// AXI master write sequence - called indirectly via the base_test

class axi_master_write_sequence extends svt_axi_master_base_sequence;

  // Control Knob
  bit b2b;            // Back-2-Back transactions
  bit no_axi_dlys;    // Cancels AXI_DLYs
  
  svt_axi_master_transaction write_transaction;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[dma_ip_common_pkg::AXI_M_ADDR_WIDTH-1:0]  cfg_addr;
  rand bit[dma_ip_common_pkg::AXI_M_DATA_WIDTH-1:0]  cfg_data[];
  rand burst_size_enum                               burst_size_enum_t;
  rand burst_type_enum                               burst_type_enum_t;
  rand burst_lenght_enum                             burst_lenght_enum_t;
  rand resp_type_enum                                exp_bresp_t;

  // AXI Delays
  rand int  addr_valid_dly;
  rand int  wvalid_dly;
  rand int  bready_dly;
  
  constraint axi_delays_c {
    if (b2b | no_axi_dlys) { 
      addr_valid_dly  == 0;
      wvalid_dly      == 0;
      bready_dly      == 0;
    }
    else {
      addr_valid_dly  inside {[0 : dma_ip_common_pkg::AXI_ADDR_VALID_MAX_DELAY-1]};
      wvalid_dly      inside {[0 : dma_ip_common_pkg::AXI_WVALID_MAX_DELAY-1]};
      bready_dly      inside {[0 : dma_ip_common_pkg::AXI_BREADY_MAX_DELAY-1]};
    }
  }

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}
  constraint data_c {cfg_data.size == int'(burst_lenght_enum_t);}
 //Utility and Field macros,
  `uvm_object_utils_begin(axi_master_write_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_sarray_int(cfg_data,UVM_ALL_ON)
    `uvm_field_enum(burst_size_enum,burst_size_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_type_enum,burst_type_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_lenght_enum, burst_lenght_enum_t,UVM_ALL_ON)
    `uvm_field_enum(resp_type_enum, exp_bresp_t,UVM_ALL_ON)
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

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
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

    if($test$plusargs("B2B_ENB")) begin
      b2b = 1'b1;
      `uvm_info("Set-Op: TEST", $sformatf("BACK2BACK Enabled (zero axi-delays) Enabled"), UVM_LOW)
    end
    if($test$plusargs("NO_AXI_DELAYS")) begin
      no_axi_dlys = 1'b1;
      `uvm_info("Set-Op: TEST", $sformatf("NO_AXI_DELAYS (zero delays)"), UVM_LOW)
    end


    for (int i = 0; i < sequence_length; i++) begin
      uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);
      /** Set up the write transaction */
      `uvm_create(write_tran)
      write_tran.port_cfg    = cfg;
      write_tran.xact_type   = svt_axi_transaction::WRITE;
      write_tran.addr        = cfg_addr;
      write_tran.burst_type  = int'(burst_type_enum_t);
      write_tran.burst_size  = int'(burst_size_enum_t);
      write_tran.atomic_type = svt_axi_transaction::NORMAL;
      write_tran.burst_length = int'(burst_lenght_enum_t);
      write_tran.data      = new[write_tran.burst_length];
      write_tran.wstrb     = new[write_tran.burst_length];
      write_tran.data_user = new[write_tran.burst_length];

      // Delays Related to the AXI-Write Transaction - Need to re-randomize here as inside a loop which can generate n-axi transactions 
      addr_valid_dly = 0;   // Avoids constraint-issues when randomizing with BK2BK or NO AXI DELAY arguments 
      wvalid_dly     = 0; 
      bready_dly     = 0;
      if (!this.randomize(addr_valid_dly))  `uvm_fatal(get_name, "addr_valid_dly : Randomization Failed!")
      if (!this.randomize(bready_dly))      `uvm_fatal(get_name, "bready_dly     : Randomization Failed!")
      
      `uvm_info("axi_master_write_sequence", $sformatf("addr_valid_dly = %0d", addr_valid_dly), UVM_LOW)
      `uvm_info("axi_master_write_sequence", $sformatf("bready_dly     = %0d", bready_dly), UVM_LOW)
      
      write_tran.data_before_addr = 0;
      write_tran.addr_valid_delay = addr_valid_dly;
      write_tran.bready_delay     = bready_dly;

      write_tran.wvalid_delay = new[write_tran.burst_length];
      foreach (write_tran.wvalid_delay[i]) begin
      
        // Different wvalid_delay between wdata transfers (of a burst) 
        if (!this.randomize(wvalid_dly))      `uvm_fatal(get_name, "wvalid_dly     : Randomization Failed!")
        `uvm_info("axi_master_write_sequence", $sformatf("wvalid_dly     = %0d", wvalid_dly), UVM_LOW)

        write_tran.wvalid_delay[i] = wvalid_dly;             // Automatically 0-delays for b2b operation (see constraints)
      end

      // Data Setup
      foreach (write_tran.data[i]) begin
        write_tran.data[i] = this.cfg_data[i];
      end

      foreach (write_tran.wstrb[i]) begin
        //Strobe calculation
        if(burst_size_enum_t == BURST_SIZE_64BIT) begin
          write_tran.wstrb[i] = 8'hFF;
        end
        else if(burst_size_enum_t == BURST_SIZE_32BIT) begin
          write_tran.wstrb[i] = 4'hF;
        end
        else if(burst_size_enum_t == BURST_SIZE_16BIT) begin
          write_tran.wstrb[i] = 2'h3;
        end
        else if(burst_size_enum_t == BURST_SIZE_8BIT) begin
          write_tran.wstrb[i] = 1'h1;
        end
      end


      /** Send the write transaction */
      `uvm_send(write_tran)

      // CHECH BRESP for non back-2-back transactions
      if(!b2b) begin
        get_response(rsp);
        if (write_tran.bresp != exp_bresp_t)
          `uvm_error("axi_master_write_sequence: Body", $sformatf("BRESP MISMATCH for WRITEs [GOT=%s. EXP=%s]", write_tran.bresp.name(), exp_bresp_t.name()))
      end

       write_transaction = write_tran;
       uvm_report_info(get_type_name(), $psprintf("axi_master_write_sequence: Body write_transaction = \n %s", write_transaction.sprint()), UVM_LOW);

    end // end for sequence_length

    `uvm_info("axi_master_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_write_sequence


// -----------------------------------------------------------------------------------------------
// AXI master read sequence - called indirectly via the base_test

class axi_master_read_sequence extends svt_axi_master_base_sequence;

  // Control Knob
  bit b2b;
  bit no_axi_dlys;    // Cancels AXI_DLYs

  svt_axi_master_transaction  read_transaction;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[dma_ip_common_pkg::AXI_M_ADDR_WIDTH-1:0]  cfg_addr;
  rand int burst_length = 1;
  rand burst_size_enum                               burst_size_enum_t;
  rand burst_type_enum                               burst_type_enum_t;
  rand burst_lenght_enum                             burst_lenght_enum_t;
  rand resp_type_enum                                exp_rresp_t;

  bit[dma_ip_common_pkg::AXI_M_DATA_WIDTH-1:0]       read_data[];


  // AXI Delays
  rand int  addr_valid_dly;
  rand int  rready_dly;
  
  constraint axi_delays_c {
    if (b2b | no_axi_dlys) { 
      addr_valid_dly  == 0;
      rready_dly      == 0;
    }
    else {
      addr_valid_dly  inside {[0 : dma_ip_common_pkg::AXI_ADDR_VALID_MAX_DELAY-1]};
      rready_dly      inside {[0 : dma_ip_common_pkg::AXI_RREADY_MAX_DELAY-1]};
    }
  }
  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length <= 100;}

  /** UVM Object Utility macro */
  `uvm_object_utils_begin(axi_master_read_sequence)
    `uvm_field_int(cfg_addr,UVM_ALL_ON)
    `uvm_field_enum(burst_size_enum,burst_size_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_type_enum,burst_type_enum_t,UVM_ALL_ON)
    `uvm_field_enum(burst_lenght_enum, burst_lenght_enum_t,UVM_ALL_ON)
    `uvm_field_enum(resp_type_enum, exp_rresp_t,UVM_ALL_ON)
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

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
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

    if($test$plusargs("B2B_ENB")) begin
      b2b = 1'b1;
      `uvm_info("Set-Op: TEST", $sformatf("BACK2BACK Enabled (zero axi-delays) Enabled"), UVM_LOW)
    end
    if($test$plusargs("NO_AXI_DELAYS")) begin
      no_axi_dlys = 1'b1;
      `uvm_info("Set-Op: TEST", $sformatf("NO_AXI_DELAYS (zero delays)"), UVM_LOW)
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

      // Delays Related to the AXI-Read Transaction - Need to re-randomize here as inside a loop which can generate n-axi transactions 
      addr_valid_dly = 0;   // Avoids constraint-issues when randomizing with BK2BK or NO AXI DELAY arguments 
      rready_dly     = 0; 
      if (!this.randomize(addr_valid_dly))  `uvm_fatal(get_name, "addr_valid_dly : Randomization Failed!")

      `uvm_info("axi_master_read_sequence", $sformatf("addr_valid_dly = %0d", addr_valid_dly), UVM_LOW)

      read_tran.addr_valid_delay = addr_valid_dly;

      foreach (read_tran.rready_delay[i]) begin

        // Different rready_delay between rdata transfers (of a burst) 
        if (!this.randomize(rready_dly))      `uvm_fatal(get_name, "rready_dly     : Randomization Failed!")
        `uvm_info("axi_master_read_sequence", $sformatf("rready_dly     = %0d", rready_dly), UVM_LOW)

        read_tran.rready_delay[i] = rready_dly;             // Automatically 0-delays for b2b operation (see constraints)
      end

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      if(!b2b) begin
        get_response(rsp);

        foreach (read_tran.rresp[i]) begin
          if (read_tran.rresp[i] != exp_rresp_t)
            `uvm_error("axi_master_write_sequence: Body", $sformatf("RRESP[%01d] MISMATCH For READs [GOT=%02d. EXP=%s]", i, read_tran.rresp[i].name(), exp_rresp_t.name()))
        end
      end

      // Assign the read-data following the READ AXI Transaction
      read_data = new[read_tran.burst_length];
      foreach (read_tran.data[i]) begin
        read_data[i] = read_tran.data[i];
      end


      read_transaction = read_tran;
      uvm_report_info(get_type_name(), $psprintf("axi_master_read_sequence: Body read_transaction = \n %s", read_transaction.sprint()), UVM_LOW);

    end // end for sequence_length
 
    `uvm_info("axi_master_read_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : axi_master_read_sequence

// -----------------------------------------------------------------------------------------------

