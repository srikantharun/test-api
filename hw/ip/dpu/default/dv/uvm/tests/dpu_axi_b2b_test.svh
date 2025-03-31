
`ifndef DPU_AXI_B2B_TEST_SVH
`define DPU_AXI_B2B_TEST_SVH

class dpu_axi_random_sequence extends svt_axi_master_base_sequence;

  /** Number of Transactions in a sequence. */
  rand int unsigned sequence_length = 10;

  /** Enable outstanding transactions */
  int unsigned enable_outstanding_xacts = 0;

  /** FIXED burst type weight. */
  int unsigned FIXED_burst_type_wt = 0;

  /** INCR burst type weight. */
  int unsigned INCR_burst_type_wt = 10;

  /** WRAP burst type weight. */
  int unsigned WRAP_burst_type_wt = 10;

  /* Local variables. */
  rand int slv_num;
  // to save the slave number
  bit [35:0] lo_addr;
  // to save the lower address of program memory
  bit [35:0] hi_addr;
  // to save the higher address of program memory
  bit [35:0] read_addr;
  // to save the address to be read from program memory after write

  /** Constrain the transaction length to a reasonable value */
  constraint reasonable_sequence_length {sequence_length inside {1, dpu_pkg::PRG_MEM_DEPTH};}

  function new(string name = "dpu_axi_random_sequence");
    super.new(name);
  endfunction

  `uvm_object_utils_begin(dpu_axi_random_sequence)
    `uvm_field_int(FIXED_burst_type_wt, UVM_ALL_ON)
    `uvm_field_int(INCR_burst_type_wt, UVM_ALL_ON)
    `uvm_field_int(WRAP_burst_type_wt, UVM_ALL_ON)
  `uvm_object_utils_end

  //added a function in order to calculate the wstrb value:
  function bit[7:0] set_wstrb(int num_ones);
      bit[7:0] result;
      int ones_placed = 0;
      while (ones_placed < num_ones) begin
          int pos = $urandom_range(0, 7);
          if (!result[pos]) begin
              result[pos] = 1;
              ones_placed++;
          end
      end
      return result;
  endfunction

  /** UVM sequence body task */
  virtual task body();
    bit status_perf_mode, status_enable_outstanding_xacts;
    bit status_FIXED_burst_type_wt;
    bit status_INCR_burst_type_wt;
    bit status_WRAP_burst_type_wt;
    /** Handles for configurations. */
    svt_configuration get_cfg;
    svt_axi_port_configuration port_cfg;
    svt_axi_transaction::burst_size_enum _burst_size;
    int read_burst_length;

    void'(uvm_config_db#(int unsigned)::get(
        null, get_full_name(), "sequence_length", sequence_length
    ));
    status_FIXED_burst_type_wt = uvm_config_db#(int unsigned)::get(
        m_sequencer, get_type_name(), "FIXED_burst_type_wt", FIXED_burst_type_wt);
    status_INCR_burst_type_wt = uvm_config_db#(int unsigned)::get(
        m_sequencer, get_type_name(), "INCR_burst_type_wt", INCR_burst_type_wt);
    status_WRAP_burst_type_wt = uvm_config_db#(int unsigned)::get(
        m_sequencer, get_type_name(), "WRAP_burst_type_wt", WRAP_burst_type_wt);

    `uvm_info("dpu_axi_random_sequence", $sformatf("sequence_length='d%0d", sequence_length),
              UVM_MEDIUM);

    `uvm_info("dpu_axi_random_sequence", $sformatf(
              "FIXED_burst_type_wt is 'd%0d as a result of %0s.",
              FIXED_burst_type_wt,
              status_FIXED_burst_type_wt ? "the config DB" : "the default value"
              ), UVM_MEDIUM);
    `uvm_info("dpu_axi_random_sequence", $sformatf(
              "INCR_burst_type_wt is 'd%0d as a result of %0s.",
              INCR_burst_type_wt,
              status_INCR_burst_type_wt ? "the config DB" : "the default value"
              ), UVM_MEDIUM);
    `uvm_info("dpu_axi_random_sequence", $sformatf(
              "WRAP_burst_type_wt is 'd%0d as a result of %0s.",
              WRAP_burst_type_wt,
              status_WRAP_burst_type_wt ? "the config DB" : "the default value"
              ), UVM_MEDIUM);

    /** Getting svt_axi_port_configuration object handle. */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(port_cfg, get_cfg)) begin
      `uvm_fatal("body",
                 "Unable to $cast the configuration to a svt_axi_system_configuration class");
    end

    `uvm_create(req);
    for (int i = 0; i < dpu_pkg::PRG_MEM_DEPTH; i++) begin
      //Initiatialize the internal regs
      `uvm_do_with(req,{
            port_cfg == cfg;
            addr == DPU_PRG_ADDR_OFFSET + i*4;
            xact_type == svt_axi_transaction::WRITE;
            burst_type == svt_axi_transaction::INCR;
            burst_size == svt_axi_transaction::BURST_SIZE_32BIT;
            atomic_type == svt_axi_transaction::NORMAL;
            burst_length == 1;
            data[0] == 'h0;
            wstrb[0] == 8'h0f;
            wvalid_delay[0] == 1;
       });
    end

    //Setting the address range to program memory
    lo_addr = DPU_PRG_ADDR_OFFSET;
    hi_addr = DPU_PRG_ADDR_OFFSET + dpu_pkg::PRG_MEM_DEPTH -1 ;
    enable_outstanding_xacts = 0;

    `uvm_create(req);
    /** Execute the transactions in selected Slave from selected Master. */
    for (int i = 0; i < sequence_length; i++) begin
      `uvm_do_with(req,
                   {
          port_cfg == cfg;
          atomic_type == svt_axi_transaction::NORMAL;
          addr >  lo_addr;
          addr <= hi_addr-((1<<burst_size)*burst_length);
          ((1<<burst_size)*burst_length) < (hi_addr-lo_addr);
          ((1<<burst_size)*burst_length)%4 ==0;
          addr%4 ==0;
          burst_type dist {svt_axi_transaction::INCR:=INCR_burst_type_wt,
                           svt_axi_transaction::FIXED:=FIXED_burst_type_wt,
                           svt_axi_transaction::WRAP:=WRAP_burst_type_wt};
          xact_type == _write_xact_type;
          addr_valid_delay == 0;

          foreach(wvalid_delay[idx])
            wvalid_delay[idx]  == 0;
          bready_delay  == 0;
          foreach(rready_delay[idx])
            rready_delay[idx] == 0;
          // Embedded WSTRB constraint
          foreach(req.wstrb[j]) {
            if (burst_type == svt_axi_transaction::INCR) {
              (burst_size == svt_axi_transaction::BURST_SIZE_8BIT) -> wstrb[j] inside { set_wstrb(1) };
              (burst_size == svt_axi_transaction::BURST_SIZE_16BIT) -> wstrb[j] inside { set_wstrb(2) };
              (burst_size == svt_axi_transaction::BURST_SIZE_32BIT) -> wstrb[j] inside { set_wstrb(4) };
              (burst_size == svt_axi_transaction::BURST_SIZE_64BIT) -> wstrb[j] == 8'hff;
            } else {
              // For FIXED or WRAP burst types, you can define behavior as needed
              // This is a placeholder example where all byte lanes are used
              req.wstrb[j] == 8'hFF;
            }
          }
        })
      `uvm_info("AXIDPUB2B_WRITE", $sformatf(
                "addr: %0h, burst_size: %0h, burst_length: %0h",
                req.addr,
                req.burst_size,
                req.burst_length
                ), UVM_MEDIUM)
      // Wait for transaction to end based on
      if (!enable_outstanding_xacts) begin
        if (req.xact_type == svt_axi_transaction::READ) begin
          wait(req.data_status == svt_axi_transaction::ACCEPT ||
               req.data_status == svt_axi_transaction::ABORTED);
        end else if (req.xact_type == svt_axi_transaction::WRITE) begin
          wait(req.write_resp_status == svt_axi_transaction::ACCEPT ||
               req.write_resp_status == svt_axi_transaction::ABORTED);
        end
      end

      //Read transaction followed by write so that we dont read Xs from unallocated program memory space
      read_addr = req.addr;
      //Using the same burst size and length as the write transaction
      read_burst_length = req.burst_length;
      _burst_size = req.burst_size;

      `uvm_create(req);
      `uvm_do_with(req,
                   {
          port_cfg == cfg;
          atomic_type == svt_axi_transaction::NORMAL;
          burst_size == _burst_size;
          burst_length ==read_burst_length;
          addr== read_addr;
          addr >  lo_addr;
          addr <= hi_addr-((1<<burst_size)*burst_length);
          ((1<<burst_size)*burst_length) < (hi_addr-lo_addr);
          ((1<<burst_size)*burst_length)%4 ==0;
          addr%4 ==0;
          burst_type dist {svt_axi_transaction::INCR:=INCR_burst_type_wt,
                           svt_axi_transaction::FIXED:=FIXED_burst_type_wt,
                           svt_axi_transaction::WRAP:=WRAP_burst_type_wt};
          xact_type == _read_xact_type;
          addr_valid_delay == 0;
          foreach(wvalid_delay[idx])
            wvalid_delay[idx]  == 0;
          bready_delay  == 0;
          foreach(rready_delay[idx])
            rready_delay[idx] == 0;
        })
      `uvm_info(get_type_name(), $sformatf(
                "AXIDPUB2B READ addr : %0h burst_size = %0h , burst_length = %0h",
                req.addr,
                req.burst_size,
                req.burst_length
                ), UVM_MEDIUM)
      // Wait for transaction to end based on
      if (!enable_outstanding_xacts) begin
        if (req.xact_type == svt_axi_transaction::READ) begin
          wait(req.data_status == svt_axi_transaction::ACCEPT ||
               req.data_status == svt_axi_transaction::ABORTED);
        end else if (req.xact_type == svt_axi_transaction::WRITE) begin
          wait(req.write_resp_status == svt_axi_transaction::ACCEPT ||
               req.write_resp_status == svt_axi_transaction::ABORTED);
        end
      end

    end

  endtask : body

endclass

//Test class for back-to-back AXI transactions
class dpu_axi_b2b_test extends dpu_base_test;

  // Registration with the factory
  `uvm_component_utils(dpu_axi_b2b_test)

  // Class Constructor
  function new(string name = "dpu_axi_b2b_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction : new
  int unsigned seq_len = 50; // Keeping the number high but not too high to avoid timeout

  virtual function void build_phase(uvm_phase phase);
    `uvm_info("build_phase", "Entered...", UVM_LOW)
    super.build_phase(phase);

    set_type_override_by_type(svt_axi_master_base_sequence::get_type(),
                              dpu_axi_random_sequence::get_type());
    // Apply the dpu_axi_random_sequence
    uvm_config_db#(uvm_object_wrapper)::set(
        this, "env.axi_system_env.master[0].sequencer.main_phase", "default_sequence",
        svt_axi_master_base_sequence::type_id::get());
    // Set the sequence length
    if (!$value$plusargs("B2B_SEQ_LEN=%0d", seq_len)) begin
      `uvm_info(
          get_type_name(), $sformatf("Using default sequence length of %0d", seq_len), UVM_MEDIUM)
    end
    uvm_config_db#(int unsigned)::set(
        this, "env.axi_system_env.master[0].sequencer.svt_axi_master_base_sequence",
        "sequence_length", seq_len);
    // Apply the slave default response sequence to every slave sequencer
    uvm_config_db#(uvm_object_wrapper)::set(
        this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence",
        axi_slave_mem_response_sequence::type_id::get());

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction : build_phase

  // Run phase with timeout
  virtual task run_phase(uvm_phase phase);
    `uvm_info("run_phase", "Entered...", UVM_LOW)
    phase.raise_objection(this);
    uvm_top.set_timeout(2ms, 1);  // Increased timeout to 5ms

    super.run_phase(phase);  // Call the parent run_phase

    `uvm_info("run_phase", "Exiting...", UVM_LOW)

    phase.drop_objection(this);
  endtask

endclass : dpu_axi_b2b_test
`endif
