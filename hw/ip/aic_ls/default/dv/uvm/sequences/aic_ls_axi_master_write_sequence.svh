// AXI master write sequence
class aic_ls_axi_master_write_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  cust_svt_axi_master_transaction write_txn;
  rand bit          b2b_en=0;
  rand int unsigned sequence_length = 1;
  rand bit[35:0]    mem_addr;
  bit[511:0]        mem_data_q[$];

  constraint C_DEFAULT_B2B_LEN { soft b2b_en == 0;}

  /** UVM Object Utility macro */
  `uvm_object_utils(aic_ls_axi_master_write_sequence)

  /** Class Constructor */
  function new(string name = "aic_ls_axi_master_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_configuration get_cfg;
    bit status;
    `uvm_info("aic_ls_axi_master_write_sequence: Body", "Entered", UVM_LOW)

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
      `uvm_fatal("aic_ls_axi_master_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin

      uvm_report_info("AXI_MST_IF", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);

      /** Set up the write transaction */
      `uvm_create(write_txn)
      write_txn.add_l1_base_addr = 0;
      if(!write_txn.randomize() with {
        addr        == mem_addr;
        xact_type   == svt_axi_transaction::WRITE;
        burst_type  == svt_axi_transaction::INCR;
        burst_size  == svt_axi_transaction::BURST_SIZE_512BIT;
        atomic_type == svt_axi_transaction::NORMAL;
        burst_length == mem_data_q.size;
        foreach (data[i]) {
          data[i] == mem_data_q[i];
          wstrb[i] == '1;
          wvalid_delay[i] inside {[0:5]};
        }
        if(b2b_en) {
          data_before_addr == 0;
          addr_valid_delay == 0;
          foreach(wvalid_delay[i]) {
            wvalid_delay[i] == 0;
          }
          bready_delay == 0;
        }
      }) begin
        `uvm_fatal(get_name, "write_txn randomization error!");
      end else begin
        `uvm_info(get_name, $sformatf("cfg_addr: 0x%0x write_txn: %s", mem_addr, write_txn.sprint()), UVM_HIGH)
      end

      /** Send the write transaction */
      write_txn.port_cfg = cfg;

      /** Send the write transaction */
      `uvm_send(write_txn)

      /** Wait for the write transaction to complete */
      if (b2b_en==0) begin
        get_response(rsp);
      end

      `uvm_info("aic_ls_axi_master_write_sequence: Body", "AXI WRITE transaction completed", UVM_LOW);
    end // end for

    `uvm_info("aic_ls_axi_master_write_sequence: Body", "Exiting", UVM_LOW)
  endtask : body

endclass : aic_ls_axi_master_write_sequence
