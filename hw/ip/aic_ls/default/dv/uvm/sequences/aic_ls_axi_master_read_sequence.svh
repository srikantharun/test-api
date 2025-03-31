// AXI master read sequence
class aic_ls_axi_master_read_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[35:0]    mem_addr;
  rand bit          b2b_en;
  v_object          m_v_object;
  uvm_event         m_axi_rd_evt = uvm_event_pool::get_global("aic_ls_axi_master_read_sequence_evt");

  rand int unsigned burst_len = 1; // defaults to single read only

  /** Constrain the sequence length to a reasonable value */
  constraint C_DEFAULT_BURST_LEN { soft burst_len == 1;}
  constraint C_DEFAULT_B2B_LEN { soft b2b_en == 0;}

  /** UVM Object Utility macro */
  `uvm_object_utils(aic_ls_axi_master_read_sequence)

  /** Class Constructor */
  function new(string name = "aic_ls_axi_master_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_configuration get_cfg;
    cust_svt_axi_master_transaction read_txn;
    bit status;
    `uvm_info("aic_ls_axi_master_read_sequence: Body", "Entered", UVM_LOW)

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
      `uvm_fatal("aic_ls_axi_master_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin
      uvm_report_info("AXI_MST_RD_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);

     /** Set up the read transaction */
      `uvm_create(read_txn)
      read_txn.add_l1_base_addr = 0;
      if(!read_txn.randomize() with {
        addr        == mem_addr;
        xact_type   == svt_axi_transaction::READ;
        burst_type  == svt_axi_transaction::INCR;
        burst_size  == svt_axi_transaction::BURST_SIZE_512BIT;
        atomic_type == svt_axi_transaction::NORMAL;
        burst_length == burst_len;
        if(b2b_en) {
          foreach(rready_delay[i]) {
            rready_delay[i] == 0;
          }
        }
      }) begin
        `uvm_fatal(get_name(), "read_txn randomization error!");
      end else begin
        `uvm_info(get_name(), $sformatf("mem_addr: 0x%0x read_txn: %s", mem_addr, read_txn.sprint()), UVM_HIGH)
      end

      /** Send the read transaction */
      `uvm_send(read_txn)

      /** Wait for the read transaction to complete */
      get_response(rsp);
      m_v_object = v_object::type_id::create("m_v_object");
      m_v_object.m_64bit_data = mem_addr;
      m_v_object.m_512bit_data = rsp.data[0];
      m_axi_rd_evt.trigger(m_v_object);
      `uvm_info(get_name(), "axi rd rsp received", UVM_LOW)
     end // end for

    `uvm_info(get_name(), "Exiting", UVM_LOW)
  endtask : body

endclass : aic_ls_axi_master_read_sequence
