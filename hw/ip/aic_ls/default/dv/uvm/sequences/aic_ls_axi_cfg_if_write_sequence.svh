// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS AXI Write Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// AXI configuration interface write sequence
class aic_ls_axi_cfg_if_write_sequence extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(aic_ls_axi_cfg_if_write_sequence)

  cust_svt_axi_master_transaction write_txn;
  bit b2b_en;

    /** Parameter that controls the number of transactions that will be generated */
  svt_axi_master_transaction write_tran;
  rand int unsigned sequence_length = 1;
  rand bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr;
  rand bit[AIC_LS_ENV_AXI_CFG_DATA_W/8-1:0] cfg_wstrb;
  rand int unsigned burst_length = 1; // defaults to single write only

  bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data_q[$];
  rand bit use_random_strb;

  /** Constrain the sequence length to a reasonable value */
  constraint C_DEFAULT_BURST_LEN { soft burst_length == 1;}
  constraint C_USE_WSTRB { soft use_random_strb==0; }
  static bit randomize_addr = 1;

  /** Class Constructor */
  function new(string name = "aic_ls_axi_cfg_if_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_configuration get_cfg;
    bit status;
    `uvm_info("aic_ls_axi_cfg_if_write_sequence: Body", "Entered", UVM_LOW)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
    `uvm_info(get_type_name(), $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW)

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("aic_ls_axi_cfg_if_write_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    if (cfg_data_q.size() != burst_length) begin
      `uvm_fatal(get_name(), "Data size error for cfg_write!")
    end else begin
      `uvm_info("AXI_CFG_IF", $psprintf("Sequence Length = %0d Burst Length = %0d cfg_data_q: %p", sequence_length, burst_length, cfg_data_q), UVM_LOW)
    end

    for (int i = 0; i < sequence_length; i++) begin

      `uvm_info("AXI_CFG_IF", $psprintf("Cfg Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM)

      /** Set up the write transaction */
      `uvm_create(write_txn)

      write_txn.add_l1_base_addr = 0;
      if(!write_txn.randomize() with {
        if (randomize_addr) addr == cfg_addr;
        xact_type   == svt_axi_transaction::WRITE;
        burst_type  == svt_axi_transaction::INCR;
        burst_size  == svt_axi_transaction::BURST_SIZE_64BIT;
        atomic_type == svt_axi_transaction::NORMAL;
        burst_length == cfg_data_q.size;
        foreach (data[i]) {
          data[i] == cfg_data_q[i];
          if (use_random_strb==0) {
            wstrb[i] == '1;
          } else {
            wstrb[i] == cfg_wstrb;
          }
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
        `uvm_fatal(get_name, "write_tran randomization error!");
      end else begin
        `uvm_info(get_name, $sformatf("cfg_addr: 0x%0x write_tran: %s", cfg_addr, write_txn.sprint()), UVM_MEDIUM)
      end

      /** Send the write transaction */
      if (!randomize_addr) write_txn.addr = cfg_addr; // use assignment instead of randomization
      write_txn.port_cfg = cfg;
      `uvm_send(write_txn)

      /** Wait for the write transaction to complete */
      if (b2b_en==0) begin
        get_response(rsp);
      end

      `uvm_info(get_type_name(), "AXI WRITE transaction completed", UVM_LOW);
    end // end for

    `uvm_info(get_type_name(), "Exiting", UVM_LOW)
  endtask : body

endclass : aic_ls_axi_cfg_if_write_sequence
