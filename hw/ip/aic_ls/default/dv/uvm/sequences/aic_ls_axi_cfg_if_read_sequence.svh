// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS AXI Read Sequence
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// AXI configuration interface read sequence
class aic_ls_axi_cfg_if_read_sequence extends svt_axi_master_base_sequence;

  /** UVM Object Utility macro */
  `uvm_object_utils(aic_ls_axi_cfg_if_read_sequence)
  svt_axi_master_transaction read_tran;

  bit b2b_en;

    /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 1;
  rand bit[AIC_LS_ENV_AXI_CFG_ADDR_W-1:0] cfg_addr;
  rand bit[AIC_LS_ENV_AXI_CFG_DATA_W-1:0] cfg_data;
  int unsigned burst_length = 1; // defaults to single read only

  /** Constrain the sequence length to a reasonable value */
  //constraint reasonable_sequence_length {sequence_length <= 100;}

  /** Class Constructor */
  function new(string name = "aic_ls_axi_cfg_if_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    svt_configuration get_cfg;
    bit status;
    `uvm_info("aic_ls_axi_cfg_if_read_sequence: Body", "Entered", UVM_LOW)

    super.body();

    status = uvm_config_db#(int unsigned)::get(null, get_full_name(), "sequence_length", sequence_length);
    `uvm_info(get_type_name(), $sformatf("sequence_length is %0d as a result of %0s.", sequence_length, status ? "config DB" : "randomization"), UVM_LOW)

    /** Obtain a handle to the port configuration */
    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("aic_ls_axi_cfg_if_read_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    for (int i = 0; i < sequence_length; i++) begin

      `uvm_info("AXI_CFG_IF", $psprintf("Cfg Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM)

      /** Set up the read transaction */
      `uvm_create(read_tran)
      read_tran.port_cfg    = cfg;
      read_tran.xact_type   = svt_axi_transaction::READ;
      read_tran.addr        = cfg_addr;
      read_tran.burst_type  = svt_axi_transaction::INCR;
      read_tran.burst_size  = svt_axi_transaction::BURST_SIZE_64BIT;
      read_tran.atomic_type = svt_axi_transaction::NORMAL;
`ifdef SVT_AXI_MAX_BURST_LENGTH_WIDTH_1
      read_tran.burst_length = 1;
`elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_2
      read_tran.burst_length = 2;
`elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_3
      read_tran.burst_length = 4;
`elsif SVT_AXI_MAX_BURST_LENGTH_WIDTH_4
      read_tran.burst_length = 8;
`else
      read_tran.burst_length = 16;
`endif
      read_tran.rresp        = new[read_tran.burst_length];
      read_tran.data         = new[read_tran.burst_length];
      read_tran.rready_delay = new[read_tran.burst_length];
      read_tran.data_user    = new[read_tran.burst_length];
      foreach (read_tran.rready_delay[i]) begin
        read_tran.rready_delay[i] = i;
      end

      /** Send the read transaction */
      `uvm_send(read_tran)

      /** Wait for the read transaction to complete */
      if (b2b_en==0) begin
        get_response(rsp);
      end

      `uvm_info(get_type_name(), "AXI WRITE transaction completed", UVM_LOW);
    end // end for

    `uvm_info(get_type_name(), "Exiting", UVM_LOW)
  endtask : body

endclass : aic_ls_axi_cfg_if_read_sequence
