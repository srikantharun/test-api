/**
 * Sequence that is used to random write and read to DWPU configuration AXI interface
 */
class axi_prog_random_sequence extends svt_axi_master_base_sequence;

  /** Parameter that controls the number of transactions that will be generated */
  rand int unsigned sequence_length = 100;

  /** variable that allows the checking of the response */
  rand bit check_resp = 1;

  /** Constrain the sequence length to a reasonable value */
  constraint reasonable_sequence_length {soft sequence_length <= 100;}

  /** Constrain the sequence to, by default, check response */
  constraint reasonable_check_resp {soft check_resp == 1;}

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_prog_random_sequence)

  /** Class Constructor */
  function new(string name = "axi_prog_random_sequence");
    super.new(name);
  endfunction

  extern virtual task body();

endclass : axi_prog_random_sequence

task axi_prog_random_sequence::body();
  svt_axi_master_transaction l_trans;
  svt_configuration get_cfg;
  bit status;
  `uvm_info("axi_prog_random_sequence: Body", "Entered", UVM_LOW)

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
    `uvm_fatal("axi_prog_random_sequence: Body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end


  for (int i = 0; i < sequence_length; i++) begin

    uvm_report_info("AXI_MST_RND_SEQ", $psprintf("Mst Seq Iter Number = %d Sequence Length = %d", i, sequence_length), UVM_MEDIUM);

    `uvm_info("body", $sformatf("Randomizing transaction with address inside 0x%0x and 0x%0x", DWPU_IMEM_ST_ADDR, DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)), UVM_LOW)
    /** Create and randomize transaction */
    `uvm_create(l_trans)
    l_trans.port_cfg    = cfg;
    //randomize transaction
    if(!l_trans.randomize() with {
      xact_type inside {svt_axi_transaction::WRITE,svt_axi_transaction::READ};
      (addr%8) == 0;
      addr inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-8]};
      (addr + (burst_length*8)) inside {[DWPU_IMEM_ST_ADDR: DWPU_IMEM_ST_ADDR+ ((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AXI_LT_DATA_WIDTH)/8)-8]};
      burst_size == BURST_SIZE_64BIT;
      burst_type inside {svt_axi_master_transaction::INCR, svt_axi_master_transaction::FIXED};
      atomic_type == svt_axi_transaction::NORMAL;
      prot_type == svt_axi_transaction::DATA_SECURE_NORMAL;
      cache_type == 0;
      foreach (wvalid_delay[i]) {
        wvalid_delay[i] inside {[0:5]};
      }
      foreach (rready_delay[i]) {
        rready_delay[i] inside {[0:5]};
      }
    }) `uvm_fatal(get_name, "l_trans randomization error!");


    /** Send the transaction */
    `uvm_send(l_trans)
    /** Wait for the transaction to complete */
    get_response(rsp);
    /** Check that response was correct*/

    if(check_resp) begin
      if(l_trans.xact_type == svt_axi_transaction::WRITE) begin
        if(l_trans.bresp == AXI_OKAY_RESPONSE)
          `uvm_info("DWPU_WRITE_PROG_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and BRESP = %s", l_trans.addr, l_trans.bresp), UVM_LOW)
        else
         `uvm_error("DWPU_WRITE_PROG_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and BRESP = %s", l_trans.addr, l_trans.bresp))
      end
      else begin
        foreach(l_trans.rresp[i]) begin
          if(l_trans.rresp[i] == AXI_OKAY_RESPONSE)
           `uvm_info("DWPU_READ_REG_COMPARE: PASSED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", l_trans.addr, i, l_trans.rresp[i]), UVM_LOW)
          else
           `uvm_error("DWPU_READ_REG_COMPARE: FAILED", $sformatf("Address= 0x%0x and RRESP[%0d] = %s", l_trans.addr, i, l_trans.rresp[i]))
        end
      end
    end
    `uvm_info("axi_prog_random_sequence: Body", "AXI WRITE transaction completed", UVM_LOW);
    //l_trans.print();

  end // end for
  `uvm_info("axi_prog_random_sequence: Body", "Exiting", UVM_LOW)
endtask : body
