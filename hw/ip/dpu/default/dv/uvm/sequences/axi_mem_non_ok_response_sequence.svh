
typedef enum {
  OKAY,
  EXOKAY,
  SLVERR,
  DECERR
} resp_enum;

class axi_mem_non_ok_response_sequence extends svt_axi_slave_base_sequence;
  /* svt_axi_slave_base_sequence is a slave sequence provided with the VIP. 
   Refer to the HTML document for more details about this sequence. */
  static resp_enum resp_e;
  /** UVM Object Utility macro */
  `uvm_object_utils(axi_mem_non_ok_response_sequence)

  /** Class Constructor */
  function new(string name = "axi_mem_non_ok_response_sequence");
    super.new(name);
  endfunction

  virtual task body();
    integer status;
    svt_configuration get_cfg;

    `uvm_info("axi_mem_non_ok_response_sequence", "Entered ...", UVM_LOW)

    /* The macro `uvm_declare_p_sequencer(svt_axi_slave_sequencer) is used in the
    base class 'svt_axi_slave_base_sequence'. So 'p_sequencer' handle will be 
    available here. */
    p_sequencer.get_cfg(get_cfg);

    /* The handle 'cfg' is of type svt_axi_port_configuration, present in the
    base class 'svt_axi_slave_base_sequence' */
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("axi_mem_non_ok_response_sequence",
                 "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    begin

      /* The declaration of the below handle should be done in the forever loop
      only. If it is done outside of forever loop, it will cause issues with
      the object getting overwritten by subsequent peeks. */

      svt_axi_slave_transaction req_resp;

      /**
       * Get the response request from the slave sequencer. The response request
       * is provided to the slave sequencer by the slave port monitor, through
       * TLM port.
       */

      /* Refer to the AXI VIP User Guide for details about 'response_request_port' */
      p_sequencer.response_request_port.peek(req_resp);

      /**
       * Randomize the response and delays
       */
      status = req_resp.randomize with {
        if (resp_e == OKAY) {
          bresp == svt_axi_transaction::OKAY;
        } else
        if (resp_e == EXOKAY) {
          bresp == svt_axi_transaction::EXOKAY;
        } else
        if (resp_e == SLVERR) {
          bresp == svt_axi_transaction::SLVERR;
        } else
        if (resp_e == DECERR) {bresp == svt_axi_transaction::DECERR;}
        foreach (rresp[index]) {
          if (resp_e == OKAY) {
            rresp[index] == svt_axi_transaction::OKAY;
          } else
          if (resp_e == EXOKAY) {
            rresp[index] == svt_axi_transaction::EXOKAY;
          } else
          if (resp_e == SLVERR) {
            rresp[index] == svt_axi_transaction::SLVERR;
          } else
          if (resp_e == DECERR) {rresp[index] == svt_axi_transaction::DECERR;}
        }
      };
      if (!status) `uvm_fatal("axi_mem_non_ok_response_sequence", "Unable to randomize a response")

      /**
       * If write transaction, write data into slave built-in memory, else get
       * data from slave built-in memory.
       */
      `uvm_info("axi_mem_non_ok_response_sequence", $sformatf("status set"), UVM_LOW)
      if (req_resp.get_transmitted_channel() == svt_axi_slave_transaction::WRITE) begin
        `uvm_info("axi_mem_non_ok_response_sequence", $sformatf("write_channel start"), UVM_LOW)
         `protect      
        put_write_transaction_data_to_mem(req_resp);
         `endprotect
      end else if (req_resp.get_transmitted_channel() == svt_axi_slave_transaction::READ) begin
        `uvm_info("axi_mem_non_ok_response_sequence", $sformatf("read_channel start"), UVM_LOW)

         `protect
        get_read_data_from_mem_to_transaction(req_resp);
         `endprotect
      end
      `uvm_info("axi_mem_non_ok_response_sequence", $sformatf("channel transmit finish"), UVM_LOW)

      $cast(req, req_resp);

      /**
       * send to driver
       */
      `uvm_send(req)
      `uvm_info("axi_mem_non_ok_response_sequence", $sformatf("transaction send"), UVM_LOW)
    end

    `uvm_info("axi_mem_non_ok_response_sequence", "Exiting...", UVM_LOW)
  endtask : body

endclass : axi_mem_non_ok_response_sequence
