
/**
 * Abstract:
 * Class ai_core_top_axi_slave_mem_response_sequence defines a sequence class that
 * the testbench uses to provide slave response to the Slave agent present in
 * the System agent. The sequence receives a response object of type
 * svt_axi_slave_transaction from slave sequencer. The sequence class then
 * randomizes the response with constraints and provides it to the slave driver
 * within the slave agent. The sequence also instantiates the slave built-in
 * memory, and writes into or reads from the slave memory.
 *
 * Execution phase: main_phase
 * Sequencer: Slave agent sequencer
 */

`ifndef GUARD_AI_CORE_TOP_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
`define GUARD_AI_CORE_TOP_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV

class ai_core_top_axi_slave_mem_response_sequence extends svt_axi_slave_base_sequence;

  svt_axi_slave_transaction req_resp;

  /** UVM Object Utility macro */
  `uvm_object_utils(ai_core_top_axi_slave_mem_response_sequence)
  static int unsigned m_slverr_prob = 0;
  static int unsigned m_decerr_prob = 0;

  /** Class Constructor */
  function new(string name="ai_core_top_axi_slave_mem_response_sequence");
    super.new(name);
  endfunction

  virtual task body();
    integer status;
    svt_configuration get_cfg;
    bit is_slverr, is_decerr;

    `uvm_info("body", "Entered ...", UVM_LOW)

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
    end

    // consumes responses sent by driver
    sink_responses();

    forever begin
      /**
       * Get the response request from the slave sequencer. The response request is
      * provided to the slave sequencer by the slave port monitor, through
      * TLM port.
      */
      p_sequencer.response_request_port.peek(req_resp);

     status=req_resp.randomize with {
       bresp == svt_axi_slave_transaction::OKAY;
       foreach (rresp[index])  {
         rresp[index] == svt_axi_slave_transaction::OKAY;
         }
       `ifdef INTERLEAVING_ENABLED
        this.interleave_pattern == RANDOM_BLOCK;
        this.enable_interleave == 1;
       `endif
      };
      if(!status)
       `uvm_fatal("body","Unable to randomize a response")

      if (is_slverr) begin
        req_resp.bresp = svt_axi_slave_transaction::SLVERR;
        foreach (req_resp.rresp[index]) begin
          req_resp.rresp[index] = svt_axi_slave_transaction::SLVERR;
        end
      end else if (is_decerr) begin
        req_resp.bresp = svt_axi_slave_transaction::DECERR;
        foreach (req_resp.rresp[index]) begin
          req_resp.rresp[index] = svt_axi_slave_transaction::DECERR;
        end
      end

      /**
       * If write transaction, write data into slave built-in memory, else get
       * data from slave built-in memory
       */
      if(req_resp.get_transmitted_channel() == svt_axi_slave_transaction::WRITE) begin
        `protect
        put_write_transaction_data_to_mem(req_resp);
        `endprotect
      end
      else if (req_resp.get_transmitted_channel() == svt_axi_slave_transaction::READ) begin
        `protect
        get_read_data_from_mem_to_transaction(req_resp);
        `endprotect
      end

      $cast(req,req_resp);

      /**
       * send to driver
       */
      `uvm_send(req)
       uvm_report_info(get_type_name(), $psprintf(" ai_core_top_axi_slave_mem_response_sequence \n%s", req.sprint()), UVM_LOW);

    end

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: ai_core_top_axi_slave_mem_response_sequence

`endif // GUARD_AI_CORE_TOP_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
