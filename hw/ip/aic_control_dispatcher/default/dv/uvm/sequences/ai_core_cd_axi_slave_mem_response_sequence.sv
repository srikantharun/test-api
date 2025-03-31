
/**
 * Abstract:
 * Class ai_core_cd_axi_slave_mem_response_sequence defines a sequence class that
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

`ifndef GUARD_AI_CORE_CD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
`define GUARD_AI_CORE_CD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV

class ai_core_cd_axi_slave_mem_response_sequence extends svt_axi_slave_base_sequence;

  svt_axi_slave_transaction req_resp;

  /** UVM Object Utility macro */
  `uvm_object_utils(ai_core_cd_axi_slave_mem_response_sequence)

  /** Class Constructor */
  function new(string name="ai_core_cd_axi_slave_mem_response_sequence");
    super.new(name);
  endfunction

  virtual task body();
    integer status;
    svt_configuration get_cfg;

    `uvm_info("body", "Entered ...", UVM_DEBUG)

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

      /** Disabling constraint that is responsible for the warning of tready_delay array to big (by default it is setting its size to 0x3FFFF)
       * which leads to performance hit. The constraint reasonable_tready_delay was copied from
       * https://spdocs.synopsys.com/dow_retrieve/qsc-t/vg/snps_vip_lib/T-2022.06/class_ref/axi_svt_uvm_class_reference/html/transaction/class_svt_axi_slave_transaction.html
       * and updated so that the size of tready_delay is equal to tvalid_delay.size()
       */
      //req_resp.reasonable_tready_delay.constraint_mode(0);

      /**
       * Randomize the response and delays
       */
      status=req_resp.randomize with {
        bresp == svt_axi_slave_transaction::OKAY;
        foreach (rresp[index])  {
          rresp[index] == svt_axi_slave_transaction::OKAY;
          }
          /** Explanation of this constraint is above ("Disabling constraint...") */
      //    if (port_cfg.axi_interface_type == svt_axi_port_configuration::AXI4_STREAM) {
      //      tready_delay.size() == 5; //allow at least 5 tready_delay different from 0
//
      //      foreach (tready_delay[idx]) {
      //        tready_delay[idx] dist {
      //         0 := 25,
      //         [1:( 1000 >> 2)] :/ 50,
      //         [(( 1000 >> 2)+1): 1000] :/ 25
      //        };
      //      }
      //    } else {
      //      tready_delay.size() == 0;
      //    }
       };
       if(!status)
        `uvm_fatal("body","Unable to randomize a response")

      /**
       * If write transaction, write data into slave built-in memory, else get
       * data from slave built-in memory
       */
      if(req_resp.get_transmitted_channel() == svt_axi_slave_transaction::WRITE) begin
        `protect
        put_write_transaction_data_to_mem(req_resp);
        
        `uvm_info("body", $sformatf("sent item write addr: %d  req_resp: %d ", req_resp.addr, req_resp.bresp), UVM_LOW)
        `endprotect 
      end
      else if (req_resp.get_transmitted_channel() == svt_axi_slave_transaction::READ) begin
        `protect
        get_read_data_from_mem_to_transaction(req_resp);
        `uvm_info("body", $sformatf("sent item read addr: %d  req_resp: %d ", req_resp.addr, req_resp.rresp[0]), UVM_LOW)
        `endprotect
      end

      $cast(req,req_resp);

      /**
       * send to driver
       */
      `uvm_send(req)


      if(req_resp.get_transmitted_channel() == svt_axi_slave_transaction::WRITE) begin
         `uvm_info("body", $sformatf("sent item write mem_resp: %s",req.sprint()), UVM_LOW)
      end
      else if (req_resp.get_transmitted_channel() == svt_axi_slave_transaction::READ) begin
         `uvm_info("body", $sformatf("sent item read mem_resp: %s",req.sprint()), UVM_LOW)
      end
    end


      `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: ai_core_cd_axi_slave_mem_response_sequence

`endif // GUARD_AI_CORE_CD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
