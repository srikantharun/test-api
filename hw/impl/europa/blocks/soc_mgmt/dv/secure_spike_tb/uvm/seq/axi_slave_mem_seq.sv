// Copied from /home/projects/dware/DESIGNWARE_HOME/vip/svt/amba_svt/T-2022.03-3-T-20220513/examples/sverilog/tb_axi_svt_uvm_basic_sys/env/axi_slave_mem_response_sequence.sv

`ifndef AXI_SLAVE_MEM_SEQ
`define AXI_SLAVE_MEM_SEQ

class axi_slave_mem_seq extends svt_axi_slave_base_sequence;

  svt_axi_slave_transaction req_resp;

  /** UVM Object Utility macro */
  `uvm_object_utils(axi_slave_mem_seq)

  /** Class Constructor */
  function new(string name="axi_slave_mem_response_sequence");
    super.new(name);
  endfunction

  virtual task body();
    integer status;
    svt_configuration get_cfg;

    `uvm_info(get_type_name(), "Entered ...", UVM_HIGH)

    p_sequencer.get_cfg(get_cfg);
    if (!$cast(cfg, get_cfg)) begin
      `uvm_fatal(get_type_name(), "Unable to $cast the configuration to a svt_axi_port_configuration class");
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

      /**
       * Randomize the response and delays
       */
      status=req_resp.randomize with {
        bresp == svt_axi_slave_transaction::OKAY;
        foreach (rresp[index])  {
          rresp[index] == svt_axi_slave_transaction::OKAY;
          }
       };
       if(!status)
        `uvm_fatal(get_type_name(),"Unable to randomize a response")

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

    end

    `uvm_info(get_type_name(), "Exiting...", UVM_HIGH)
  endtask: body

endclass: axi_slave_mem_seq

`endif // AXI_SLAVE_MEM_SEQ
