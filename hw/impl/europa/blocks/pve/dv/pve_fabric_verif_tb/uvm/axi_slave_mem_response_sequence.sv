// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

/**
 * Abstract:
 * Class axi_slave_mem_response_sequence defines a sequence class that
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

`ifndef GUARD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
`define GUARD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV

class axi_slave_mem_response_sequence extends svt_axi_slave_base_sequence;

  svt_axi_slave_transaction req_resp;
  bit delay_bresp;
  bit delay_rresp;
  bit delay_4k;
  bit fake_slv_err_resp;
  int rand_delay;
  /** UVM Object Utility macro */
  `uvm_object_utils(axi_slave_mem_response_sequence)

  /** Class Constructor */
  function new(string name="axi_slave_mem_response_sequence");
    super.new(name);
  endfunction

  virtual task body();
    integer status;
    svt_configuration get_cfg;

    if($test$plusargs("DELAY_RRESP")) 
      $value$plusargs("DELAY_RRESP=%0d",delay_rresp);
    
    if($test$plusargs("DELAY_BRESP")) 
      $value$plusargs("DELAY_BRESP=%0d",delay_bresp);
    
    if(($test$plusargs("DELAY_4K")) || ($test$plusargs("DELAY_4k")))
      $value$plusargs("DELAY_4K=%0d",delay_4k);
    
    if($test$plusargs("FAKE_SLV_ERR_RESP") || ($test$plusargs("FAKE_SLVERR_RESP"))) 
      $value$plusargs("FAKE_SLV_ERR_RESP=%0d",fake_slv_err_resp);

    `uvm_info("axi_slave_mem_response_sequence", "Entered body...", UVM_LOW)
    `uvm_info("EXT_ARGS_PASSED", $sformatf("DELAY_RRESP=%0d, DELAY_BRESP=%0d, DELAY_4K=%0d FAKE_SLV_ERR_RESP=%0d",delay_rresp,delay_bresp,delay_4k,fake_slv_err_resp), UVM_LOW)

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
      `uvm_info("body", $sformatf("received item: %s",req_resp.sprint()), UVM_LOW)

      // check that req address received on slave port falls into expected address range
      if ((req_resp.port_id == targ_dma0  && (req_resp.addr < `PVE_BASE + `DMA0_SA          || req_resp.addr > `PVE_BASE + `DMA0_EA)) ||
          (req_resp.port_id == targ_dma1  && (req_resp.addr < `PVE_BASE + `DMA1_SA          || req_resp.addr > `PVE_BASE + `DMA1_EA)) ||
          (req_resp.port_id == targ_clint && (req_resp.addr < `PVE_BASE + `CLINT_SA         || req_resp.addr > `PVE_BASE + `CLINT_EA)) ||
          (req_resp.port_id == targ_perfc && (req_resp.addr < `PVE_BASE + `PERF_COUNTERS_SA || req_resp.addr > `PVE_BASE + `PERF_COUNTERS_EA)) ||
          (req_resp.port_id == targ_trace && (req_resp.addr < `PVE_BASE + `TRACE_IP_SA      || req_resp.addr > `PVE_BASE + `TRACE_IP_EA)) ||
          (req_resp.port_id == targ_spm   && (req_resp.addr < `PVE_BASE + `SPM_SA           || req_resp.addr > `PVE_BASE + `SPM_EA)) ||
          (req_resp.port_id == targ_l1_0  && (req_resp.addr < `PVE_BASE + `L1_0_SA          || req_resp.addr > `PVE_BASE + `L1_0_EA)) ||
          (req_resp.port_id == targ_l1_1  && (req_resp.addr < `PVE_BASE + `L1_1_SA          || req_resp.addr > `PVE_BASE + `L1_1_EA)) ||
          (req_resp.port_id == targ_l1_2  && (req_resp.addr < `PVE_BASE + `L1_2_SA          || req_resp.addr > `PVE_BASE + `L1_2_EA)) ||
          (req_resp.port_id == targ_l1_3  && (req_resp.addr < `PVE_BASE + `L1_3_SA          || req_resp.addr > `PVE_BASE + `L1_3_EA)) 
         )
        `uvm_error(get_name,$sformatf("REQ with addr: %0h received on slave port %s",req_resp.addr, targ_t'(req_resp.port_id)))
      else if (req_resp.port_id == targ_lt_ext &&
              ((req_resp.addr >= `PVE_BASE + `DMA0_SA          && req_resp.addr < `PVE_BASE + `DMA0_EA)||
              (req_resp.addr >= `PVE_BASE + `DMA1_SA          && req_resp.addr < `PVE_BASE + `DMA1_EA) ||
              (req_resp.addr >= `PVE_BASE + `CLINT_SA         && req_resp.addr < `PVE_BASE + `CLINT_EA)||
              //(req_resp.addr >= `PVE_BASE + `PERF_COUNTERS_SA && req_resp.addr < `PVE_BASE + `PERF_COUNTERS_SA) || //FIXME: uncomment after perfc target port is implemented
              //(req_resp.addr >= `PVE_BASE + `TRACE_IP_SA      && req_resp.addr < `PVE_BASE + `TRACE_IP_SA) ||
              (req_resp.addr >= `PVE_BASE + `SPM_SA           && req_resp.addr < `PVE_BASE + `SPM_EA)  ||
              (req_resp.addr >= `PVE_BASE + `L1_0_SA          && req_resp.addr < `PVE_BASE + `L1_0_EA) ||
              (req_resp.addr >= `PVE_BASE + `L1_1_SA          && req_resp.addr < `PVE_BASE + `L1_1_EA) ||
              (req_resp.addr >= `PVE_BASE + `L1_2_SA          && req_resp.addr < `PVE_BASE + `L1_2_EA) ||
              (req_resp.addr >= `PVE_BASE + `L1_3_SA          && req_resp.addr < `PVE_BASE + `L1_3_EA)))
        `uvm_error(get_name,$sformatf("REQ with addr: %0h received on slave port %s",req_resp.addr, targ_t'(req_resp.port_id)))
      else if (req_resp.port_id == targ_ht_ext &&
              ((req_resp.addr >= `PVE_BASE + `L1_0_SA          && req_resp.addr < `PVE_BASE + `L1_0_EA) ||
               (req_resp.addr >= `PVE_BASE + `L1_1_SA          && req_resp.addr < `PVE_BASE + `L1_1_EA) ||
               (req_resp.addr >= `PVE_BASE + `L1_2_SA          && req_resp.addr < `PVE_BASE + `L1_2_EA) ||
               (req_resp.addr >= `PVE_BASE + `L1_3_SA          && req_resp.addr < `PVE_BASE + `L1_3_EA)))
        `uvm_error(get_name,$sformatf("REQ with addr: %0h received on slave port %s",req_resp.addr, targ_t'(req_resp.port_id)))
      else
        `uvm_info(get_name,$sformatf("REQ with addr: %0h received on slave port %s",req_resp.addr, targ_t'(req_resp.port_id)), UVM_LOW)


      status=req_resp.randomize with {
        this.interleave_pattern == RANDOM_BLOCK;
        this.enable_interleave == 1;
      };
      if(!status)
        `uvm_fatal("body","Unable to randomize a response")
      req_resp.random_interleave_array = new[req_resp.burst_length];
      foreach (req_resp.random_interleave_array[i])
        req_resp.random_interleave_array[i] = 1;
      
      /**
       * Randomize the response and delays
       */
      if(fake_slv_err_resp)
        req_resp.bresp = svt_axi_transaction::SLVERR;
      else if (req_resp.atomic_type == svt_axi_transaction::EXCLUSIVE)
        req_resp.bresp = svt_axi_transaction::EXOKAY;
      else
        req_resp.bresp = svt_axi_transaction::OKAY;

      req_resp.addr_ready_delay = 'b0;
      req_resp.bvalid_delay = 'b0;

      if(fake_slv_err_resp)
        foreach (req_resp.rresp[index]) 
          req_resp.rresp[index] = svt_axi_transaction::SLVERR;
      else
        foreach (req_resp.rresp[index]) 
          req_resp.rresp[index] = svt_axi_transaction::OKAY;
          
      req_resp.rvalid_delay = new [req_resp.burst_length];
      foreach(req_resp.rvalid_delay[idx])
            req_resp.rvalid_delay[idx] = 'b0;//req_resp.burst_length; 
      
      req_resp.wready_delay = new [req_resp.burst_length];
      foreach(req_resp.wready_delay[idx])
            req_resp.wready_delay[idx] = 'b0;//req_resp.burst_length; 

      if(req_resp.get_transmitted_channel() == svt_axi_transaction::READ_WRITE)begin
        // If update_memory_in_request_order is set then call
        // set_update_mem_in_req_order_field(req) task for updating
        // update_mem_in_req_order transaction attribute. Updating memory
        // for this condition will be taken care in
        // put_write_transaction_data_to_mem() task in
        // svt_axi_slave_agent
        if (update_memory_in_request_order)
          set_update_mem_in_req_order_field(req_resp);
        get_read_data_from_mem_to_transaction(req_resp);
        req_resp.perform_atomic_xact_operation(req_resp);
        put_write_transaction_data_to_mem(req_resp);
      end
      /**
       * If write transaction, write data into slave built-in memory, else get
       * data from slave built-in memory
       */
      else if(req_resp.get_transmitted_channel() == svt_axi_transaction::WRITE) begin
        if(delay_bresp == 1 && delay_4k == 1) begin
          `protect      
          put_write_transaction_data_to_mem(req_resp);
          `endprotect
          req_resp.suspend_response = 1; //for the read response, setting this bit delays sending this transaction

          /* The waiting has to be done inside a fork-join_none, because the 
          transaction object has to be sent to driver in zero time only. */ 
          fork 
            begin 
              #5200ns;
              //wait for some event or delay
              req_resp.suspend_response = 0; //now the transaction will be sent
            end
          join_none
        end
        else if(delay_bresp == 1 && delay_4k == 0) begin
          `protect      
          put_write_transaction_data_to_mem(req_resp);
          `endprotect
          req_resp.suspend_response = 1; //for the read response, setting this bit delays sending this transaction

          /* The waiting has to be done inside a fork-join_none, because the 
          transaction object has to be sent to driver in zero time only. */ 
          fork 
            begin 
              rand_delay = $urandom_range(100,5100);
              #(rand_delay * 1ns);
              //wait for some event or delay
              req_resp.suspend_response = 0; //now the transaction will be sent
            end
          join_none
        end
        else begin
          `protect      
          put_write_transaction_data_to_mem(req_resp); //else dont delay the txn
          `endprotect
        end
      end
      else begin
        if(delay_rresp == 1 && delay_4k == 1) begin
          `uvm_info("axi_slave_mem_response_sequence", "Delaying the slave RRESP & RDATA", UVM_LOW)
          req_resp.suspend_response = 1; //for the read response, setting this bit delays sending this transaction

          /* The waiting has to be done inside a fork-join_none, because the 
          transaction object has to be sent to driver in zero time only. */ 
          fork 
            begin 
              #5200ns;
              //wait for some event or delay
              get_read_data_from_mem_to_transaction(req_resp);
              req_resp.suspend_response = 0; //now the transaction will be sent
            end
          join_none
        end
        else if(delay_rresp == 1 && delay_4k == 0) begin
          `uvm_info("axi_slave_mem_response_sequence", "Delaying the slave RRESP & RDATA", UVM_LOW)
          req_resp.suspend_response = 1; //for the read response, setting this bit delays sending this transaction

          /* The waiting has to be done inside a fork-join_none, because the 
          transaction object has to be sent to driver in zero time only. */ 
          fork 
            begin 
              #5200ns;
              rand_delay = $urandom_range(100,5100);
              #(rand_delay * 1ns);
              //wait for some event or delay
              get_read_data_from_mem_to_transaction(req_resp);
              req_resp.suspend_response = 0; //now the transaction will be sent
            end
          join_none
          end
        else begin
          get_read_data_from_mem_to_transaction(req_resp);
          req_resp.suspend_response = 0; //else dont delay the txn
        end
      end
         
      $cast(req,req_resp);

      /**
       * send to driver
       */
      `uvm_send(req)
      
      `uvm_info("body", $sformatf("sent item: %s",req.sprint()), UVM_LOW)
    end

    `uvm_info("body", "Exiting...", UVM_LOW)
  endtask: body

endclass: axi_slave_mem_response_sequence

`endif // GUARD_AXI_SLAVE_MEM_RESPONSE_SEQUENCE_SV
