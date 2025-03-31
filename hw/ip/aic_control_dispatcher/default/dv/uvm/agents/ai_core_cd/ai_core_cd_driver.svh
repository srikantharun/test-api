`ifndef AI_CORE_CD_DRIVER_SV
`define AI_CORE_CD_DRIVER_SV

class ai_core_cd_driver extends uvm_driver#(token_agent_seq_item);
  `uvm_component_utils(ai_core_cd_driver)

  //declare token agent configuration
  //ai_core_cd_agent_config m_aicd_cfg;

  //declare interface
  virtual ai_core_cd_if irq_vif;
  virtual ai_core_cd_done_if done_vif;

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    //if ( ! uvm_config_db#( ai_core_cd_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "aicd_agt_cfg" ), .value( m_aicd_cfg ) ) ) begin
    //  `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    //end
  endfunction

  virtual task reset_phase (uvm_phase phase);
    reset();
  endtask : reset_phase

  virtual task reset();
      done_vif.done_o = 1'b0;
  endtask : reset


  //sequence 
  //
  //
  //start drive_done_with_delay() {
  //  //the semaphores help avoid the overwrtiing 
  //  wait delay;
  //  sema[idx].get(1);
  //  done_a[idx] = 1;  //assert has precedence over de-assert with the aid of semaphores
  //  wait clock
  //  sema[idx].put(1);
  //  sema[idx].get(1);
  //  done_a[idx] = 0;  //assert
  //  sema[idx].put(1);
  //}

  //send reactive sequences if needed in the current clock cycle
  //forever begin
  //  crt_done = {done_a};
  //  if crt_done != bus_done  begin
  //    fork sequence
  //    bus_done = crt_done;
  //  end
  //  wait clock;
  //end

  virtual task cycle_through_done();
    for (int i =0; i<17; i++) begin
      @(done_vif.drv);
      done_vif.done_o[i] = 1'b1;
    end
    @(done_vif.drv);
    done_vif.done_o = 'd0;
  endtask : reset
  

  virtual task drive_done(token_agent_seq_item a_req);
    `uvm_info(get_full_name(), $sformatf("Start driving done %s", a_req.convert2string()), UVM_HIGH)
    @(done_vif.drv);    
      //wait for the delay time
      repeat (a_req.m_bv_delay) @(done_vif.drv);
      //drive the output to 1
     done_vif.done_o = a_req.done;


    //this logic will not allow back to back driving therefore will let the sequence handle the de-assertion  
    //wait one cycle
    //@(done_vif.drv);

    //drive the output to 0
    // done_vif.done_o = 'b0;

    `uvm_info(get_full_name(), $sformatf("Finish driving output"), UVM_HIGH)
  endtask : drive_tok

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    reset();
    
    //TODO: remove code - initial check done interface
    #100ms;
    cycle_through_done(); 

    fork
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info(get_full_name(), $sformatf("received token %s", req.convert2string()), UVM_HIGH)
        //put command on the respective queue
        if(req.m_type_enm == DONE) begin
          drive_done(req);
        end
        else begin
          `uvm_fatal(get_full_name(), $sformatf("Cannot drive the following req %s", req.convert2string()))
        end
        //send to the upper layer the information that this token was received and is on queue to be run
        seq_item_port.item_done();
      end
    join
  endtask
endclass

`endif // AI_CORE_CD_DRIVER_SV


