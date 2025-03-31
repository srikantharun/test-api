`ifndef TOKEN_AGENT_DRIVER_SV
`define TOKEN_AGENT_DRIVER_SV

class token_agent_driver extends uvm_driver#(token_agent_seq_item);
  `uvm_component_utils(token_agent_driver)

  //declare token agent configuration
  token_agent_config m_tok_cfg;

  //declare interface
  virtual token_agent_if m_vif;
  //declare token queues
  token_agent_seq_item m_tok_cons_q[$];
  token_agent_seq_item m_tok_prod_q[$];

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if ( ! uvm_config_db#( token_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "tok_agt_cfg" ), .value( m_tok_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
  endfunction

  virtual task reset_phase (uvm_phase phase);
    reset();

  endtask : reset_phase

  virtual task reset();
    //set the default value of tok_cons_vld and tok_prod_rdy on reset phase
    if(m_tok_cfg.m_type == TOK_AGT_MASTER) begin
      m_vif.tok_cons_vld = 1'b0;
      m_vif.tok_prod_rdy = 1'b0;
    end
    else begin
      m_vif.tok_prod_vld = 1'b0;
      m_vif.tok_cons_rdy = 1'b0;
    end
  endtask : reset

  virtual task drive_output(token_agent_seq_item a_req, bit a_b_value);
    `uvm_info(get_full_name(), $sformatf("START Driving output to be %0d for token %s", a_b_value, a_req.convert2string()), UVM_LOW)
    //depending on the m_type_enm drive the Consumer or Producer output
    if(a_req.m_type_enm == TOK_CONS_DRV) begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER) m_vif.drv_mstr.tok_cons_vld <= a_b_value;
      else                                   m_vif.drv_slv.tok_cons_rdy <= a_b_value;
    end
    else begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER) m_vif.drv_mstr.tok_prod_rdy <= a_b_value;
      else                                   m_vif.drv_slv.tok_prod_vld <= a_b_value;
    end
    `uvm_info(get_full_name(), $sformatf("END Driving output to be %0d for token %s", a_b_value, a_req.convert2string()), UVM_LOW)
  endtask : drive_output

  virtual task wait_input_value(token_agent_seq_item a_req, bit a_b_value);
    `uvm_info(get_full_name(), $sformatf("START Waiting input value to be %0d for token %s", a_b_value, a_req.convert2string()), UVM_LOW)
    //depending on the m_type_enm wait for Consumer or Producer input to be equal to a_b_value
    if(a_req.m_type_enm == TOK_CONS_DRV) begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER)
        while( m_vif.tok_cons_rdy !== a_b_value)
          @(m_vif.mon);
      else
        while( m_vif.tok_cons_vld !== a_b_value)
          @(m_vif.mon);
    end
    else begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER)
        while( m_vif.tok_prod_vld !== a_b_value)
          @(m_vif.mon);
      else
        while( m_vif.tok_prod_rdy !== a_b_value)
          @(m_vif.mon);
    end
    `uvm_info(get_full_name(), $sformatf("END Waiting input value to be %0d for token %s", a_b_value, a_req.convert2string()), UVM_LOW)
  endtask : wait_input_value

  virtual task drive_tok_cons();
    if(m_tok_cfg.m_b_cons_active) begin
      forever begin
        wait(m_tok_cons_q.size > 0) begin
          drive_tok(m_tok_cons_q.pop_front());
        end
      end
    end
    else begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER) m_vif.drv_mstr.tok_cons_vld <= 1'b0;
      else                                   m_vif.drv_slv.tok_cons_rdy <= 1'b0;
    end
  endtask : drive_tok_cons

  virtual task drive_tok_prod();
    if(m_tok_cfg.m_b_prod_active) begin
      forever begin
        wait(m_tok_prod_q.size > 0) begin
          drive_tok(m_tok_prod_q.pop_front());
        end
      end
    end
    else begin
      if(m_tok_cfg.m_type == TOK_AGT_MASTER) m_vif.drv_mstr.tok_prod_rdy <= 1'b0;
      else                                   m_vif.drv_slv.tok_prod_vld <= 1'b0;
    end
  endtask : drive_tok_prod

  virtual task drive_tok(token_agent_seq_item a_req);
    `uvm_info(get_full_name(), $sformatf("Start driving token %s", a_req.convert2string()), UVM_LOW)
    @(m_vif.drv_mstr);
    //if delay equal to 0 then drive the signal to 1 directly and wait for the input to go high
    if(a_req.m_bv_delay == 0) begin
      //drive the output to 1
      drive_output(a_req, 1);
      //wait for the posedge of the input
      wait_input_value(a_req, 1'b1);
    end
    //else (delay different from 0), then it is necessary to wait for the posedege of the input
    else begin
      //wait for the posedge of the input
      wait_input_value(a_req, 1'b1);
      //wait for the delay time
      repeat (a_req.m_bv_delay) @(m_vif.drv_mstr);
      //drive the output to 1
      drive_output(a_req, 1);
    end

    //wait one cycle
    @(m_vif.drv_mstr);

    //drive the output to 0
    drive_output(a_req, 0);

    `uvm_info(get_full_name(), $sformatf("Finish driving output"), UVM_LOW)
  endtask : drive_tok

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    reset();
    fork
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info(get_full_name(), $sformatf("received token %s", req.convert2string()), UVM_HIGH)
        //put command on the respective queue
        if(req.m_type_enm == TOK_CONS_DRV) begin
          m_tok_cons_q.push_back(req);
        end
        else begin
          m_tok_prod_q.push_back(req);
        end
        //send to the upper layer the information that this token was received and is on queue to be run
        seq_item_port.item_done();
      end
      begin
        drive_tok_cons();
      end
      begin
        drive_tok_prod();
      end
    join
  endtask
endclass

`endif // TOKEN_AGENT_DRIVER_SV


