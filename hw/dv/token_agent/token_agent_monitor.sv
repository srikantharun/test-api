`ifndef TOKEN_AGENT_MONITOR_SV
`define TOKEN_AGENT_MONITOR_SV

class token_agent_monitor extends uvm_monitor;
  `uvm_component_utils(token_agent_monitor)

  string m_parent_name;
  token_agent_config m_tok_cfg;

  virtual token_agent_if m_vif;

  uvm_analysis_port#(token_agent_seq_item) ap;

  token_agent_seq_item m_cons_trans;
  token_agent_seq_item m_prod_trans;

  function new (string name, uvm_component parent);
    super.new (name, parent);
    m_parent_name = parent.get_name();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
    m_cons_trans = token_agent_seq_item::type_id::create("m_cons_trans", this);
    m_prod_trans = token_agent_seq_item::type_id::create("m_prod_trans", this);

    if ( ! uvm_config_db#( token_agent_config )::get( .cntxt( this ), .inst_name( "" ), .field_name( "tok_agt_cfg" ), .value( m_tok_cfg ) ) ) begin
      `uvm_fatal(get_full_name(), $sformatf("Configuration was not passed using uvm_config_db"));
    end
  endfunction : build_phase

  virtual task monitor_cons ();
    int l_bv_delay_counter;

    if(m_tok_cfg.m_b_cons_active) begin
      `uvm_info(get_full_name(), $sformatf("Entering on monitor_cons"), UVM_HIGH)
      forever @(m_vif.mon) begin
        //verify if input is high
        if(m_vif.mon.tok_cons_rdy === 1) begin
          //reset delay variable
          l_bv_delay_counter = 0;
          fork
            begin
              //if the ouput is already equal to 1 end this loop
              while (m_vif.mon.tok_cons_vld === 1'b0) begin
                //increment the delay counter
                l_bv_delay_counter++;
                @(m_vif.mon);
              end
              //fill and send the transaction to the analysis port
              m_cons_trans.m_type_enm = TOK_CONS_MON;
              m_cons_trans.m_bv_delay = l_bv_delay_counter;
              m_cons_trans.m_tok_path_name = m_parent_name;
              ap.write(m_cons_trans.do_clone());
              `uvm_info(get_full_name(), $sformatf("Sending to SB on monitor_cons"), UVM_LOW)
            end
            begin
              #(m_tok_cfg.m_cons_timeout);
              `uvm_error(get_full_name(), "The timeout waiting for posedge of tok_cons_vld was achieved!")
            end
          join_any
          disable fork;
        end
      end
    end
  endtask : monitor_cons

  virtual task monitor_prod ();
    int l_bv_delay_counter;

    if(m_tok_cfg.m_b_prod_active) begin
      `uvm_info(get_full_name(), $sformatf("Entering on monitor_prod"), UVM_HIGH)
      forever @(m_vif.mon) begin
        //verify if input is high
        if(m_vif.mon.tok_prod_vld===1) begin
          //reset delay variable
          l_bv_delay_counter = 0;
          fork
            begin
              //if the ouput is already equal to 1 end this loop
              while (m_vif.mon.tok_prod_rdy === 1'b0) begin
                //increment the delay counter
                l_bv_delay_counter++;
                @(m_vif.mon);
              end
              //fill and send the transaction to the analysis port
              m_prod_trans.m_type_enm = TOK_PROD_MON;
              m_prod_trans.m_bv_delay = l_bv_delay_counter;
              m_prod_trans.m_tok_path_name = m_parent_name;
              ap.write(m_prod_trans.do_clone());
              `uvm_info(get_full_name(), $sformatf("Sending to SB on monitor_prod"), UVM_LOW)
            end
            begin
              #(m_tok_cfg.m_prod_timeout);
              `uvm_error(get_full_name(), "The timeout waiting for posedge of tok_prod_rdy was achieved!")
            end
          join_any
          disable fork;
        end
      end
    end
  endtask : monitor_prod

  virtual task monitor_reset ();
    //monitor a reset negedge and finish this task. By finishing this task it will restart all over again the monitor tasks
    @(negedge m_vif.reset_n);
    `uvm_info(get_full_name(), $sformatf("Reset was seen on the token interface and monitor will be reset"), UVM_MEDIUM)
    @(posedge m_vif.reset_n);
    `uvm_info(get_full_name(), $sformatf("Reset done!"), UVM_MEDIUM)
  endtask : monitor_reset

  virtual task run_phase(uvm_phase phase);
    bit init_done;
    super.run_phase(phase);
    forever begin
      if (m_tok_cfg.m_b_init_reset && init_done==0) begin
        monitor_reset();
        init_done = 1;
      end
      fork
        begin
          fork
            monitor_cons();
            monitor_prod();
          join
        end
        monitor_reset();
      join_any
      disable fork;
    end
  endtask : run_phase
endclass : token_agent_monitor



`endif // TOKEN_AGENT_MONITOR_SV
