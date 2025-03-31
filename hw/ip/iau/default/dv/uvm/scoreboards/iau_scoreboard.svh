`ifndef IAU_SCOREBOARD_SV
`define IAU_SCOREBOARD_SV
class iau_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(iau_scoreboard)

  svt_axi_transaction mon_item;  
  svt_axi_transaction mdl_item;
  iau_seq_item mon_iau_item;
  iau_seq_item mdl_iau_item;
  token_agent_seq_item tok_mon_item;
  token_agent_seq_item tok_mdl_item;

  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mdl;
  uvm_tlm_analysis_fifo#(iau_seq_item) taf_iau_mon;
  uvm_tlm_analysis_fifo#(iau_seq_item) taf_iau_mdl;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mdl_tok;

  token_agent_seq_item tok_mon_cons_item_q[$];
  token_agent_seq_item tok_mdl_cons_item_q[$];
  token_agent_seq_item tok_mon_prod_item_q[$];
  token_agent_seq_item tok_mdl_prod_item_q[$];

  int mon_irq_cnt, mdl_irq_cnt;
  bit past_irq;
  bit wait_mdl_item;

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    mon_item = new("mon_item");
    mdl_item = new("mdl_item");
    mon_iau_item = new("mon_iau_item");
    mdl_iau_item = new("mdl_iau_item");


    taf_mon = new("taf_mon", this);
    taf_mdl = new("taf_mdl", this);
    taf_iau_mon = new("taf_iau_mon", this);
    taf_iau_mdl = new("taf_iau_mdl", this);
    taf_mon_tok = new("taf_mon_tok", this);
    taf_mdl_tok = new("taf_mdl_tok", this);
  endfunction : build_phase

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork 
      forever begin
        taf_mon.get(mon_item);
        `uvm_info("iau_scb", $sformatf("mon_item: \n%s", mon_item.sprint()), UVM_HIGH)
        //ack and data status == ABORTED: reset in progress while receiving transaction 
        if (mon_item.ack_status != svt_axi_transaction::ABORTED && mon_item.data_status != svt_axi_transaction::ABORTED) begin
          wait_mdl_item = 1;
          taf_mdl.get(mdl_item);
          wait_mdl_item = 0;
          if (mdl_item.tdata.size() != mon_item.tdata.size()) begin 
            `uvm_error("iau_scb", $sformatf("data stream with unexpected size, mdl size: %0d, mon size: %0d", mdl_item.tdata.size(), mon_item.tdata.size()));
          end
          foreach(mon_item.tdata[i]) begin 
            if (mon_item.tdata[i] !== mdl_item.tdata[i]) begin
              `uvm_error("iau_scb",  $sformatf("Data mismatch.\nRef Model data[%0d]   : %h\nMonitor data[%0d]     : %h\nDiff                 : %h",
                         i, mdl_item.tdata[i], i, mon_item.tdata[i], mon_item.tdata[i]^mdl_item.tdata[i] ) );
            end else begin
              `uvm_info("iau_scb",  $sformatf("Data match.\n data[%0d]: %h",i, mon_item.tdata[i]), UVM_FULL);
            end
            
          end
        end
      end
      forever begin
        taf_iau_mon.get(mon_iau_item);
        if (!past_irq && mon_iau_item.irq_o) begin
          `uvm_info("iau_scb", "Got mon_iau_item with irq_o = 1", UVM_FULL)
          mon_irq_cnt++;
          taf_iau_mdl.get(mdl_iau_item);
          mdl_irq_cnt++;
          if (!mdl_iau_item.irq_o) begin
            `uvm_error("iau_scb", "Expected IRQ from model not asserted!")
          end else 
            `uvm_info("iau_scb", "Got irq from both mdl and rtl", UVM_FULL)
        end
        past_irq = mon_iau_item.irq_o;
      end
      
      tok_mon_get();
      tok_mdl_get();

    join
  endtask : run_phase

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    if (wait_mdl_item)
      `uvm_error("iau_scb", "got item from monitor but not from model!")

    if (!taf_mon.is_empty())
      `uvm_error("iau_scb", $sformatf("taf_mon is not empty with %0d items",taf_mon.used()))

    if (!taf_mdl.is_empty())
      `uvm_error("iau_scb", $sformatf("taf_mdl is not empty with %0d items",taf_mdl.used()))

    if (mon_irq_cnt != mdl_irq_cnt)
      `uvm_error("iau_scb", $sformatf("number of IRQ RTL vs MDL mismatch, mdl: %0d rtl: %0d",mdl_irq_cnt,mon_irq_cnt))
    if (!taf_iau_mdl.is_empty())
      `uvm_error("iau_scb", $sformatf("taf_iau_mdl is not empty with %0d items",taf_iau_mdl.used()))

    if (tok_mon_cons_item_q.size()!=0)
      `uvm_error("iau_scb", $sformatf("tok_mon_cons_item_q is not empty with %0d items",tok_mon_cons_item_q.size()))
    if (tok_mdl_cons_item_q.size()!=0)
      `uvm_error("iau_scb", $sformatf("tok_mdl_cons_item_q is not empty with %0d items",tok_mdl_cons_item_q.size()))
    if (tok_mon_prod_item_q.size()!=0)
      `uvm_error("iau_scb", $sformatf("tok_mon_prod_item_q is not empty with %0d items",tok_mon_prod_item_q.size()))
    if (tok_mdl_prod_item_q.size()!=0)
      `uvm_error("iau_scb", $sformatf("tok_mdl_prod_item_q is not empty with %0d items",tok_mdl_prod_item_q.size()))

  endfunction

  virtual task tok_mon_get();
    forever begin
      taf_mon_tok.get(tok_mon_item);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token monitor the item: \n%s", tok_mon_item.convert2string()), UVM_FULL)
      //add to queue and check
      if(tok_mon_item.m_type_enm == TOK_CONS_MON) begin
        add_mon_tok_cons_and_check(tok_mon_item);
      end
      else begin
        add_mon_tok_prod_and_check(tok_mon_item);
      end
    end
  endtask : tok_mon_get

  virtual task tok_mdl_get();
    forever begin
      taf_mdl_tok.get(tok_mdl_item);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token model the item: \n%s", tok_mdl_item.convert2string()), UVM_FULL)
      //add to queue and check
      if(tok_mdl_item.m_type_enm == TOK_CONS_MON) begin
        add_mdl_tok_cons_and_check(tok_mdl_item);
      end
      else begin
        add_mdl_tok_prod_and_check(tok_mdl_item);
      end
    end
  endtask : tok_mdl_get

  virtual function void add_mon_tok_cons_and_check(token_agent_seq_item p_tok_item);
    //add to mon tok_cons_q
    tok_mon_cons_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mon_tok_cons_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_cons_item_q.size(), tok_mdl_cons_item_q.size()), UVM_FULL)
    tok_check(tok_mon_cons_item_q, tok_mdl_cons_item_q);
  endfunction : add_mon_tok_cons_and_check

  virtual function void add_mdl_tok_cons_and_check(token_agent_seq_item p_tok_item);
    //add to mdl tok_cons_q
    tok_mdl_cons_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mdl_tok_cons_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_cons_item_q.size(), tok_mdl_cons_item_q.size()), UVM_FULL)
    tok_check(tok_mon_cons_item_q, tok_mdl_cons_item_q);
  endfunction : add_mdl_tok_cons_and_check

  virtual function void add_mon_tok_prod_and_check(token_agent_seq_item p_tok_item);
    //add to mon tok_prod_q
    tok_mon_prod_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mon_tok_prod_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_prod_item_q.size(), tok_mdl_prod_item_q.size()), UVM_FULL)
    tok_check(tok_mon_prod_item_q, tok_mdl_prod_item_q);
  endfunction : add_mon_tok_prod_and_check

  virtual function void add_mdl_tok_prod_and_check(token_agent_seq_item p_tok_item);
    //add to mdl tok_prod_q
    tok_mdl_prod_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mdl_tok_prod_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_prod_item_q.size(), tok_mdl_prod_item_q.size()), UVM_FULL)
    tok_check(tok_mon_prod_item_q, tok_mdl_prod_item_q);
  endfunction : add_mdl_tok_prod_and_check


  virtual function void tok_check(ref token_agent_seq_item p_tok_mon_item_q[$], ref token_agent_seq_item p_tok_mdl_item_q[$]);
    //if both queues have more than one position, compare type of the transaction
    if((p_tok_mon_item_q.size>0) && (p_tok_mdl_item_q.size>0)) begin
      token_agent_seq_item l_mon_item, l_mdl_item;
      l_mon_item = p_tok_mon_item_q.pop_front();
      l_mdl_item = p_tok_mdl_item_q.pop_front();
      if(l_mon_item.m_type_enm != l_mdl_item.m_type_enm) begin
        `uvm_error("iau_scb", $sformatf("Token enum type of monitor and model are different. Mon: %s and Mdl: %s", l_mon_item.m_type_enm.name(), l_mdl_item.m_type_enm.name() ));
      end
      else begin
        `uvm_info("TOK_DBG_SB", $sformatf("Compared the two items and the tokens are equal (%s). Mon: %0d and Mdl: %0d ", l_mon_item.m_type_enm.name(), p_tok_mon_item_q.size(), p_tok_mdl_item_q.size()), UVM_FULL)
      end
    end
  endfunction : tok_check

endclass
`endif
