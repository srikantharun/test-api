`ifndef DWPU_SCOREBOARD_SV
`define DWPU_SCOREBOARD_SV
class ai_core_dwpu_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(ai_core_dwpu_scoreboard)

  svt_axi_transaction mon_cfg_item;
  svt_axi_transaction mon_cfg_item_aux;
  svt_axi_transaction mon_item;
  svt_axi_transaction mdl_item;
  ai_core_dwpu_seq_item mon_dwpu_item;
  ai_core_dwpu_seq_item mdl_dwpu_item;
  token_agent_seq_item tok_mon_item;
  token_agent_seq_item tok_mdl_item;
  axi_lp_data_t m_prog_mem[int];

  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_cfg;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mdl;
  uvm_tlm_analysis_fifo#(ai_core_dwpu_seq_item) taf_mon_dwpu;
  uvm_tlm_analysis_fifo#(ai_core_dwpu_seq_item) taf_mdl_dwpu;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mdl_tok;
  token_agent_seq_item tok_mon_cons_item_q[$];
  token_agent_seq_item tok_mdl_cons_item_q[$];
  token_agent_seq_item tok_mon_prod_item_q[$];
  token_agent_seq_item tok_mdl_prod_item_q[$];

  int mon_cnt, mdl_cnt;
  int mon_irq_cnt, mdl_irq_cnt;
  bit past_irq;

  // reset handling
  event m_rst_evt;
  event m_rst_done_evt;
  bit   m_is_rst;

  //verbosity options
  uvm_verbosity dp_dbg_verbosity = UVM_DEBUG;
  uvm_verbosity tok_dbg_verbosity = UVM_DEBUG;
  typedef uvm_enum_wrapper#(uvm_verbosity) verbosity_wrapper;

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    mon_cfg_item      = svt_axi_transaction::type_id::create("mon_cfg_item");
    mon_cfg_item_aux  = svt_axi_transaction::type_id::create("mon_cfg_item_aux");
    mon_item          = svt_axi_transaction::type_id::create("mon_item");
    mdl_item          = svt_axi_transaction::type_id::create("mdl_item");
    mon_dwpu_item     = ai_core_dwpu_seq_item::type_id::create("mon_dwpu_item");
    mdl_dwpu_item     = ai_core_dwpu_seq_item::type_id::create("mdl_dwpu_item");

    taf_mon_cfg = new("taf_mon_cfg", this);
    taf_mon = new("taf_mon", this);
    taf_mdl = new("taf_mdl", this);
    taf_mon_dwpu = new("taf_mon_dwpu", this);
    taf_mdl_dwpu = new("taf_mdl_dwpu", this);
    taf_mon_tok = new("taf_mon_tok", this);
    taf_mdl_tok = new("taf_mdl_tok", this);
  endfunction : build_phase
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    uvm_config_db#(uvm_verbosity)::get(this, "", "dp_dbg_verbosity", dp_dbg_verbosity);
    uvm_config_db#(uvm_verbosity)::get(this, "", "tok_dbg_verbosity", tok_dbg_verbosity);
  endfunction : connect_phase

  virtual task tok_mon_get();
    forever begin
      taf_mon_tok.get(tok_mon_item);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token monitor the item: \n%s", tok_mon_item.convert2string()), tok_dbg_verbosity)
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
      `uvm_info("DATA_DBG_SB", $sformatf("received from token model the item: \n%s", tok_mdl_item.convert2string()), tok_dbg_verbosity)
      //add to queue and check
      if(tok_mdl_item.m_type_enm == TOK_CONS_MON) begin
        add_mdl_tok_cons_and_check(tok_mdl_item);
      end
      else begin
        add_mdl_tok_prod_and_check(tok_mdl_item);
      end
    end
  endtask : tok_mdl_get

  virtual task taf_mon_cfg_get();
    forever begin
      taf_mon_cfg.get(mon_cfg_item_aux);
      mon_cfg_item.do_copy(mon_cfg_item_aux);
      `uvm_info("DATA_DBG_SB", $sformatf("received from axi configuration monitor the item: \n%s", mon_cfg_item.sprint()), UVM_DEBUG)
      //decode address
      decode_addr(mon_cfg_item);
    end
  endtask : taf_mon_cfg_get

  function void decode_addr(svt_axi_transaction a_trans);
    axi_lp_addr_t l_addr;
    axi_lp_addr_t l_addr_prog_mem;
    axi_lp_data_t l_data_aux;
    bit l_err_in_resp;

    l_addr = a_trans.addr;
    //analise if the write address will cross program memory boundaries
    if(a_trans.xact_type==svt_axi_master_transaction::WRITE) begin
      if(l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_END_ADDR]}) begin
        if(l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_REGION_END]}) begin
          if(((l_addr+(a_trans.burst_length*8)-8) > DWPU_IMEM_REGION_END) && (a_trans.bresp != svt_axi_master_transaction::SLVERR)) begin
            `uvm_error("dwpu_scb",  $sformatf("Response mismatch into a write operation that starts at 0x%0x (inside program memory) and ends outside (0x%0x). Monitored bresp = %s and expected bresp = %s",
              l_addr, l_addr+(a_trans.burst_length*8)-8, a_trans.bresp.name(), "SLVERR") );
          end
          else if(((l_addr+(a_trans.burst_length*8)-8) inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_REGION_END]}) && (a_trans.bresp != svt_axi_master_transaction::OKAY)) begin
            `uvm_error("dwpu_scb",  $sformatf("Response mismatch into a write operation that starts and ends inside program memory. Monitored bresp = %s and expected bresp = %s",
              a_trans.bresp.name(), "OKAY") );
          end
          else begin
            `uvm_info("dwpu_scb", $sformatf("Bresp match to address 0x%0x",l_addr), UVM_MEDIUM)
          end
        end
        else begin
          if(a_trans.bresp != svt_axi_master_transaction::SLVERR) begin
            `uvm_error("dwpu_scb",  $sformatf("Response mismatch into a write operation for address 0x%0x (outside program memory). Monitored bresp = %s and expected bresp = %s",
              l_addr, a_trans.bresp.name(), "SLVERR") );
          end
        end
      end 
    end

    //iterate through the data
    foreach (a_trans.data[i]) begin
      `uvm_info("dwpu_scb", $sformatf("Decoding addr: %0h, data: %0h", l_addr, a_trans.data[i]), UVM_MEDIUM)
      //analise if the read address will cross program memory boundaries
      if(a_trans.xact_type==svt_axi_master_transaction::READ) begin
        if(l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_END_ADDR]}) begin
          if((l_addr > DWPU_IMEM_REGION_END) && (a_trans.rresp[i] != svt_axi_master_transaction::SLVERR)) begin
            `uvm_error("dwpu_scb",  $sformatf("Response mismatch into a read operation for address 0x%0x (outside program memory). Monitored rresp[%0d] = %s and expected rresp = %s",
              l_addr, i, a_trans.rresp[i].name(), "SLVERR") );
          end
          else if((l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_REGION_END]}) && (a_trans.rresp[i] != svt_axi_master_transaction::OKAY)) begin
            `uvm_error("dwpu_scb",  $sformatf("Response mismatch into a read operation for address 0x%0x (inside program memory). Monitored rresp[%0d] = %s and expected bresp = %s",
              l_addr, i, a_trans.rresp[i].name(), "OKAY") );
          end
          else begin
            `uvm_info("dwpu_scb", $sformatf("Rresp match to address 0x%0x",l_addr), UVM_MEDIUM)
          end
        end
      end

      //if the address is from program memory
      if (l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_REGION_END]}) begin
        l_addr_prog_mem = l_addr-(DWPU_IMEM_ST_ADDR);
        if(a_trans.xact_type == svt_axi_transaction::WRITE) begin
          //update array of data with information
          l_data_aux = a_trans.data[i];
          `uvm_info("dwpu_scb", $sformatf("Write into prog mem addr = 0x%0x Data 0x%0x and wstrb = 0x%0x (value after strobe)",l_addr_prog_mem/8, l_data_aux, a_trans.wstrb[i]), UVM_MEDIUM)
          for(int strb_idx = 0; strb_idx< AXI_LT_DATA_WIDTH/8; strb_idx++) begin
            if(a_trans.wstrb[i][strb_idx]==1) begin
              m_prog_mem[l_addr_prog_mem/8][((8*(strb_idx+1)) - 1) -: 8] = l_data_aux[((8*(strb_idx+1)) - 1) -: 8];
            end
          end
          `uvm_info("dwpu_scb", $sformatf("Write into prog iddr = 0x%0x Data 0x%0x (value after strobe)",l_addr_prog_mem/8, m_prog_mem[l_addr_prog_mem/8]), UVM_MEDIUM)
        end
        else begin
          if(m_prog_mem.exists(l_addr_prog_mem/8)) begin
            //compare data read with data in m_prog_mem
            if(m_prog_mem[l_addr_prog_mem/8] != a_trans.data[i]) begin
              `uvm_error("dwpu_scb",  $sformatf("Data mismatch into address 0x%0x from program memory.\nData written : 0x%0x and Data read : 0x%0x",
                l_addr_prog_mem/8, m_prog_mem[l_addr_prog_mem/8], a_trans.data[i]) );
            end
            else begin
              `uvm_info("dwpu_scb", $sformatf("Program Data match to address 0x%0x",l_addr_prog_mem/8), UVM_MEDIUM)
            end
          end
        end
      end

      //update address from transaction
      if (mon_cfg_item.burst_type != svt_axi_transaction::FIXED) begin
        l_addr+=8;
      end
    end
  endfunction : decode_addr

  virtual task run_sb();
    fork
      forever begin
        taf_mon.get(mon_item);
        mon_cnt++;
        `uvm_info("dwpu_scb", $sformatf("mon_item: \n%s", mon_item.sprint()), UVM_DEBUG)
        foreach (mon_item.tdata[i]) begin
          `uvm_info("dwpu_scb", $sformatf("mon_item: tdata[%0d]=%0d", i, mon_item.tdata[i]), dp_dbg_verbosity)
        end
        taf_mdl.get(mdl_item);
        `uvm_info("dwpu_scb", $sformatf("mdl_item: \n%s", mdl_item.sprint()), UVM_DEBUG)
        foreach (mdl_item.tdata[i]) begin
          `uvm_info("dwpu_scb", $sformatf("mdl_item: tdata[%0d]=%0d", i, mdl_item.tdata[i]), dp_dbg_verbosity)
        end
        mdl_cnt++;
        if (mdl_item.tdata.size() != mon_item.tdata.size()) begin
          `uvm_error("dwpu_scb", $sformatf("data stream with unexpected size, mdl size: %0d, rtl size: %0d", mdl_item.tdata.size(), mon_item.tdata.size()));
        end
        foreach(mon_item.tdata[i]) begin
          if (mon_item.tdata[i] !== mdl_item.tdata[i]) begin
            for (int j = 0; j < NUM_CHANNELS; j++) begin
              if (mon_item.tdata[i][j * DWPU_OUT_WORD_DW +: DWPU_OUT_WORD_DW] !== mdl_item.tdata[i][j * DWPU_OUT_WORD_DW +: DWPU_OUT_WORD_DW]) begin
                `uvm_error("dwpu_scb",  $sformatf("Data mismatch.\nChannel: %0d data[%0d] mdl: %0h rtl: %0h",
                       j,i, mdl_item.tdata[i][j * DWPU_OUT_WORD_DW +: DWPU_OUT_WORD_DW], mon_item.tdata[i][j * DWPU_OUT_WORD_DW +: DWPU_OUT_WORD_DW]) );
                break; //just print first occurence
              end
            end
          end else begin
            `uvm_info("dwpu_scb",  $sformatf("Calculation Data match.\n data[%0d]: %h",i, mon_item.tdata[i]), dp_dbg_verbosity);
          end
        end
      end
      forever begin
        taf_mon_dwpu.get(mon_dwpu_item);
        if(mon_dwpu_item.trace_vld_o) begin
          taf_mdl_dwpu.get(mdl_dwpu_item);
          if (!mdl_dwpu_item.trace_vld_o) begin
            `uvm_error("dwpu_scb", "Expected trace valid from model not asserted!")
          end else begin
            `uvm_info("dwpu_scb", "Got trace valid from both mdl and rtl", UVM_NONE)
          end
        end
        else begin
          if (!past_irq && mon_dwpu_item.irq_o) begin
            `uvm_info("dwpu_scb", $sformatf("Got mon_dwpu_item with irq_o = 1"), UVM_FULL)
            mon_irq_cnt++;
            taf_mdl_dwpu.get(mdl_dwpu_item);
            mdl_irq_cnt++;
            if (!mdl_dwpu_item.irq_o) begin
              `uvm_error("dwpu_scb", "Expected IRQ from model not asserted!")
            end else begin
              `uvm_info("dwpu_scb", "Got irq from both mdl and rtl", UVM_FULL)
            end
          end
          past_irq = mon_dwpu_item.irq_o;
        end
      end
      //call token manager scoreboard
      tok_mon_get();
      tok_mdl_get();
      //call axi configuration scoreboard
      taf_mon_cfg_get();
    join
  endtask : run_sb

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    forever begin
      `uvm_info(get_name(), "Running sb!", UVM_DEBUG)
      fork
        run_sb();
        @ (m_rst_evt); // triggered by the user
      join_any
      disable fork;
      `uvm_info(get_name(), "Reset detected", UVM_HIGH)
      m_is_rst = 1;
      @ (m_rst_done_evt); // triggered by the user
      m_is_rst = 0;
      reset_scb();
      `uvm_info(get_name(), "Reset done!", UVM_HIGH)
    end
  endtask

  function void reset_scb();
    int counter;
    while (taf_mon_tok.try_get(tok_mon_item))begin
      `uvm_info(get_name(), $sformatf("Got reset tok_mon_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mdl_tok.try_get(tok_mdl_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset tok_mdl_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mdl.try_get(mdl_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset mdl_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mon.try_get(mon_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset mon_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mon_dwpu.try_get(mon_dwpu_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset mon_dwpu_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mdl_dwpu.try_get(mdl_dwpu_item)) begin
      `uvm_info(get_name(), $sformatf("Got reset mdl_dwpu_item: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    counter = 0;
    while(taf_mon_cfg.try_get(mon_cfg_item_aux)) begin
      `uvm_info(get_name(), $sformatf("Got reset mon_cfg_item_aux: %0d", counter), UVM_DEBUG)
      counter += 1;
    end
    mon_cnt = 0;
    mdl_cnt = 0;
    mon_irq_cnt = 0;
    mdl_irq_cnt = 0;
    past_irq = 0;
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    if (!taf_mon.is_empty())
      `uvm_error("dwpu_scb", $sformatf("taf_mon is not empty with %0d items",taf_mon.used()))

    if (!taf_mdl.is_empty())
      `uvm_error("dwpu_scb", $sformatf("taf_mdl is not empty with %0d items",taf_mdl.used()))

    if (mon_cnt != mdl_cnt)
      `uvm_error("dwpu_scb", $sformatf("number of received items RTL vs MDL mismatch, mdl: %0d rtl: %0d",mdl_cnt,mon_cnt))
    if (mon_irq_cnt != mdl_irq_cnt)
      `uvm_error("dwpu_scb", $sformatf("number of IRQ received RTL vs MDL mismatch, mdl: %0d rtl: %0d",mdl_irq_cnt,mon_irq_cnt))
    if (!taf_mdl_dwpu.is_empty())
      `uvm_error("dwpu_scb", $sformatf("taf_mdl_dwpu is not empty with %0d items",taf_mdl_dwpu.used()))

    if (tok_mon_cons_item_q.size()!=0)
      `uvm_error("dwpu_scb", $sformatf("tok_mon_cons_item_q is not empty with %0d items",tok_mon_cons_item_q.size()))
    if (tok_mdl_cons_item_q.size()!=0)
      `uvm_error("dwpu_scb", $sformatf("tok_mdl_cons_item_q is not empty with %0d items",tok_mdl_cons_item_q.size()))
    if (tok_mon_prod_item_q.size()!=0)
      `uvm_error("dwpu_scb", $sformatf("tok_mon_prod_item_q is not empty with %0d items",tok_mon_prod_item_q.size()))
    if (tok_mdl_prod_item_q.size()!=0)
      `uvm_error("dwpu_scb", $sformatf("tok_mdl_prod_item_q is not empty with %0d items",tok_mdl_prod_item_q.size()))
  endfunction

  virtual function void add_mon_tok_cons_and_check(token_agent_seq_item p_tok_item);
    //add to mon tok_cons_q
    tok_mon_cons_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mon_tok_cons_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_cons_item_q.size(), tok_mdl_cons_item_q.size()), tok_dbg_verbosity)
    tok_check(tok_mon_cons_item_q, tok_mdl_cons_item_q);
  endfunction : add_mon_tok_cons_and_check

  virtual function void add_mdl_tok_cons_and_check(token_agent_seq_item p_tok_item);
    //add to mdl tok_cons_q
    tok_mdl_cons_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mdl_tok_cons_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_cons_item_q.size(), tok_mdl_cons_item_q.size()), tok_dbg_verbosity)
    tok_check(tok_mon_cons_item_q, tok_mdl_cons_item_q);
  endfunction : add_mdl_tok_cons_and_check

  virtual function void add_mon_tok_prod_and_check(token_agent_seq_item p_tok_item);
    //add to mon tok_prod_q
    tok_mon_prod_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mon_tok_prod_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_prod_item_q.size(), tok_mdl_prod_item_q.size()), tok_dbg_verbosity)
    tok_check(tok_mon_prod_item_q, tok_mdl_prod_item_q);
  endfunction : add_mon_tok_prod_and_check

  virtual function void add_mdl_tok_prod_and_check(token_agent_seq_item p_tok_item);
    //add to mdl tok_prod_q
    tok_mdl_prod_item_q.push_back(p_tok_item);
    `uvm_info("TOK_DBG_SB", $sformatf("Entered into add_mdl_tok_prod_and_check. mon_q size: %0d and mdl_q size: %0d", tok_mon_prod_item_q.size(), tok_mdl_prod_item_q.size()), tok_dbg_verbosity)
    tok_check(tok_mon_prod_item_q, tok_mdl_prod_item_q);
  endfunction : add_mdl_tok_prod_and_check

  virtual function void tok_check(ref token_agent_seq_item p_tok_mon_item_q[$], ref token_agent_seq_item p_tok_mdl_item_q[$]);
    //if both queues have more than one position, compare type of the transaction
    if((p_tok_mon_item_q.size>0) && (p_tok_mdl_item_q.size>0)) begin
      token_agent_seq_item l_mon_item, l_mdl_item;
      l_mon_item = p_tok_mon_item_q.pop_front();
      l_mdl_item = p_tok_mdl_item_q.pop_front();
      if(l_mon_item.m_type_enm != l_mdl_item.m_type_enm) begin
        `uvm_error("dwpu_scb", $sformatf("Token enum type of monitor and model are different. Mon: %s and Mdl: %s", l_mon_item.m_type_enm.name(), l_mdl_item.m_type_enm.name() ));
      end
      else begin
        `uvm_info("TOK_DBG_SB", $sformatf("Compared the two items and the tokens are equal (%s). Mon: %0d and Mdl: %0d ", l_mon_item.m_type_enm.name(), p_tok_mon_item_q.size(), p_tok_mdl_item_q.size()), tok_dbg_verbosity)
      end
    end
  endfunction : tok_check


endclass
`endif
