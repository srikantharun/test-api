`ifndef AI_CORE_MVM_SCOREBOARD_SV
`define AI_CORE_MVM_SCOREBOARD_SV
`uvm_analysis_imp_decl(_actual_data)
`uvm_analysis_imp_decl(_expected_data)

class ai_core_mvm_scoreboard extends uvm_scoreboard;

  /** Analysis port connected to the AXI IAU SLAVE Agent */
  uvm_analysis_imp_actual_data#(svt_axi_transaction, ai_core_mvm_scoreboard) actual_data_export;

  /** Analysis port conneted to the ref model */
  uvm_analysis_imp_expected_data#(svt_axi_transaction, ai_core_mvm_scoreboard) expected_data_export;
  
  /** Analysis port to receive transactions from monitor */
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok[VERIF_MVM_NUM_TOK_AGENTS];
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mdl_tok[VERIF_MVM_NUM_TOK_AGENTS];

  /** UVM Component Utility macro */
  `uvm_component_utils(ai_core_mvm_scoreboard)
  svt_axi_transaction act_xact[$];
  svt_axi_transaction exp_xact[$];
  int num_of_act_pkts;
  int num_of_exp_pkts;
  
  // mvm user Inteface Handle
  virtual mvm_if mvm_if;
  
  token_agent_seq_item m_tok_mon_item[VERIF_MVM_NUM_TOK_AGENTS];
  token_agent_seq_item m_tok_mdl_item[VERIF_MVM_NUM_TOK_AGENTS];
  token_agent_seq_item m_tok_cons_mon_q[VERIF_MVM_NUM_TOK_AGENTS][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS][$];
  token_agent_seq_item m_tok_prod_mon_q[VERIF_MVM_NUM_TOK_AGENTS][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS][$];
  token_agent_seq_item m_tok_cons_mdl_q[VERIF_MVM_NUM_TOK_AGENTS][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS][$];
  token_agent_seq_item m_tok_prod_mdl_q[VERIF_MVM_NUM_TOK_AGENTS][token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS][$];

  function new(string name = "ai_core_mvm_scoreboard", uvm_component parent = null);
    super.new(name, parent);
    /** Construct the analysis ports */
    actual_data_export = new("actual_data_export", this);
    expected_data_export  = new("expected_data_export", this);

    foreach (taf_mon_tok[i]) begin
      taf_mon_tok[i] = new($sformatf("taf_mon_tok[%0d]", i), this);
    end
    foreach (taf_mdl_tok[i]) begin
      taf_mdl_tok[i] = new($sformatf("taf_mdl_tok[%0d]", i), this);
    end
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build();
    // Recieve mvm user interface handle
    uvm_config_db#(virtual mvm_if)::get(uvm_root::get(), "uvm_test_top", "mvm_if", mvm_if);
  endfunction

  virtual function void write_actual_data(input svt_axi_transaction xact);
    int index = num_of_act_pkts;
    if (!$cast(act_xact[num_of_act_pkts], xact.clone())) begin
      `uvm_fatal("SB_ACT_DATA",
                 "Unable to $cast the received transaction to actual svt_axi_transaction");
    end
    `uvm_info("SB_ACT_DATA", $sformatf("act_xact[%0d]:\n%s", num_of_act_pkts,act_xact[num_of_act_pkts].sprint()), UVM_MEDIUM)
    
    

      if ( $test$plusargs("IRQ_testing_so_no_data_checks") ) //TODO in next project for IRQ 
      `uvm_info("SB_NO_CHECK", $sformatf("IRQ_testing_so_no_data_checks num_of_act_pkts=%0d,num_of_exp_pkts=%0d",num_of_act_pkts,num_of_exp_pkts), UVM_HIGH)
       else if(num_of_act_pkts < num_of_exp_pkts) begin
         if(act_xact[index].tdata.size() != exp_xact[index].tdata.size()) begin
           `uvm_error(get_type_name, $sformatf("Actual pkt size = %0d and Expected pkt size=%0d are not matched",act_xact[index].tdata.size(),exp_xact[index].tdata.size()))
         end
         foreach (act_xact[index].tdata[i]) begin
           if (act_xact[index].tdata[i] == exp_xact[index].tdata[i]) begin
             `uvm_info("SB_COMPARE_PASSED", $sformatf("\n  actual_data[%0d]=%0h  is matched with \nexpected_data[%0d]=%0h", i,act_xact[index].tdata[i],i,exp_xact[index].tdata[i]), UVM_HIGH)
           end else begin
             `uvm_error("SB_COMPARE_FAILED", $sformatf("\n  actual_data[%0d]=%0h is not matched with \nexpected_data[%0d]=%0h", i,act_xact[index].tdata[i],i,exp_xact[index].tdata[i]))
           end
         end
      end

    
    num_of_act_pkts++;
    `uvm_info("SB_COUNT", $sformatf("num_of_act_pkts=%0d",num_of_act_pkts), UVM_DEBUG)
  endfunction : write_actual_data

  virtual function void write_expected_data(input svt_axi_transaction xact);
    int index = num_of_exp_pkts;

    if (!$cast(exp_xact[num_of_exp_pkts], xact.clone())) begin
      `uvm_fatal("SB_EXP_DATA",
                 "Unable to $cast the received transaction to expected svt_axi_transaction");
    end
    begin
      `uvm_info("SB_EXP_DATA", $sformatf("exp_xact[%0d]:\n%s",num_of_exp_pkts, exp_xact[num_of_exp_pkts].sprint()), UVM_MEDIUM)
    end
    if ( $test$plusargs("IRQ_testing_so_no_data_checks") ) //TODO in next project for IRQ
    `uvm_info("SB_NO_CHECK", $sformatf("IRQ_testing_so_no_data_checks num_of_act_pkts=%0d,num_of_exp_pkts=%0d",num_of_act_pkts,num_of_exp_pkts), UVM_HIGH)
    else if(num_of_exp_pkts < num_of_act_pkts) begin
      if(act_xact[index].tdata.size() != exp_xact[index].tdata.size()) begin
        `uvm_error(get_type_name, $sformatf("Actual pkt size = %0d and Expected pkt size=%0d are not matched",act_xact[index].tdata.size(),exp_xact[index].tdata.size()))
      end
      foreach (act_xact[index].tdata[i]) begin
        if (act_xact[index].tdata[i] == exp_xact[index].tdata[i]) begin
          `uvm_info("SB_COMPARE_PASSED", $sformatf("\n  actual_data[%0d]=%0h  is matched with \nexpected_data[%0d]=%0h", i,act_xact[index].tdata[i],i,exp_xact[index].tdata[i]), UVM_HIGH)
        end else begin
          `uvm_error("SB_COMPARE_FAILED", $sformatf("\n  actual_data[%0d]=%0h is not matched with \nexpected_data[%0d]=%0h", i,act_xact[index].tdata[i],i,exp_xact[index].tdata[i]))
        end
      end
    end
    num_of_exp_pkts++;
    `uvm_info("SB_COUNT", $sformatf("num_of_exp_pkts=%0d",num_of_exp_pkts), UVM_DEBUG)
  endfunction : write_expected_data

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      //call token manager scoreboard
      tok_exe_mon_get();
      tok_prg_mon_get();
      tok_exe_mdl_get();
      tok_prg_mdl_get();
    join
  endtask : run_phase
  
  virtual task tok_exe_mon_get();
    int l_index = VERIF_MVM_EXE_TOK_AGT;
    forever begin
      taf_mon_tok[l_index].get(m_tok_mon_item[l_index]);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token execution monitor the item: \n%s", m_tok_mon_item[l_index].convert2string()), UVM_HIGH)
      //add to a queue of tokens and check against the model
      add_tok_mon_and_check(m_tok_mon_item[l_index], l_index);
    end
  endtask : tok_exe_mon_get

  virtual task tok_prg_mon_get();
    int l_index = VERIF_MVM_PRG_TOK_AGT;
    forever begin
      taf_mon_tok[l_index].get(m_tok_mon_item[l_index]);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token program monitor the item: \n%s", m_tok_mon_item[l_index].convert2string()), UVM_HIGH)
      //add to a queue of tokens and check against the model
      add_tok_mon_and_check(m_tok_mon_item[l_index], l_index);
    end
  endtask : tok_prg_mon_get


  virtual task tok_exe_mdl_get();
    int l_index = VERIF_MVM_EXE_TOK_AGT;
    forever begin
      taf_mdl_tok[l_index].get(m_tok_mdl_item[l_index]);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token execution model the item: \n%s", m_tok_mdl_item[l_index].convert2string()), UVM_HIGH)
      //add to a queue of tokens and check against the model
      add_tok_mdl_and_check(m_tok_mdl_item[l_index], l_index);
    end
  endtask : tok_exe_mdl_get
  
  virtual task tok_prg_mdl_get();
    int l_index = VERIF_MVM_PRG_TOK_AGT;
    forever begin
      taf_mdl_tok[l_index].get(m_tok_mdl_item[l_index]);
      `uvm_info("TOK_DBG_SB", $sformatf("received from token program model the item: \n%s", m_tok_mdl_item[l_index].convert2string()), UVM_HIGH)
      //add to a queue of tokens and check against the model
      add_tok_mdl_and_check(m_tok_mdl_item[l_index], l_index);
    end
  endtask : tok_prg_mdl_get
  
  virtual function void add_tok_mon_and_check(token_agent_seq_item p_tok_item, int p_index) ;
    string l_str_aux;
      //convert the number that is on the name of the token to a number
      l_str_aux= p_tok_item.m_tok_path_name[p_tok_item.m_tok_path_name.len()-2];
      //disabling adding token to queue while flush operation is going
      if(mvm_if.mvm_flush_oprt==0) begin
        //add to a queue of tokens to be compared
        if(p_tok_item.m_type_enm == TOK_CONS_MON) begin
          `uvm_info("TOK_DBG_SB", $sformatf("add a new position to m_tok_cons_mon_q[%0d][%0d]", p_index, l_str_aux.atoi()), UVM_HIGH)
          m_tok_cons_mon_q[p_index][l_str_aux.atoi()].push_back(p_tok_item);
          tok_rm_from_queues(m_tok_cons_mon_q[p_index][l_str_aux.atoi()], m_tok_cons_mdl_q[p_index][l_str_aux.atoi()]);
        end else begin
          `uvm_info("TOK_DBG_SB", $sformatf("add a new position to m_tok_prod_mon_q[%0d][%0d]", p_index, l_str_aux.atoi()), UVM_HIGH)
          m_tok_prod_mon_q[p_index][l_str_aux.atoi()].push_back(p_tok_item);
          tok_rm_from_queues(m_tok_prod_mon_q[p_index][l_str_aux.atoi()], m_tok_prod_mdl_q[p_index][l_str_aux.atoi()]);
        end
      end

  endfunction : add_tok_mon_and_check
  
  virtual function void add_tok_mdl_and_check(token_agent_seq_item p_tok_item, int p_index) ;
    string l_str_aux;
      //convert the number that is on the name of the token to a number
      l_str_aux= p_tok_item.m_tok_path_name[p_tok_item.m_tok_path_name.len()-2];
      //disabling adding token to queue while flush operation is going
      if(mvm_if.mvm_flush_oprt==0) begin
        //add to a queue of tokens to be compared
        if(p_tok_item.m_type_enm == TOK_CONS_MON) begin
          `uvm_info("TOK_DBG_SB", $sformatf("add a new position to m_tok_cons_mdl_q[%0d][%0d]", p_index, l_str_aux.atoi()), UVM_HIGH)
          m_tok_cons_mdl_q[p_index][l_str_aux.atoi()].push_back(p_tok_item);
          tok_rm_from_queues(m_tok_cons_mon_q[p_index][l_str_aux.atoi()], m_tok_cons_mdl_q[p_index][l_str_aux.atoi()]);
        end else begin
          `uvm_info("TOK_DBG_SB", $sformatf("add a new position to m_tok_prod_mdl_q[%0d][%0d]", p_index, l_str_aux.atoi()), UVM_HIGH)
          m_tok_prod_mdl_q[p_index][l_str_aux.atoi()].push_back(p_tok_item);
          tok_rm_from_queues(m_tok_prod_mon_q[p_index][l_str_aux.atoi()], m_tok_prod_mdl_q[p_index][l_str_aux.atoi()]);
        end
      end
      //call the check

  endfunction : add_tok_mdl_and_check
  
  virtual function void tok_rm_from_queues(ref token_agent_seq_item p_tok_mon_item_q[$], ref token_agent_seq_item p_tok_mdl_item_q[$]);
    //if both queues have more than one position, compare type of the transaction
    if((p_tok_mon_item_q.size>0) && (p_tok_mdl_item_q.size>0)) begin
      token_agent_seq_item l_mon_item, l_mdl_item;
      l_mon_item = p_tok_mon_item_q.pop_front();
      l_mdl_item = p_tok_mdl_item_q.pop_front();
    end
  endfunction : tok_rm_from_queues

  function void check_phase(uvm_phase phase);
    if ( $test$plusargs("no_refmodel_check_for_exe_software_bypass") || $test$plusargs("IRQ_testing_so_no_data_checks") )  //TODO in next project
      `uvm_info("SB_NO_CHECK", $sformatf("no_data_checks num_of_act_pkts=%0d,num_of_exp_pkts=%0d",num_of_act_pkts,num_of_exp_pkts), UVM_HIGH)
    else if(num_of_act_pkts != num_of_exp_pkts )
      `uvm_error("SB_CHECK", $sformatf("num_of_act_pkts=%0d,num_of_exp_pkts=%0d",num_of_act_pkts,num_of_exp_pkts))
    else
      `uvm_info("SB_CHECK", $sformatf("num_of_act_pkts=%0d,num_of_exp_pkts=%0d",num_of_act_pkts,num_of_exp_pkts), UVM_HIGH)
    
    foreach (m_tok_cons_mon_q[i,j]) begin
      if (m_tok_cons_mon_q[i][j].size()!=0)
        `uvm_error("SB_CHECK", $sformatf("m_tok_cons_mon_q[%0d][%0d] is not empty with %0d items",i, j, m_tok_cons_mon_q[i][j].size()))
    end
    foreach (m_tok_prod_mon_q[i,j]) begin
      if (m_tok_prod_mon_q[i][j].size()!=0)
        `uvm_error("SB_CHECK", $sformatf("m_tok_prod_mon_q[%0d][%0d] is not empty with %0d items",i, j, m_tok_prod_mon_q[i][j].size()))
    end
    foreach (m_tok_cons_mdl_q[i,j]) begin
      if (m_tok_cons_mdl_q[i][j].size()!=0)
        `uvm_error("SB_CHECK", $sformatf("m_tok_cons_mdl_q[%0d][%0d] is not empty with %0d items",i, j, m_tok_cons_mdl_q[i][j].size()))
    end
    foreach (m_tok_prod_mdl_q[i,j]) begin
      if (m_tok_prod_mdl_q[i][j].size()!=0)
        `uvm_error("SB_CHECK", $sformatf("m_tok_prod_mdl_q[%0d][%0d] is not empty with %0d items",i, j, m_tok_prod_mdl_q[i][j].size()))
    end
  endfunction
endclass  // axi_uvm_scoreboard
`endif

