// MVM basic test-case class
`ifndef __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TOKEN_TEST__
`define __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TOKEN_TEST__

/** Override environment configuration to set the token scoreboard to 1.
* This is necessary to make sure that the input stream interrupt is triggered correctly.
*/
class ai_core_mvm_env_w_token_enable_cfg extends ai_core_mvm_env_cfg;

  `uvm_object_utils(ai_core_mvm_env_w_token_enable_cfg)

  function new(string name = "ai_core_mvm_env_w_token_enable_cfg");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from ai_core_mvm_env_w_token_enable_cfg"), UVM_HIGH)
    /** Set has_scoreboard_token to 1 */
    has_scoreboard_token = 1;
  endfunction

endclass : ai_core_mvm_env_w_token_enable_cfg

class ai_core_mvm_random_matrix_multiplication_token_test extends ai_core_mvm_random_matrix_multiplication_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_random_matrix_multiplication_token_test)
  
  mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
  mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
  mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
  mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
  mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
  token_agent_cons_sequence         tok_cons_seq[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS];
  token_agent_prod_sequence         tok_prod_seq[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD];
  // Class constructor
  function new (string name="ai_core_mvm_random_matrix_multiplication_token_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_random_matrix_multiplication_token_test", "Build phase entered", UVM_HIGH)
    /** Override classes that will be created in the build phase */
    set_type_override_by_type (ai_core_mvm_env_cfg::get_type(), ai_core_mvm_env_w_token_enable_cfg::get_type());

    /** Call super */
    super.build_phase(phase);
    /** Create sequences that will be used in the test */
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
    foreach (tok_cons_seq[i]) begin
      tok_cons_seq[i] = token_agent_cons_sequence::type_id::create($sformatf("tok_cons_seq[%0d]", i), this);
    end
    foreach (tok_prod_seq[i]) begin
      tok_prod_seq[i] = token_agent_prod_sequence::type_id::create($sformatf("tok_prod_seq[%0d]", i), this);
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);

      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication starting"), UVM_HIGH)
      #100ns;
      ral_write_data = 64'h000_0001;
      configure_prg_reg();
      configure_exe_reg();
      begin
         prepare_prg_packet_and_send_ifdw();
      end
      fork : fork_common_prg
        tok_prod_start(mvm_prg_cmd_tb_data_h.header.token_prod, VERIF_MVM_PRG_TOK_AGT);
        tok_cons_start(mvm_prg_cmd_tb_data_h.header.token_cons, VERIF_MVM_PRG_TOK_AGT);
        begin
          wait_for_prg_status();
          disable fork_common_prg;
        end
        begin : watchdog_thd
          #200us;
          `uvm_error("check_prg_done", $sformatf("Watchdog of 200us was reached and the DUT Program module didn't change its state to IDLE"))
          disable fork_common_prg;
        end
      join

      repeat(1) begin
        prepare_exe_instr();
        prepare_exe_packet_and_send_ifd0();
        
        `uvm_info(get_type_name(), $sformatf("size of mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data : %0d",mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.size), UVM_HIGH);
        `uvm_info(get_type_name(), $sformatf("size of mvm_exe_cmd_tb_data_packet_h.header : %0d",mvm_exe_cmd_tb_data_packet_h.header.size), UVM_HIGH);
        fork : fork_common_exe
          foreach (mvm_exe_cmd_tb_data_packet_h.header[i]) begin
            tok_prod_start(mvm_exe_cmd_tb_data_packet_h.header[i].token_prod, VERIF_MVM_EXE_TOK_AGT);
          end
          foreach (mvm_exe_cmd_tb_data_packet_h.header[i]) begin
            tok_cons_start(mvm_exe_cmd_tb_data_packet_h.header[i].token_cons, VERIF_MVM_EXE_TOK_AGT);
          end
          begin
            wait_for_exe_status();
            disable fork_common_exe;
          end
          begin : watchdog_thd
            #200us;
            `uvm_error("check_exec_done", $sformatf("Watchdog of 200us was reached and the DUT Execution module didn't change its state to IDLE"))
            disable fork_common_exe;
          end
        join
        //drain time to wait for the token monitor to see the request and answer of token producer for the last command
        #2us;
      end
      
      check_irq_status();

      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication end"), UVM_HIGH)
    phase.drop_objection(this);
  endtask
  
  task tok_prod_start(bit [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] a_tok_en, mvm_tok_agt_type_t a_tok_agt_type);
    foreach (a_tok_en[i]) begin
      if(a_tok_en[i]) begin
        `uvm_info("TOK_DBG", $sformatf("Starting producer token sequence for index %0d", i), UVM_HIGH)
        tok_prod_seq[i].start(env.tok_agt[a_tok_agt_type][i].m_tok_seqr);
      end
    end
  endtask : tok_prod_start
  
  task tok_cons_start(bit [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] a_tok_en, mvm_tok_agt_type_t a_tok_agt_type);
    foreach (a_tok_en[i]) begin
      if(a_tok_en[i]) begin
        `uvm_info("TOK_DBG", $sformatf("Starting consumer token sequence for index %0d", i), UVM_HIGH)
        tok_cons_seq[i].start(env.tok_agt[a_tok_agt_type][i].m_tok_seqr);
      end
    end
  endtask : tok_cons_start

endclass:ai_core_mvm_random_matrix_multiplication_token_test

`endif	// __AI_CORE_MVM_RANDOM_MATRIX_MULTIPLICATION_TOKEN_TEST__
