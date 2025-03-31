/** Token sequence that make sure that delay of token interface is huge enough
* to create the scenario of having tvalid = 1 and tready = 0 on dwpu command fifo.
* Note that the huge delay is only for the token producer, for the token consumer is the normal range.
*/
class token_agent_prod_huge_delay_seq_item extends token_agent_seq_item;

  constraint c_huge_delay {
    if(m_type_enm != TOK_CONS_DRV) {
      m_bv_delay inside {[100:1000]};
    }
    else {
      m_bv_delay inside {[0:10]};
    }
  }
  constraint c_huge_delay_dist {
    //only apply the delays to producer line
    if(m_type_enm != TOK_CONS_DRV) {
      m_bv_delay dist {
        [100:700] :/ 10,
        [700:1000] :/ 90
      };
    }
  }

  `uvm_object_utils(token_agent_prod_huge_delay_seq_item)

  function new(string name = "token_agent_prod_huge_delay_seq_item");
    super.new(name);
    `uvm_info ("run_phase", $sformatf("New from token_agent_prod_huge_delay_seq_item"), UVM_HIGH)

  endfunction

endclass : token_agent_prod_huge_delay_seq_item

/**
* This testcase is similar to ai_core_dwpu_cmd_fifo_overflow_test excepth the fact that programs only has init
*  section to make sure the programs are smaller
*/
class ai_core_dwpu_small_cmds_fifo_overflow_test extends ai_core_dwpu_cmd_fifo_overflow_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_small_cmds_fifo_overflow_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual function void set_type_override_callback();
    `uvm_info ("run_phase", $sformatf("Overriding token_agent_seq_item with token_agent_prod_huge_delay_seq_item"), UVM_HIGH)
    /** Factory override of the master transaction object */
    set_type_override_by_type (token_agent_seq_item::get_type(), token_agent_prod_huge_delay_seq_item::get_type());
  endfunction : set_type_override_callback

  virtual function void build_phase(uvm_phase phase);

    super.build_phase(phase);
  endfunction : build_phase


  virtual function void randomize_cmd_seq(ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb  cmd_info_seq[], ai_core_dwpu_cmd_sequence cmd_seq[], int iter);
    `uvm_info ("run_phase", $sformatf("Overriding randomize_cmd_seq to only use init portion"), UVM_HIGH)
    /** randomize the commands
     * It was necessary to constraint the start and the length of the programs to make sure that all the programs could be loaded for
     * memory at the same time without overrides between them.
     */
    foreach (cmd_seq[i]) begin
      //randomize the commands (one more than the maximum number of FIFO depth)
      if(!cmd_seq[i].randomize() with {
        enable_tokens == 1;
        
        //constraint the format to be only inside M1N0 to make the programs even smaller
        header.format == aic_dp_cmd_gen_pkg::LoopsM1N0;
        
        //make sure that tokens is active for all commands and the full of token fifos is achieved (only on half of the iterations)
        if(iter%2) {
          header.token_cons == 1;
          header.token_prod == 3;
        }
      }) `uvm_error(get_name, $sformatf("cmd_seq[%0d] randomization error!", i));
    end
        
    foreach (cmd_info_seq[i]) begin
      //set the base and top addresses for cmd_info_seq randomization
      cmd_info_seq[i].base=0;
      cmd_info_seq[i].top=INSTR_MEM_DEPTH-1;
      if(!cmd_info_seq[i].randomize() with {
        //set the command to be valid
        valid == 1;
        format == cmd_seq[i].header.format;
        
        main_0.length inside {[0:2]};

        //make sure that the start of the current program is located after the previous program with a maximum of 10 address positions of difference.
        //this is necessary to help the randomization to complete successfully and do not overwrite programs
        if (i!=0) {
          main_0.start inside {[(cmd_info_seq[i-1].main_0.start+cmd_info_seq[i-1].main_0.length) : (cmd_info_seq[i-1].main_0.start+cmd_info_seq[i-1].main_0.length + 10)]};
        }
        else {
          main_0.start inside {[0:20]};
        }
      }) `uvm_error(get_name, $sformatf("cmd_info_seq[%0d] randomization error!", i));
      //set the pointer to command info
      cmd_seq[i].cmd_info = cmd_info_seq[i];
    end
  endfunction : randomize_cmd_seq

  virtual task run_phase(uvm_phase phase);
    `uvm_info ("run_phase", "Entered...", UVM_LOW)
    super.run_phase(phase);
  endtask
endclass : ai_core_dwpu_small_cmds_fifo_overflow_test
