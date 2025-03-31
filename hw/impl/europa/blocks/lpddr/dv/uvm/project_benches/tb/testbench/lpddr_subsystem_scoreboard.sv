//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_scoreboard.sv
// Unit        : lpddr_subsystem_scoreboard
//------------------------------------------------------------------------------
// Description : This is 
//------------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Macro Name  : pass_msg
// Arguments   : CHECK_NAME -> Name of check
//               MSG -> String argument to print message
// Description : Macro to display passing checks/messages.
//-----------------------------------------------------------------------------
`define pass_msg(CHECK_NAME,MSG)\
  `uvm_info(CHECK_NAME,MSG,UVM_LOW)\

//-----------------------------------------------------------------------------
// Macro Name  : fail_msg
//               CHECK_NAME -> Name of Check
// Arguments   : MSG -> String Argument to print message.
// Description : Macro to display failing checks/messages.
//-----------------------------------------------------------------------------
`define fail_msg(CHECK_NAME,MSG)\
  `uvm_error(CHECK_NAME,MSG)\

 //-----------------------------------------------------------------------------
// Macro Name  : pass_fail_msg
// Arguments   : CHECK_NAME -> Name of check
//               EXPR -> Expression to be evaluated
//               MSG -> String argument to print message
// Description : Macro to display passing/failing checks/messages.
//-----------------------------------------------------------------------------
`define pass_fail_msg(CHECK_NAME,EXPR,MSG)\
  if(EXPR)begin\
    `uvm_info(CHECK_NAME,MSG,UVM_LOW)\
  end\
  else begin\
    `uvm_error(CHECK_NAME,MSG)\
  end

//TODO : Need to move above macro to some base file
  
`ifndef LPDDR_SUBSYSTEM_SCOREBOARD_SV
`define LPDDR_SUBSYSTEM_SCOREBOARD_SV

`uvm_analysis_imp_decl(_from_lpddr_predictor)       //Received from LPDDR Predictor
`uvm_analysis_imp_decl(_from_lpddr_monitor)         //Received from LPDDR Monitor
`uvm_analysis_imp_decl(_from_lpddr_monitor_nonrw)   //Received from LPDDR Monitor

//---------------------------------------------------------------------------
// Class          : lpddr_subsystem_scoreboard
// Parent         : uvm_scoreboard
//---------------------------------------------------------------------------
class lpddr_subsystem_scoreboard extends uvm_scoreboard;
  
  //typedef for lpddr_subsystem_scoreboard
  typedef lpddr_subsystem_scoreboard this_type;
  
  //To receive LPDDR expected and actual transactions
  uvm_analysis_imp_from_lpddr_predictor       #(amem_command_class, this_type) lpddr_exp_export;
  uvm_analysis_imp_from_lpddr_monitor         #(amem_command_class, this_type) lpddr_act_rw_export;
  uvm_analysis_imp_from_lpddr_monitor_nonrw   #(amem_command_class, this_type) lpddr_act_nonrw_export;

  amem_command_class lpddr_exp_trans;
  amem_command_class lpddr_act_trans;
  amem_command_class lpddr_act_trans_nonrw;

  //Queue to store transaction for In-order Comparison
  amem_command_class lpddr_exp_trans_q [$];

  //Associative array to store transaction for Out-of-order Comparison
  amem_command_class lpddr_non_rw_exp_trans [int];
  amem_command_class lpddr_non_rw_act_trans [int];

  //TODO: assign below signal through System reset and remove below line
  bit reset_assertion;

  // Event Declarations
  event received_lpddr_exp_trans;
  event received_lpddr_rw_trans;
  event received_lpddr_nonrw_trans;

  // ------------------------------------------------------------------------
  // Register fault management component with the factory.
  // ------------------------------------------------------------------------
  `uvm_component_utils (this_type)
  
  //-------------------------------------------------------------------------
  // Function       : new
  // Arguments      : string name - Name of the object.
  //                  uvm_component parent
  // Description    : Constructor for fpga base scoreboard class objects.
  //-------------------------------------------------------------------------
  function new(string name = "lpddr_subsystem_scoreboard", uvm_component parent);
    super.new(name,parent);
    lpddr_exp_export = new("lpddr_exp_export", this);
    lpddr_act_rw_export = new("lpddr_act_rw_export", this);
    lpddr_act_nonrw_export = new("lpddr_act_nonrw_export", this);
  endfunction : new
  
  //--------------------------------------------------------------------------
  // Function       : build_phase
  // Arguments      : uvm_phase phase - Handle of uvm_phase.
  // Description    : This phase create all the required objects.
  //--------------------------------------------------------------------------
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("SCOREBOARD", $sformatf("Build-phase executed in scoreboard"),UVM_LOW)
  endfunction : build_phase
  
  //--------------------------------------------------------------------------
  // Function       : connect_phase
  // Arguments      : uvm_phase phase - Handle of uvm_phase.
  // Description    : This phase create all the required objects.
  //--------------------------------------------------------------------------
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("SCOREBOARD", $sformatf("Connect-phase executed in scoreboard"),UVM_LOW)
  endfunction : connect_phase

  //-------------------------------------------------------------------------
  // Task           : run_phase
  // Arguments      : uvm_phase phase  - Handle of uvm_phase.
  // Description    : In this phase the TB execution starts
  //-------------------------------------------------------------------------
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info("SCOREBOARD", $sformatf("Run-phase executed in scoreboard"),UVM_LOW)
    forever begin
      fork begin
        fork
          default_value_on_reset();
          lpddr_in_or_out_of_order_comparison();
        join_any
        disable fork;
      end join
    end
  endtask : run_phase

  //---------------------------------------------------------------------------
  // Task Name   : default_value_on_reset
  // Arguments   : NA
  // Description : This task will flush all the entries from arrays when 
  //               Device Reset is asserted.
  //---------------------------------------------------------------------------
  task default_value_on_reset();
    // TODO : need to provide relevant reset signal
    forever@(reset_assertion) begin 
      lpddr_exp_trans_q.delete();
      lpddr_non_rw_exp_trans.delete();
      lpddr_non_rw_act_trans.delete();
    end//
  endtask : default_value_on_reset

  //---------------------------------------------------------------------------
  // Task        : lpddr_in_or_out_of_order_comparison
  // Arguments   : NA
  // Description : This task will compare coming out-of-order commands other
  //               than read and write.
  //---------------------------------------------------------------------------
  task lpddr_in_or_out_of_order_comparison();
    bit [31:0] addr;
    forever@(received_lpddr_rw_trans) begin
    //forever@(received_lpddr_nonrw_trans, received_lpddr_rw_trans) begin
      addr = lpddr_act_trans.col_addr;
      //In-order Comparision
      if((lpddr_act_trans.mem_cmd == AMEM_READ) || (lpddr_act_trans.mem_cmd == AMEM_WRITE)) begin
        lpddr_trans_compare(lpddr_act_trans,lpddr_exp_trans_q);
      end
      //Out-of-order Comparision
      else begin
        // check if corresponding expected transaction is already received and
        // then compare it.
        if(lpddr_non_rw_exp_trans.exists(addr)) begin
          // Iterate through each entry of lpddr_non_rw_exp_trans to match addr
          foreach(lpddr_non_rw_exp_trans[exp_addr]) begin 
            if(lpddr_non_rw_exp_trans[exp_addr].col_addr == addr) begin 
              //lpddr_trans_compare(lpddr_act_trans, lpddr_non_rw_exp_trans[addr]);
              lpddr_non_rw_exp_trans.delete(addr); // delete once transaction is compared.
            end // end if
          end // end foreach
        end // end if exist
        // If corresponding expected transaction is not exist then store it in
        // array.
        else begin 
          // In case on Read Command push transaction based on address
          assert($cast(lpddr_non_rw_act_trans[addr],lpddr_act_trans.clone()));
        end
      end
    end
    //TODO: understand below line and do BACKDOOR WRITE to update APB Scoreboard memory
    //m_config.scoreboard_mem.backdoor_write(temp_address, t.wdata_words[0] [(8*(lane))+7 -: 8]);
  endtask : lpddr_in_or_out_of_order_comparison

  //---------------------------------------------------------------------------
  // Function    : lpddr_trans_compare
  // Arguments   : NA
  // Description : This task will compare received lpddr transaction.
  //---------------------------------------------------------------------------
  virtual function void lpddr_trans_compare(amem_command_class ddr_act_trans, lpddr_exp_trans_q[$]);
    if(lpddr_exp_trans_q.size()>0) begin
      amem_command_class ddr_exp_trans = lpddr_exp_trans_q.pop_front();
		  if(ddr_act_trans.compare(ddr_exp_trans)) begin
        `pass_msg("LPDDR_DATA_CHECK","Act and Exp Data Are Matching")
        ddr_act_trans.sprintf();
        ddr_exp_trans.sprintf();
      end
      else begin 
        `fail_msg("LPDDR_DATA_CHECK","Act and Exp Data Are Not Matching")
        ddr_act_trans.sprintf();
        ddr_exp_trans.sprintf();
      end
    end
  endfunction : lpddr_trans_compare

  //---------------------------------------------------------------------------
  // Function    : lpddr_trans_compare
  // Arguments   : i, exp_data, act_data
  // Description : This task will compare actual and expected data.
  //---------------------------------------------------------------------------
  /*virtual function void compare_subsystem_outputs(int i, ref bit[i:0] exp_data, ref bit[i:0] act_data);
    `pass_fail_msg(($psprintf()),
                   (act_data == exp_data),
                   ());
  endfunction : compare_subsystem_outputs

  /*Checks to be implemented for below signals:
    * hpr_credit_cnt[6:0]
    * lpr_credit_cnt[6:0]
    * wr_credit_cnt[6:0]
    * wrecc_credit_cnt[6:0]
    * cactive_ddrc
    * csysack_ddrc
    * stat_ddrc_reg_selfref_type[1:0]
    * sbr_done_intr
    * dgb_dfi_ie_cmd_type[2:0]
    * derate_temp_limit_intr
    * derate_temp_limit_intr_fault[1:0]
    * ecc_ap_err_intr
    * ecc_ap_err_intr_fault[1:0]
    * ecc_corrected_err_intr
    * ecc_corrected_err_intr_fault[1:0]
    * ecc_uncorrected_err_intr
    * ecc_uncorrected_err_intr_fault[1:0]
    * rd_linkecc_corr_err_intr
    * rd_linkecc_corr_err_intr_fault[1:0]
    * rd_linkecc_uncorr_err_intr
    * rd_linkecc_uncorr_err_intr_fault[1:0]
    * dfi_reset_n_ref
    * init_mr_done_out
    * hif_mrr_data[31:0]
    * hif_mrr_data_valid
    * hif_refresh_req_bank
    * perf_* siganls*/
  
  //-------------------------------------------------------------------------
  // Function       : write_from_lpddr_predictor
  // Arguments      : amem_command_class t
  // Description    : This method receives transaction from LPDDR predictor.
  //-------------------------------------------------------------------------
  virtual function void write_from_lpddr_predictor(amem_command_class t);
    `uvm_info("write_from_lpddr_predictor1", $sformatf("Expected LPDDR transaction received from LPDDR predictor in scoreboard = \n%s", t.sprintf()),UVM_LOW)

    //Creating seperate copy of transaction
    assert($cast(lpddr_exp_trans,t.clone()));
    -> received_lpddr_exp_trans;
    lpddr_exp_trans_q.push_back(lpddr_exp_trans);
    `uvm_info("write_from_lpddr_predictor2", $sformatf("LPDDR input transaction = \n%s", lpddr_exp_trans.sprintf()),UVM_LOW)
  endfunction: write_from_lpddr_predictor

  //-------------------------------------------------------------------------
  // Function       : write_from_lpddr_monitor
  // Arguments      : amem_command_class t
  // Description    : This method receives transaction from LPDDR Monitor.
  //-------------------------------------------------------------------------
  virtual function void write_from_lpddr_monitor(amem_command_class t);
    `uvm_info("write_from_lpddr_monitor1", $sformatf("Actual LPDDR transaction received from LPDDR predictor in scoreboard = \n%s", t.sprintf()),UVM_LOW)

    //Creating seperate copy of transaction
    assert($cast(lpddr_act_trans,t.clone()));
    -> received_lpddr_rw_trans;
    `uvm_info("write_from_lpddr_monitor2", $sformatf("LPDDR Actual transaction = \n%s", lpddr_act_trans.sprintf()),UVM_LOW)
  endfunction: write_from_lpddr_monitor
  
  //-------------------------------------------------------------------------
  // Function       : write_from_lpddr_monitor_nonrw
  // Arguments      : amem_command_class t
  // Description    : This method receives transaction from LPDDR Monitor.
  //-------------------------------------------------------------------------
  virtual function void write_from_lpddr_monitor_nonrw(amem_command_class t);
    `uvm_info("write_from_lpddr_monitor_nonrw1", $sformatf("Actual LPDDR transaction received from LPDDR predictor in scoreboard = \n%s", t.sprintf()),UVM_LOW)

    //Creating seperate copy of transaction
    assert($cast(lpddr_act_trans_nonrw,t.clone()));
    -> received_lpddr_nonrw_trans;
    `uvm_info("write_from_lpddr_monitor_nonrw2", $sformatf("LPDDR Actual transaction = \n%s", lpddr_act_trans_nonrw.sprintf()),UVM_LOW)
  endfunction: write_from_lpddr_monitor_nonrw

  //---------------------------------------------------------------------------
  // Function Name : report_phase
  // Arguments     : uvm_phase phase  - Handle of uvm_phase.
  // Arguments     : uvm_phase phase
  //---------------------------------------------------------------------------
  virtual function void report_phase(uvm_phase phase);
    lpddr_left_over_transaction();
  endfunction: report_phase

  //---------------------------------------------------------------------------
  // Function Name : lpddr_left_over_transaction
  // Arguments     : NA
  // Description   : This method checks that there are no left over transaction
  //                 exist in actual and expected fifo at the end of simulation
  //                 time
  //---------------------------------------------------------------------------
  virtual function void lpddr_left_over_transaction();
    // Expected FIFO Left Over Transaction Check
    if(lpddr_exp_trans_q.size() > 0) begin 
      // `fail_msg("Check Name","Message")
      // FAIL : There exist left over transaction in actual fifo which is not
      // compared against expected data
    end 
    else begin 
      // `pass_msg("Check Name","Message")
      // PASS : There is no left over transaction exist in actual fifo
    end
  endfunction : lpddr_left_over_transaction
  
endclass : lpddr_subsystem_scoreboard
`endif // LPDDR_SUBSYSTEM_SCOREBOARD_SV
