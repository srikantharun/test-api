// AI Core MVM Bist_error_test-case class
class ai_core_mvm_bist_error_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_bist_error_test)
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_addr[$];
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;
      bit busy,pass,done;
      bit [3:0] error_bank;
      bit [4:0] error_col;
      bit [15:0] error_cycle;
      byte unsigned imc_err_bank,imc_err_bank_wrapper;
      int temp,err_inj_bank,imc_err_col_decimal,exp_err_col;
      string imc_bank_str, imc_err_bank_str,imc_err_col_str, imc_str,imc_str_2,exp_str,imc_err_col ;
      bit exp;
      rand int unsigned imc_force_value;
      imc_bist_pkg::reg2hw_imc_bist_status_reg_t reg_imc_bist_status;


      axi_master_write_sequence axi_wr_seq;
  // Class constructor
  function new (string name="ai_core_mvm_bist_error_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info (get_name, "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
      `uvm_info(get_name,$sformatf("MVM Bist test starting"), UVM_HIGH)

      void'(randomize());

      imc_force();
      
      //make sure the reset is done before starting BIST test
      repeat(15) @(posedge mvm_if.mvm_int_clk);

      if($test$plusargs("CBIST"))
        start_imc_cbist();
      else
        start_imc_mbist();
        
      fork : busy_chk
        begin
          repeat(160000) @(posedge mvm_if.mvm_int_clk);
          `uvm_fatal(get_name, "Timeout - Done not observed within 160000 clock cycles");
        end

        begin
          do begin
            reg_imc_bist_status = mvm_if.aic_csr_reg2hw.imc_bist_status;
            if(!reg_imc_bist_status.done.q) repeat(1000) @(posedge mvm_if.mvm_int_clk);
          end while(!reg_imc_bist_status.done.q);
          `uvm_info (get_name, "Done status is observed", UVM_HIGH)
        end
 
      join_any
      disable busy_chk;
  
      bist_error_check();

    phase.drop_objection(this);
  endtask

  task start_imc_mbist;
    mvm_if.aic_csr_reg2hw.imc_bist_cfg = '{
      csr_sel: 1'b1,
      default: '0
    };
    repeat(5) @(posedge mvm_if.mvm_int_clk);
    mvm_if.aic_csr_reg2hw.imc_bist_cmd = '{
      mbist_start: 1'b1,
      default: '0
    };
  endtask

  task start_imc_cbist;
    mvm_if.aic_csr_reg2hw.imc_bist_cfg = '{
      csr_sel: 1'b1,
      default: '0
    };
    repeat(5) @(posedge mvm_if.mvm_int_clk);
    mvm_if.aic_csr_reg2hw.imc_bist_cmd = '{
      cbist_start: 1'b1,
      default: '0
    };
  endtask

  task imc_force;
    imc_err_bank         = $urandom_range(0,7)+48; // to change into ascii value
    imc_err_col          = $sformatf("%0d", $urandom_range(0,31)); 
    imc_err_bank_wrapper = $urandom_range(0,1)+48; // to change into ascii value

    temp=$urandom_range(97,98); //To restrict between 'a-b'
    imc_bank_str={imc_bank_str, string'(temp)};
    imc_str = {"hdl_top.dut.i_mvm_dp.inst_mvm_imc_acc.g_imc_acc_pairs[", imc_err_bank, "].inst_mvm_imc_acc_pair.inst_imc_bank_acc_", imc_bank_str, ".inst_imc_w_acc.u_mvm_imc_bank_combiner.g_imc_bank_wrapper[", imc_err_bank_wrapper, "].u_mvm_imc_bank_wrapper.u_imc_bank.compute_out_", imc_err_col};
      
    if (!uvm_hdl_force(imc_str,imc_force_value)) begin
      `uvm_fatal(get_name(), "hdl force got failed for imc bank")
    end
    
    `uvm_info(get_name,$sformatf("forcing on %s and forcing value is %d",imc_str,imc_force_value), UVM_LOW) 

  endtask

  task bist_error_check;
    
    busy = reg_imc_bist_status.busy.q;
    done = reg_imc_bist_status.done.q;
    pass = reg_imc_bist_status.pass.q;
    error_bank = reg_imc_bist_status.error_bank.q;
    error_col = reg_imc_bist_status.error_col.q;
    error_cycle = reg_imc_bist_status.error_cycle.q;


    if(busy==0 && done==1 && pass==0 && error_cycle!=0) begin
      `uvm_info(get_name,$sformatf("busy/done status is correctly obeseved and error_bank = %0d error_col = %0b error_cycle = %0b",error_bank, error_col, error_cycle), UVM_HIGH) 
    end
    else begin `uvm_error(get_name, $sformatf("Test failed - busy/done status is not correctly obeseved and busy = %0d, done = %0d, error_cycle = %0b",busy, done, error_cycle )) 
    end

    if(mvm_if.imc_bist_busy!=0 || mvm_if.imc_bist_done!=1 || mvm_if.imc_bist_pass!=0)
        `uvm_error(get_name, $sformatf("Test failed - observation pins are incoherent with internal status register (%0b,%0b,%0b)",
          mvm_if.imc_bist_busy,mvm_if.imc_bist_done,mvm_if.imc_bist_pass));


    
    if($test$plusargs("MBIST")) begin
      case (imc_err_bank-48)  //previously ASCII value was used -> using decimal value for comparison
        'd0: err_inj_bank = (imc_bank_str=="a") ? 0 : 2;
        'd1: err_inj_bank = (imc_bank_str=="a") ? 1 : 3;
        'd2: err_inj_bank = (imc_bank_str=="a") ? 4 : 6;
        'd3: err_inj_bank = (imc_bank_str=="a") ? 5 : 7;
        'd4: err_inj_bank = (imc_bank_str=="a") ? 8 : 10;
        'd5: err_inj_bank = (imc_bank_str=="a") ? 9 : 11;
        'd6: err_inj_bank = (imc_bank_str=="a") ? 12: 14;
        'd7: err_inj_bank = (imc_bank_str=="a") ? 13: 15;
        default : `uvm_fatal("BIST_ERROR_test", "wrong bank got selected.. Please check ")
      endcase
    end

    else if($test$plusargs("CBIST")) begin
      case (imc_err_bank-48)  //previously ASCII value was used -> using decimal value for comparison
        'd0: err_inj_bank = 2;
        'd1: err_inj_bank = 3;
        'd2: err_inj_bank = 6;
        'd3: err_inj_bank = 7;
        'd4: err_inj_bank = 10;
        'd5: err_inj_bank = 11;
        'd6: err_inj_bank = 14;
        'd7: err_inj_bank = 15;
        default : `uvm_fatal("BIST_ERROR_test", "wrong bank got selected.. Please check ")
      endcase
    end

    //converting char to decimal value
    $sscanf(imc_err_col, "%0d", imc_err_col_decimal);
    //previously ASCII value was used -> using decimal value for comparison
    //for europa computation formula has changed : #1608
    exp_err_col =  imc_err_col_decimal/2 +(imc_err_bank_wrapper-48)*16;
    if(err_inj_bank == error_bank && exp_err_col == error_col ) begin
      `uvm_info(get_name,$sformatf("injected error bank/column status is correctly obeseved "), UVM_HIGH) 
    end
    else begin `uvm_error(get_name, $sformatf("Test failed - injected error bank/column status is correctly obeseved. observed_error_bank is %0d  observed_error_column is %0d injected_error_bank is %0d injected_error_column is %0d", error_bank, error_col,err_inj_bank, exp_err_col )) 
    end

  endtask

endclass:ai_core_mvm_bist_error_test
