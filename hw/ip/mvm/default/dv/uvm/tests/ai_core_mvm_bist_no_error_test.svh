// AI Core MVM Bist_nor_error_test-case class
class ai_core_mvm_bist_no_error_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_bist_no_error_test)
      bit [AXI_LT_ADDR_WIDTH-1:0]    axi_addr[$];
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_write_data;
      bit [AXI_LT_DATA_WIDTH-1:0]    axi_read_data;
      bit busy,pass,done;
      bit [3:0] error_bank;
      bit [4:0] error_col;
      bit [15:0] error_cycle;
      imc_bist_pkg::reg2hw_imc_bist_status_reg_t reg_imc_bist_status;


      axi_master_write_sequence axi_wr_seq;
  // Class constructor
  function new (string name="ai_core_mvm_bist_no_error_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info (get_name, "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
      `uvm_info(get_name,$sformatf("MVM Bist test starting (%s)", $test$plusargs("CBIST") ? "CBIST" : "MBIST"), UVM_HIGH)

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

      busy = reg_imc_bist_status.busy.q;
      done = reg_imc_bist_status.done.q;
      pass = reg_imc_bist_status.pass.q;
      error_bank = reg_imc_bist_status.error_bank.q;
      error_col = reg_imc_bist_status.error_col.q;
      error_cycle = reg_imc_bist_status.error_cycle.q;

      if(busy==0 && done==1 && pass==1) begin
        `uvm_info(get_name,$sformatf("busy/done/pass status is correctly obeseved and status register value is %0b",ral_read_data), UVM_HIGH) 
      end
      else begin `uvm_error(get_name, $sformatf("Test failed - busy/done/pass status is not correctly obeseved and status register value is %0b",ral_read_data)) 
      end

      if(mvm_if.imc_bist_busy!=0 || mvm_if.imc_bist_done!=1 || mvm_if.imc_bist_pass!=1)
        `uvm_error(get_name, $sformatf("Test failed - observation pins are incoherent with internal status register (%0b,%0b,%0b)",
          mvm_if.imc_bist_busy,mvm_if.imc_bist_done,mvm_if.imc_bist_pass));

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

endclass:ai_core_mvm_bist_no_error_test
