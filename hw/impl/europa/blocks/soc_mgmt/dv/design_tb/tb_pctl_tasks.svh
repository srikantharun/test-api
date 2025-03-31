// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Tssks to check the syscfg APB interface.
//
//============================================================================
//==============================================================================
task do_pctl_reg_check();
  bit [31:0]                   test_addr;
  chip_apb_syscfg_data_t       data     ;
  chip_pkg::chip_axi_lt_data_t exp_data ;

  for (int i=0; i<'h90; i+=4) begin
    test_addr = PCTL_APB_BASE_ADDR + i;
    syso_syscfg_apb_read(test_addr, data, syscfg_slverr);
    case(test_addr)
      'h5320020 : begin exp_data = 'h4040404; end
      'h5320024 : begin exp_data = 'h4040404; end
      'h5320028 : begin exp_data = 'h4040404; end
      'h532002c : begin exp_data = 'h4040404; end
      'h5320030 : begin exp_data = 'h4040404; end
      'h5320034 : begin exp_data = 'h4040404; end
      'h5320038 : begin exp_data = 'h4040404; end
      'h532003c : begin exp_data = 'h4040404; end
      'h5320040 : begin exp_data = 'h7      ; end
      'h5320044 : begin exp_data = 'hf      ; end
      'h5320048 : begin exp_data = 'h3      ; end
      default   : begin exp_data = 0        ; end
    endcase
    `uvm_info("TEST_REG_CHECK", $sformatf("DEBUG300 Read Addr: %0x Data: %0x Exp: %0x %0s",test_addr, data, exp_data, data==exp_data ? "OK" : "KO"), UVM_NONE)

    check_reg_read(test_addr, data, exp_data);
  end

  for (int i=0; i<'h90; i+=4) begin
    test_addr = PCTL_APB_BASE_ADDR + i;
    syso_syscfg_apb_write(test_addr, ~(i), syscfg_slverr);
    syso_syscfg_apb_read(test_addr, data , syscfg_slverr);
    case(test_addr)
      'h5320000 : begin exp_data =  'h1        ; end
      'h5320004 : begin exp_data =  'h3        ; end
      'h5320008 : begin exp_data =  'h3        ; end
      'h532000c : begin exp_data =  'h3        ; end
      'h5320010 : begin exp_data =  'h3        ; end
      'h5320014 : begin exp_data =  'h3        ; end
      'h5320018 : begin exp_data =  'h3        ; end
      'h532001c : begin exp_data =  'h3        ; end
      'h5320020 : begin exp_data =  'hffffffdf ; end
      'h5320024 : begin exp_data =  'hffffffdb ; end
      'h5320028 : begin exp_data =  'hffffffd7 ; end
      'h532002c : begin exp_data =  'hffffffd3 ; end
      'h5320030 : begin exp_data =  'hffffffcf ; end
      'h5320034 : begin exp_data =  'hffffffcb ; end
      'h5320038 : begin exp_data =  'hffffffc7 ; end
      'h532003c : begin exp_data =  'hffffffc3 ; end
      'h5320040 : begin exp_data =  'h7        ; end
      'h5320044 : begin exp_data =  'hb        ; end
      'h5320048 : begin exp_data =  'h3        ; end
      'h532004c : begin exp_data =  'h0        ; end
      'h5320050 : begin exp_data =  'h0        ; end
      'h5320054 : begin exp_data =  'h0        ; end
      'h5320058 : begin exp_data =  'h1        ; end
      'h532005c : begin exp_data =  'h0        ; end
      'h5320060 : begin exp_data =  'h1        ; end
      'h5320064 : begin exp_data =  'hff01     ; end
      'h5320068 : begin exp_data =  'hff01     ; end
      'h532006c : begin exp_data =  'hff01     ; end
      'h5320070 : begin exp_data =  'hff01     ; end
      'h5320074 : begin exp_data =  'hff01     ; end
      'h5320078 : begin exp_data =  'hff01     ; end
      'h532007c : begin exp_data =  'hff01     ; end
      'h5320080 : begin exp_data =  'hff01     ; end
      'h5320084 : begin exp_data =  'h3        ; end
      'h5320088 : begin exp_data =  'h3        ; end
      'h532008c : begin exp_data =  'h3        ; end
      default   : begin exp_data = ~(i)        ; end
    endcase
    `uvm_info("TEST_REG_CHECK", $sformatf("DEBUG302 Read Addr: %0x Data: %0x Exp: %0x %0s",test_addr, data, exp_data, data==exp_data ? "OK" : "KO"), UVM_NONE)

    check_reg_read(test_addr, data, exp_data);
  end

endtask

//==============================================================================
// check unpoplated apb spaces
task do_syscfg_apb_no_pop();
  bit [31:0]                   test_addr;
  chip_apb_syscfg_data_t       data     ;
  chip_pkg::chip_axi_lt_data_t exp_data ;

  `uvm_info("NO POP TEST", $sformatf("START"), UVM_NONE)

  test_addr = SYSCFG_APB_NOPOP0_ADDR;
  exp_data  = 0;
  syso_syscfg_apb_read(test_addr, data, syscfg_slverr);
  check_reg_read(test_addr, data, exp_data);
  check_apb_err (test_addr, syscfg_slverr, 1);

  syso_syscfg_apb_write(test_addr, SYSCFG_APB_NOPOP0_ADDR, syscfg_slverr);
  check_apb_err (test_addr, syscfg_slverr, 1);

  syso_syscfg_apb_read(test_addr, data, syscfg_slverr);
  check_reg_read(test_addr, data, exp_data);
  check_apb_err (test_addr, syscfg_slverr, 1);


  test_addr = SYSCFG_APB_NOPOP1_ADDR;
  exp_data  = 0;
  syso_syscfg_apb_read(test_addr, data, syscfg_slverr);
  check_reg_read(test_addr, data, exp_data);
  check_apb_err (test_addr, syscfg_slverr, 1);

  syso_syscfg_apb_write(test_addr, SYSCFG_APB_NOPOP1_ADDR, syscfg_slverr);
  check_apb_err (test_addr, syscfg_slverr, 1);

  syso_syscfg_apb_read(test_addr, data, syscfg_slverr);
  check_reg_read(test_addr, data, exp_data);
  check_apb_err (test_addr, syscfg_slverr, 1);

endtask

//==============================================================================
function void check_apb_err(input [31:0] addr, bit act_err, exp_err);

  if (act_err != exp_err) begin
    `uvm_error("CHECK_APB_ERR", $sformatf("ERROR APB Slave Error Addr: %0x Act: %0x Exp: %0x", addr, act_err, exp_err))
    fail_cnt++;
  end

endfunction

//==============================================================================
task syso_syscfg_apb_write(input [31:0] addr, chip_apb_syscfg_data_t data, output bit slverr);
  bit done;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_psel     = 1    ;
  i_syscfg_apb4_s_penable  = 0    ;
  i_syscfg_apb4_s_paddr    = addr ;
  i_syscfg_apb4_s_pwdata   = data ;
  i_syscfg_apb4_s_pwrite   = 1    ;
  i_syscfg_apb4_s_pstrb    = '1   ;
  i_syscfg_apb4_s_pprot    = '0   ;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge i_ref_clk)
    if (o_syscfg_apb4_s_pready) begin
      slverr = o_syscfg_apb4_s_pslverr;
      done = 1;
    end
  end while (!done);
  i_syscfg_apb4_s_psel     = 0    ;
  i_syscfg_apb4_s_penable  = 0    ;

  @(posedge i_ref_clk);
  //regs_wdata[addr>>2] = data;

  `uvm_info("syso_syscfg_apb_write_COMPLETE", $sformatf("DEBUG340 ADDR: %0x Data: %0x,%0x", addr, data, addr>>2), UVM_HIGH)

endtask

//============================================================================
task syso_syscfg_apb_read(input [31:0] addr, output chip_apb_syscfg_data_t data, output bit slverr);
  bit done;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_psel     = 1    ;
  i_syscfg_apb4_s_penable  = 0    ;
  i_syscfg_apb4_s_paddr    = addr ;
  i_syscfg_apb4_s_pwdata   = '0   ;
  i_syscfg_apb4_s_pwrite   = 0    ;
  i_syscfg_apb4_s_pstrb    = '1   ;
  i_syscfg_apb4_s_pprot    = '0   ;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge i_ref_clk)
    data = o_syscfg_apb4_s_prdata;
    if (o_syscfg_apb4_s_pready) begin
      slverr = o_syscfg_apb4_s_pslverr;
      done = 1;
    end
  end while (!done);
  i_syscfg_apb4_s_psel     = 0    ;
  i_syscfg_apb4_s_penable  = 0    ;

  @(posedge i_ref_clk);

  `uvm_info("syso_syscfg_apb_read_COMPLETE", $sformatf("ADDR: %0x Data: %0x", addr, data), UVM_HIGH)

endtask

