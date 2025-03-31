// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_register read test
// Read reset value from all registers
// Check reset value read with APB and JTAG
//==============================================================================
// Register reset testing
task register_reset_test();
  int         i      ;
  int         ptr    ;
  tms_pdata_t prdata ;
  tms_pdata_t chkdata;

  `uvm_info("RESET_TEST", "RESET_TEST", UVM_NONE)
  //============================================================================
  // APB reset check
  for (int k=0; k<2; k++) begin
    i   = 0;
    ptr = 0;
    // read all registers.
    while (i<=LAST_REG_ADDR) begin
      apb_read (i, prdata);

      chkdata = get_reg_reset_value(i);
      `uvm_info("APB_RESET_CHECK", $sformatf("APB Reset Read Reg: %0s Addr: %0x Data: %0x Exp: %0x", get_reg_name(i), i, prdata, chkdata), UVM_HIGH)
      check_reg_read_data("APB", get_reg_name(i), i, prdata, chkdata);
      i+=4;
      ptr++;
    end

    ////============================================================================
    // JTAG reset check
    // start jtag clock
    repeat(10) @ (posedge tb_clk);
    reset_jtag(5ns);
    drive_tck();

      //i=0;
    i   = 0;
    ptr = 0;
    // read all registers.
    while (i<=LAST_REG_ADDR) begin
      jtag_read_data(i, prdata);

      chkdata = get_reg_reset_value(i);
      `uvm_info("JTAG_RESET_CHECK", $sformatf("JTAG Reset Read Reg: %0s Addr: %0x, Data: %0x Exp: %0x", get_reg_name(i), i, prdata, chkdata), UVM_HIGH)
      check_reg_read_data("JTAG", get_reg_name(i), i, prdata, chkdata);
      i+=4;
      ptr++;
    end
  end

endtask


