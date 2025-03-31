// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Testbench watchdog tasks
//

//==============================================================================
// WTD Registers
//    Reg Name        | Addr | Acc |
// -------------------+------+-----+--------------------------------
// WDT_CR             | 'h00 | RW  | Control Register
// WDT_TORR           | 'h04 | ??  | Timeout Range Register
// WDT_CCVR           | 'h08 | RO  | Current Counter Value Register
// WDT_CRR            | 'h0c | RW  | Counter Restart Register
// WDT_STAT           | 'h10 | RO  | Interrupt Status Register
// WDT_EOI            | 'h14 | RO  | Interrupt Clear Register
// WDT_PROT_LEVEL     | 'h1c | ??  | WDT Protection level
// WDT_SFTY_INTR_STAT | 'h20 | RO  | Safety Interrupt Status Register
// WDT_SFTY_INTR_CLR  | 'h24 | RW  | Safety Interrupt Clear Register
// WDT_COMP_PARAM_5   | 'he4 | RO  | Component Parameters Register 5
// WDT_COMP_PARAM_4   | 'he8 | RO  | Component Parameters Register 4
// WDT_COMP_PARAM_3   | 'hec | RO  | Component Parameters Register 3
// WDT_COMP_PARAM_2   | 'hf0 | RO  | Component Parameters Register 2
// WDT_COMP_PARAM_1   | 'hf4 | RO  | Component Parameters Register 1
// WDT_COMP_VERSION   | 'hf8 | RO  | Component Version Register
// WDT_COMP_TYPE      | 'hfc | RO  | Component Type Register

//==============================================================================
task do_wtd_check(int unsigned num_rst = 2);
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;
  bit                          done     ;
  bit                          no_check ;

  for (int i=0; i<num_rst; i++) begin
    // clear the wdt reset mask bit
    set_global_rst_mask(3'h3);

    #10us;

    // enable wtd
    // set the timeout period
    set_wdt_timeout(0); // set shortest timeout

    // restart the count to load new value
    set_wdt_restart();

    // write to cr register t set enable
    set_wdt_enable();

    // wait for global reset
    @(negedge o_global_rst_n);
    `uvm_info("DO_WTD_CHECK", $sformatf("Got Global Reset loop: %0d", i), UVM_NONE)
    @(posedge o_global_rst_n);
    #10us;
  end
  
endtask

//==============================================================================
task set_wdt_timeout(bit [3:0] load = 0);
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr     = WTD_BASE_ADDR + 'h04; // WDT_TORR
  reg_data      = 0                   ;
  reg_data[7:4] = load                ; // set shortest timeout
  reg_data      = shift_axi_write_data(test_addr, reg_data);
  axi_reg_write                       (test_addr, reg_data, reg_resp);
  check_axi_resp                      (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

endtask

//==============================================================================
task set_wdt_restart();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr     = WTD_BASE_ADDR + 'h0C; // WDT_CRR
  reg_data      = 0                   ;
  reg_data[7:0] = 'h76                ; // write the restart code
  reg_data      = shift_axi_write_data(test_addr, reg_data);
  axi_reg_write                       (test_addr, reg_data, reg_resp);
  check_axi_resp                      (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

endtask

//==============================================================================
// wdt enable
task set_wdt_enable();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  // write to cr register t set enable
  test_addr     = WTD_BASE_ADDR;
  reg_data      = 0            ;
  reg_data[0]   = 1            ; //set enable
  reg_data[1]   = 0            ; // rmod set to resert (defauilt). 1 =interrupt.
  reg_data      = shift_axi_write_data(test_addr, reg_data);
  axi_reg_write                       (test_addr, reg_data, reg_resp);
  check_axi_resp                      (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

endtask

//==============================================================================
task do_wtd_reg_check();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  bit                          done     ;
  bit                          no_check ;

  // set address and expected data for first read
  test_addr = WTD_BASE_ADDR;
  exp_data  = 'hffffffff00000000;
  no_check  = 0;

  done = 0;
  do begin
    axi_reg_read  (test_addr, reg_read_data, reg_resp);

    if (no_check) begin
    end else begin
      check_reg_read(test_addr, reg_read_data            , exp_data);
    end
    check_axi_resp(test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

    no_check = 0;
    test_addr += 4;
    case(test_addr)
     WTD_BASE_ADDR + 'h04 : begin
       exp_data  = 'h0000000F_FFFFFFFF;
     end
     WTD_BASE_ADDR + 'h08 : begin
       exp_data  = 'hFFFFFFFF_7fffffff;
     end
     WTD_BASE_ADDR + 'h0C : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     WTD_BASE_ADDR + 'h10 : begin
       exp_data  = 'hFFFFFFFF_00000000;
     end
     WTD_BASE_ADDR + 'h14 : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     WTD_BASE_ADDR + 'h18 : begin
       exp_data  = 'hFFFFFFFF_3131332a;
     end
     WTD_BASE_ADDR + 'h1C : begin
       exp_data  = 'h00000000_ffffffff;
     end
     WTD_BASE_ADDR + 'h20 : begin
       exp_data  = 'hffffffff_00000000;
     end
     WTD_BASE_ADDR + 'h24 : begin
       exp_data  = 'h00000000_FFFFFFFF;
       test_addr = WTD_BASE_ADDR + 'hE4;
     end
     WTD_BASE_ADDR + 'hE4 : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     WTD_BASE_ADDR + 'hE8 : begin
       exp_data  = 'hFFFFFFFFF_00000000;
     end
     WTD_BASE_ADDR + 'hEC : begin
       exp_data  = 'h0000000F_FFFFFFFF;
     end
     WTD_BASE_ADDR + 'hF0 : begin
       exp_data  = 'hFFFFFFFF_7FFFFFFF;
     end
     WTD_BASE_ADDR + 'hF4 : begin
       exp_data  = 'h100f0240_ffffffff;
     end
     WTD_BASE_ADDR + 'hF8 : begin
       exp_data  = 'hffffffff_3131332a;
     end
     WTD_BASE_ADDR + 'hFC : begin
       exp_data  = 'hDEADDEAD_DEADDEAD;
       // last address
       done = 1;
     end
    endcase

  end while (!done);

endtask
