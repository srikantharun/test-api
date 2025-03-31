// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Testbench watchdog tasks
//

//==============================================================================
// RTC registers
// Name             | ADDR |          |
// -----------------+------+----------+---------------------------------
// RTC_CCVR         | 0x00 | RO       | Current Counter Value Register
// RTC_CMR          | 0x04 | RW       | Counter Match Register
// RTC_CLR          | 0x08 | RW       | Counter Load Register
// RTC_CCR          | 0x0c | ??       | Counter Control Register
// RTC_STAT         | 0x10 | [1:0] RW | Interrupt Status Register
// RTC_RSTAT        | 0x14 | RO       | Interrupt Raw Status Register
// RTC_EOI          | 0x18 | RO       | End of Interrupt Register
// RTC_COMP_VERSION | 0x1c | RO       | Component Version Register
// RTC_CPSR         | 0x20 | RW       | Counter PreScaler Register
// RTC_CPCVR        | 0x24 | RO       | Current Prescaler Counter Value Register

//==============================================================================
// write ccr register
// [   0] : interrupt enable
// [   1] : interrupt mask
// [   3] : rtc wrap en
// [   4] : rtc prescaler en
// [7::5] : rt protection level
task rtc_write_ccr();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr   =  RTC_BASE_ADDR + 'h0c;
  reg_data    = 0;
  reg_data[0] = 1;
  reg_data[1] = 0;
  reg_data[4] = 1;

  reg_data = shift_axi_write_data  (test_addr, reg_data);
  axi_reg_write                    (test_addr, reg_data,       reg_resp);
  check_axi_resp                   (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);
endtask

//==============================================================================
// write rtc_cmr to set match value
task rtc_write_match_val(bit [31:0] val);
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr      =  RTC_BASE_ADDR + 'h04;
  reg_data       = 0  ; 
  reg_data[31:0] = val;

  reg_data = shift_axi_write_data  (test_addr, reg_data);
  axi_reg_write                    (test_addr, reg_data,       reg_resp);
  check_axi_resp                   (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);
endtask

//==============================================================================
// clear the interrupt
// read reg RTC_EOI to clear
task rtc_read_eoi();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr      =  RTC_BASE_ADDR + 'h18;

  axi_reg_read  (test_addr, reg_read_data,  reg_resp);
  check_axi_resp(test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

endtask

//==============================================================================
// rtc counter load
// write RTC_CLR
task rtc_counter_load(bit [31:0] val);
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr = RTC_BASE_ADDR + 'h08;

  reg_data  = val;

  reg_data = shift_axi_write_data  (test_addr, reg_data);
  axi_reg_write                    (test_addr, reg_data,       reg_resp);
  check_axi_resp                   (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);
endtask
//==============================================================================
// rtc interurpt check
task do_rtc_int_check();
  bit [31:0] match_val;
  int unsigned cnt;

  // set pll
  test_step = 2000;
  #10us;

  // keep rtc match value for interrupt as small
  match_val = 'h1000;
  rtc_write_match_val(match_val);
  test_step = 2002;

  // set interrupt enable
  rtc_write_ccr();
  test_step = 2100;

  cnt=0;
  repeat(2) begin
    `uvm_info("DO_RTC_INT_CHECK", $sformatf("WAIT FOR RTC IRQ %0d", cnt), UVM_NONE)
    @(posedge o_rtc_irq);
    cnt++;
    `uvm_info("DO_RTC_INT_CHECK", $sformatf("GOT RTC IRQ %0d", cnt), UVM_NONE)
    test_step++;
    
    // clear the interrupt
    rtc_read_eoi();
    test_step++;

    // keep rtc match value for interrupt as small
    match_val += 'h1555;
    rtc_write_match_val(match_val);
    test_step++;

    #10us;
    test_step++;
  end
  test_step = 2555;

endtask

//==============================================================================
// read registers
task do_rtc_reg_check();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  bit                          done     ;
  bit                          no_check ;

  // set pll
  test_step = 1500;
  #10us;

  // set address and expected data for first read
  test_addr = RTC_BASE_ADDR;
  exp_data  = 'hffffffff000005AA;
  no_check  = 1; //don't check this address. This is the rtc count and value will  change

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
     RTC_BASE_ADDR + 'h04 : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     RTC_BASE_ADDR + 'h08 : begin
       exp_data  = 'hFFFFFFFF_00000000;
     end
     RTC_BASE_ADDR + 'h0C : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     RTC_BASE_ADDR + 'h10 : begin
       exp_data  = 'hFFFFFFFF_00000000;
     end
     RTC_BASE_ADDR + 'h14 : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     RTC_BASE_ADDR + 'h18 : begin
       exp_data  = 'hFFFFFFFF_00000000;
     end
     RTC_BASE_ADDR + 'h1C : begin
       exp_data  = 'h3230392a_ffffffff;
     end
     RTC_BASE_ADDR + 'h20 : begin
       exp_data  = 'hffffffff_00000535;
     end
     RTC_BASE_ADDR + 'h24 : begin
       exp_data  = 'h00000000_FFFFFFFF;
     end
     RTC_BASE_ADDR + 'h28 : begin
       exp_data  = 'hDEADDEAD_DEADDEAD;
       test_addr = RTC_BASE_ADDR;
       // last address
       done = 1;
     end
    endcase
    test_step++;
  end while (!done);

  test_step = 1888;
endtask
