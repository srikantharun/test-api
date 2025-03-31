// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Memmory map test for soc_mgmt
// Read the first word from each peripheral:
// and check read data matches expected.
// Also check response is always OK.

task memory_map_test();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  bit                          done     ;

  `uvm_info("MEMORY_MAP_TEST", "Test Start", UVM_NONE)

  #10us;

  // set address and expected data for first read
  test_addr = ROT_BASE_ADDR;
  exp_data  = 'hffffffffdead0000;

  done = 0;
  do begin
    axi_reg_read(test_addr, reg_read_data, reg_resp);
    `uvm_info("MEMORY_MAP_TEST", $sformatf("Read Addr: %0x Data: %0x Resp: %x", test_addr, reg_read_data, reg_resp), UVM_HIGH)
    check_reg_read(test_addr, reg_read_data            , exp_data);
    check_axi_resp(test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

    // Set the address and the expected data for the next read.
    // If the current address is for the last address then set done.
    case(test_addr)
      ROT_BASE_ADDR         : begin
        test_addr = OTP_HOST_BASE_ADDR;
        exp_data = 'hffffffff00000000;
      end
      OTP_HOST_BASE_ADDR    : begin  
        test_addr = TMS_CSR_BASE_ADDR;
        exp_data = 'hffffffff00030001;
      end
      TMS_CSR_BASE_ADDR     : begin
        test_addr = CLK_GEN_CSR_BASE_ADDR;
        exp_data = 'hffffffff00000000;
      end
      CLK_GEN_CSR_BASE_ADDR : begin
        test_addr = RST_GEN_CSR_BASE_ADDR;
        exp_data = 'hffffffff000a0007;
      end
      RST_GEN_CSR_BASE_ADDR : begin
        test_addr = RTC_BASE_ADDR;
        exp_data = 'hffffffff00000126;
      end
      RTC_BASE_ADDR         : begin
        test_addr = WTD_BASE_ADDR;
        exp_data = 'hffffffff00000000;
      end
      WTD_BASE_ADDR         : begin
        test_addr = DEBUGGER_BASE_ADDR;
        exp_data = 'hffffffffdead000a;
      end
      DEBUGGER_BASE_ADDR    : begin
        test_addr = MBIST_BASE_ADDR;
        exp_data = 'hffffffffdead000b;
      end
      MBIST_BASE_ADDR       : begin
        test_addr = TRACE_BUF_BASE_ADDR;
        exp_data = 'hffffffffdead000c;
      end
      TRACE_BUF_BASE_ADDR   : begin
        test_addr = RESRVD_BASE_ADDR;
        exp_data = 'hffffffffdead000d;
      end
      RESRVD_BASE_ADDR      : begin
        test_addr = ROT_BASE_ADDR;
        done = 1;
      end
    endcase

  end while (!done);

  #10us;
endtask

