// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//        kevin luciani  <kevin.luciani@axelera.ai>
//
// Task for checking the otp

//==============================================================================
task otp_reg_check();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  chip_pkg::chip_axi_lt_data_t read_data ;
  chip_pkg::chip_axi_lt_data_t wr_data ;
  axi_pkg::axi_resp_t          axi_resp;
  bit                          done     ;
  bit                          no_check ;
  bit                          jtag_err;
  kse3_jtag_haddr_t            jtag_addr;
  soc_mgmt_hdata_t             jtag_exp_data;
  soc_mgmt_hdata_t             jtag_read_data;

  //============================================================================
  // Test error responses.
  // Access to OTP secure region from APU should return an error.
  wr_data   = 32'hDEAD_BEEF;

  test_addr = OTP_SECU_START_ADDR;
  axi_reg_write  (test_addr, wr_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);
  axi_reg_read   (test_addr, read_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);

  // Write access to OTP write protected region from APU should return an error.
  test_addr = OTP_WR_PROT_START_ADDR;
  axi_reg_write  (test_addr, wr_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);
  axi_reg_read   (test_addr, read_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);

  // Write access to AOR write protected region from APU should return an error.
  test_addr = AOR_WR_PROT_START_ADDR;
  axi_reg_write  (test_addr, wr_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);
  axi_reg_read   (test_addr, read_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);

  // Read/Write access to AOR secure region should not return an error.
  test_addr = AOR_SECU_START_ADDR;
  axi_reg_write  (test_addr, wr_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);
  axi_reg_read   (test_addr, read_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_SLVERR);

  //============================================================================
  // Enable smart programming to speed up OTP operations
  test_addr = OTP_HOST_BASE_ADDR + otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET;

  // word to doubleword alignment
  wr_data   = 64'h0000_0002;
  wr_data   = test_addr[2] ? wr_data << 32 : wr_data;

  axi_reg_write  (test_addr, wr_data,   axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  axi_reg_read   (test_addr, read_data, axi_resp);
  check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);

  test_addr = OTP_PUB_START_ADDR;
  wr_data   = 'h0010_0010;
  exp_data  = 'h0010_0010;

  done = 0;
  do begin

    axi_reg_write  (test_addr, exp_data,  axi_resp);
    axi_reg_read   (test_addr, read_data, axi_resp);

    check_reg_read (test_addr, read_data[31:0], exp_data[31:0]);
    check_axi_resp (test_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
    `uvm_info("OTP_REG_CHECK", $sformatf("test_addr = %4x, read_data = %8x, reg_resp = %2x", test_addr, read_data, reg_resp), UVM_NONE)

    // Increas address by 8 to keep address doubleword-aligned and simplify things.
    test_addr += 8;

    if (test_addr > OTP_PUB_START_ADDR + 'h20) begin
       done = 1;
    end

  end while (!done);

endtask
