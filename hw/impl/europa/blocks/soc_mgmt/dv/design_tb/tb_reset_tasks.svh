// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Testbench reset tasks


//==============================================================================
// set the por reset
task do_por_rst();
  for (int i=0; i<2; i++) begin
    drv_rst[0] = (i==0);
    #1ns;
  end
endtask

//==============================================================================
// set hw_reset_n
task do_hw_rst();
  for (int i=0; i<2; i++) begin
    drv_rst[1] = (i==0);
    #1ns;
  end
endtask

//==============================================================================
// sets i_rst_req_n input for stage0 basic block
task do_ao_rst_req();
  for (int i=0; i<2; i++) begin
    //i_ao_rst_req_n = (i==0);
    if (i==0) begin
      force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_ao_rst_req_n = 1'h0;
    end else begin
      release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_ao_rst_req_n;
    end
    #1ns;
  end
endtask

//==============================================================================
task set_global_rst_mask(bit [2:0] value);
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t reg_data ;

  test_addr     = RST_GEN_APB_BASE_ADDR + soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_GLOBAL_RST_OFFSET;
  reg_data      = 0      ;
  reg_data[ 2: 0] = value;
  reg_data[27:16] = 'ha  ; // heep stretch cycles at default value

  `uvm_info("GLOBAL_RST_MASK", $sformatf("DEBUG100 %0x,%0x", test_addr, reg_data), UVM_NONE)

  reg_data = shift_axi_write_data(test_addr, reg_data);
  axi_reg_write                  (test_addr, reg_data , reg_resp);
  check_axi_resp                 (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);
endtask

//==============================================================================
// write sw reset for specified stage
// sw reset supported fror multiple stage
task do_sw_rst(int stage_sel);
  chip_pkg::chip_axi_lt_data_t sw_rst_data  ;

  reg_addr       = RST_GEN_APB_BASE_ADDR;
  sw_rst_data    = 0;
  sw_rst_data[0] = 0; //sw reset is active low
   `uvm_info("SW_RESET", $sformatf("DEBUG200 %0x, %0x", reg_addr, sw_rst_data), UVM_NONE)

  case (stage_sel)
    //SMI SW Reset
    1       : begin
      reg_addr += soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_DMI_RST_OFFSET;
      repeat(2) begin
        syso_syscfg_apb_write(reg_addr, sw_rst_data, syscfg_slverr);
        // check axi response
        sw_rst_data[0] = 1; // clear sw reset
      end
    end
    // Global SW Reset
    2       : begin
      reg_addr += soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_GLOBAL_RST_OFFSET;
      repeat(2) begin
        syso_syscfg_apb_write(reg_addr, sw_rst_data, syscfg_slverr);
        // check axi response
        sw_rst_data[0] = 1; // clear sw reset
      end
    end
    // AO SW Reset
    default : begin
      reg_addr += soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_AO_RST_OFFSET;
      repeat(2) begin
        syso_syscfg_apb_write(reg_addr, sw_rst_data, syscfg_slverr);
        // check axi response
        sw_rst_data[0] = 1; // clear sw reset
        `uvm_info("SW_RESET", $sformatf("DEBUG202 %0x, %0x", reg_addr, sw_rst_data), UVM_NONE)
      end
    end
  endcase
endtask

//==============================================================================
task do_dmi_reset();
  for (int i=0; i<2; i++) begin
    i_dmi_rst_n = ~(i==0);
    #1ns;
  end
endtask

//==============================================================================
task do_tamper_reset();
  // TODO: ADI: fix reset when debug is inclueded.
  //for (int i=0; i<2; i++) begin
  //  i_tamper_rst_n = ~(i==0);
  //  #1ns;
  //end
endtask

//==============================================================================
task do_mbist_reset();
  // Mist_rst_n is removed
  //for (int i=0; i<2; i++) begin
  //  i_mbist_rst_n = ~(i==0);
  //  #1ns;
  //end
endtask

//==============================================================================
task do_debug_reset();
  for (int i=0; i<2; i++) begin
    if (i==0) begin
      force   i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_debug_rst_n = 1'h1;
    end else begin
      release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_debug_rst_n;
    end
    #1ns;
  end
endtask

//==============================================================================
task do_wdt_reset();
  for (int i=0; i<2; i++) begin
    if (i==0) begin
      force   i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_wdt_rst_n = 1'h1;
    end else begin
      release i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_reset_gen.i_wdt_rst_n;
    end
    #1ns;
  end
endtask

//==============================================================================
// register reset test
task do_rst_gen_reg_check();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  bit                          done     ;

  // set address and expected data for first read
  test_addr = RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_AO_RST_OFFSET;

  done = 0;
  do begin
    case(test_addr)
       RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_AO_RST_OFFSET         : begin
       exp_data  = 'h00A0007;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_AO_RST_OFFSET           : begin
        exp_data  = 'h00000001;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_DMI_RST_OFFSET         : begin
        exp_data  = 'h000A0000;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_DMI_RST_OFFSET          : begin
        exp_data  = 'h00000001;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_GLOBAL_RST_OFFSET      : begin
        exp_data  = 'h00A0007;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_SW_GLOBAL_RST_OFFSET       : begin
        exp_data  = 'h00000001;
      end
      RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_WDT_RESET_CONFIG_OFFSET        : begin
        exp_data  = 'h00000000;
        done = 1;
      end
      default : begin
        test_addr = RST_GEN_APB_BASE_ADDR+soc_mgmt_reset_gen_csr_reg_pkg::SOC_MGMT_RESET_GEN_CSR_RST_CFG_AO_RST_OFFSET;
        exp_data  = 'h0000001;
        done = 1;
      end
    endcase

    syso_syscfg_apb_read(test_addr, reg_read_data, syscfg_slverr);
    `uvm_info("RESET_REG_CHECK", $sformatf("DEBUG220 %0x,%0x,%0x,%0s", test_addr, reg_read_data, exp_data, reg_read_data==exp_data ? "OK" : "KO"), UVM_NONE)
    check_reg_read (test_addr, reg_read_data, exp_data);
    test_addr += 4;

  end while (!done);

endtask
