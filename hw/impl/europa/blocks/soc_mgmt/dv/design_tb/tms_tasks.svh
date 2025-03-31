// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Task for checking the tms

//==============================================================================
task tms_reg_check();
  chip_pkg::chip_axi_addr_t    test_addr;
  chip_pkg::chip_axi_lt_data_t exp_data ;
  bit                          done     ;
  bit                          no_check ;

  //============================================================================
  // Check from start of tms register address space
  test_addr = TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET;
  exp_data  = 'hffffffff_00030001;
  no_check  = 0;

  done = 0;
  do begin
    axi_reg_read  (test_addr, reg_read_data, reg_resp);
    if (no_check) begin
    end else begin
      check_reg_read(test_addr, reg_read_data            , exp_data);
    end
    check_axi_resp  (test_addr, axi_resp_e'(reg_resp), AXI_RESP_OKAY);

    no_check   = 0;
    test_addr += 4;
    case(test_addr)
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_CTRL_OFFSET                 : begin // 0x04
        exp_data = 'h00030001_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_DATA_OFFSET                 : begin // 0x08
        exp_data = 'hffffffff_00030001;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_0_OFFSET        : begin // 0x0c
        exp_data = 'h00030001ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_1_OFFSET        : begin // 0x10
        exp_data = 'hffffffff_00030001;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_2_OFFSET        : begin // 0x14
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_3_OFFSET        : begin // 0x18
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_4_OFFSET        : begin // 0x1c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_5_OFFSET        : begin // 0x20
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_0_OFFSET : begin // 0x24
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_1_OFFSET : begin // 0x28
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_2_OFFSET : begin // 0x2c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_3_OFFSET : begin // 0x30
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_4_OFFSET : begin // 0x34
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_5_OFFSET : begin // 0x38
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_0_OFFSET   : begin // 0x3c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_1_OFFSET   : begin // 0x40
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_2_OFFSET   : begin // 0x44
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_3_OFFSET   : begin // 0x48
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_4_OFFSET   : begin // 0x4c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_5_OFFSET   : begin // 0x50
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_0_OFFSET      : begin // 0x54
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_1_OFFSET      : begin // 0x58
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_2_OFFSET      : begin // 0x5C
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_3_OFFSET      : begin // 0x60
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_4_OFFSET      : begin // 0x64
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_5_OFFSET      : begin // 0x68
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_0_OFFSET     : begin // 0x6c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_1_OFFSET     : begin // 0x70
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_2_OFFSET     : begin // 0x74
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_3_OFFSET     : begin // 0x78
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_4_OFFSET     : begin // 0x7c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_5_OFFSET     : begin // 0x80
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET           : begin // 0x84
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET           : begin // 0x88
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET           : begin // 0x8c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET           : begin // 0x90
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET           : begin // 0x94
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET           : begin // 0x98
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET           : begin // 0x9c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET           : begin // 0xa0
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET           : begin // 0xa4
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET           : begin // 0xa8
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET           : begin // 0xac
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET           : begin // 0xb0
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET           : begin // 0xb4
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET           : begin // 0xb8
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET           : begin // 0xbc
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET           : begin // 0xc0
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET           : begin // 0xc4
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET           : begin // 0xc8
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_0_OFFSET       : begin // 0xcc
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_1_OFFSET       : begin // 0xd0
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_2_OFFSET       : begin // 0xd4
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_3_OFFSET       : begin // 0xd8
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_4_OFFSET       : begin // 0xdc
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_5_OFFSET       : begin // 0xe0
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_6_OFFSET       : begin // 0xe4
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_7_OFFSET       : begin // 0xe8
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_8_OFFSET       : begin // 0xec
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_9_OFFSET       : begin // 0xf0
        exp_data = 'hffffffff_00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_10_OFFSET      : begin // 0xf4
        exp_data = 'h00000000_ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_11_OFFSET      : begin // 0xf8
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_0_OFFSET     : begin // 0xfc
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_1_OFFSET     : begin // 0x100
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_2_OFFSET     : begin // 0x104
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_3_OFFSET     : begin // 0x108
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_4_OFFSET     : begin // 0x10c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_5_OFFSET     : begin // 0x110
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_6_OFFSET     : begin // 0x114
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_7_OFFSET     : begin // 0x118
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_8_OFFSET     : begin // 0x11c
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_9_OFFSET     : begin // 0x120
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_10_OFFSET    : begin // 0x124
        exp_data = 'h00000000ffffffff;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_11_OFFSET    : begin // 0x128
        exp_data = 'hffffffff00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET     : begin // 0x12c
        exp_data = 'h00000000ffffffff;
      end
      default : begin
        // Last address reached
        test_addr = TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET;
        exp_data  = 'hffffffff_00030001;
        // terminate loop
        done = 1;
      end
    endcase

  end while (!done);

endtask

//==============================================================================
task tms_jtag_reg_check();
  chip_pkg::chip_axi_addr_t test_addr;
  logic [31:0]              exp_data ;
  bit                       done     ;
  bit                       no_check ;

  //============================================================================
  // Check from start of tms register address space
  test_addr = TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET;
  exp_data  = 'h00030001;
  no_check  = 0;

  done = 0;
  do begin
    tms_jtag_set_instr_and_read_data(test_addr, reg_read_data);
    if (no_check) begin
    end else begin
      check_reg_read(test_addr, reg_read_data, exp_data);
    end

    no_check   = 0;
    test_addr += 4;
    case(test_addr)
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_CTRL_OFFSET                 : begin // 0x04
        exp_data = 'h1cc21000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_DATA_OFFSET                 : begin // 0x08
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_0_OFFSET        : begin // 0x0c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_1_OFFSET        : begin // 0x10
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_2_OFFSET        : begin // 0x14
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_3_OFFSET        : begin // 0x18
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_4_OFFSET        : begin // 0x1c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_5_OFFSET        : begin // 0x20
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_0_OFFSET : begin // 0x24
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_1_OFFSET : begin // 0x28
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_2_OFFSET : begin // 0x2c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_3_OFFSET : begin // 0x30
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_4_OFFSET : begin // 0x34
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_5_OFFSET : begin // 0x38
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_0_OFFSET   : begin // 0x3c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_1_OFFSET   : begin // 0x40
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_2_OFFSET   : begin // 0x44
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_3_OFFSET   : begin // 0x48
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_4_OFFSET   : begin // 0x4c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_5_OFFSET   : begin // 0x50
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_0_OFFSET      : begin // 0x54
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_1_OFFSET      : begin // 0x58
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_2_OFFSET      : begin // 0x5C
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_3_OFFSET      : begin // 0x60
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_4_OFFSET      : begin // 0x64
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_5_OFFSET      : begin // 0x68
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_0_OFFSET     : begin // 0x6c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_1_OFFSET     : begin // 0x70
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_2_OFFSET     : begin // 0x74
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_3_OFFSET     : begin // 0x78
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_4_OFFSET     : begin // 0x7c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_5_OFFSET     : begin // 0x80
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET           : begin // 0x84
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET           : begin // 0x88
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET           : begin // 0x8c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET           : begin // 0x90
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET           : begin // 0x94
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET           : begin // 0x98
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET           : begin // 0x9c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET           : begin // 0xa0
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET           : begin // 0xa4
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET           : begin // 0xa8
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET           : begin // 0xac
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET           : begin // 0xb0
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET           : begin // 0xb4
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET           : begin // 0xb8
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET           : begin // 0xbc
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET           : begin // 0xc0
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET           : begin // 0xc4
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET           : begin // 0xc8
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_0_OFFSET       : begin // 0xcc
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_1_OFFSET       : begin // 0xd0
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_2_OFFSET       : begin // 0xd4
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_3_OFFSET       : begin // 0xd8
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_4_OFFSET       : begin // 0xdc
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_5_OFFSET       : begin // 0xe0
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_6_OFFSET       : begin // 0xe4
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_7_OFFSET       : begin // 0xe8
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_8_OFFSET       : begin // 0xec
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_9_OFFSET       : begin // 0xf0
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_10_OFFSET      : begin // 0xf4
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_11_OFFSET      : begin // 0xf8
        exp_data = 'h00000007;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_0_OFFSET     : begin // 0xfc
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_1_OFFSET     : begin // 0x100
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_2_OFFSET     : begin // 0x104
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_3_OFFSET     : begin // 0x108
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_4_OFFSET     : begin // 0x10c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_5_OFFSET     : begin // 0x110
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_6_OFFSET     : begin // 0x114
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_7_OFFSET     : begin // 0x118
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_8_OFFSET     : begin // 0x11c
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_9_OFFSET     : begin // 0x120
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_10_OFFSET    : begin // 0x124
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_11_OFFSET    : begin // 0x128
        exp_data = 'h00000000;
      end
      TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET     : begin // 0x12c
        exp_data = 'h00000000;
      end
      default : begin
        // Last address reached
        test_addr = TMS_CSR_BASE_ADDR+tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET;
        exp_data  = 'h00030001;
        // terminate loop
        done = 1;
      end
    endcase

  end while (!done);

endtask

//============================================================================
task tms_jtag_set_instr_and_read_data(input [15:0] instr, output [31:0] data);
  bit [31:0] sr;
  // set instruction
  @(posedge tck); // test_logic_reset
  tms = 0;
  @(posedge tck); // run_test_idle
  tms = 1;
  @(posedge tck); // select_dr
  tms = 1;
  @(posedge tck); // select_ir
  tms = 0;
  @(posedge tck); // capture_ir
  tms = 0;
  repeat(16-1) begin
    @(posedge tck); // shift_ir
    // LSB first
    tms = instr[0];
    instr >>= 1;
    tms = 0;
  end
  @(posedge tck); // shift_ir
  tms = 1'h0;// read
  tms = 1;
  @(posedge tck); // exit1_ir
  tms = 1;
  //@(posedge tck); // pause_ir
  //tms = 1;
  //@(posedge tck); // exit2_ir
  //tms = 1;
  @(posedge tck); // update_ir
  tms = 0;
  @(posedge tck); // run_test_idle
  tms = 1;
  // shift data
  @(posedge tck); // select_dr
  tms = 0;
  @(posedge tck); // capture_dr
  tms = 0;
  sr = 0;
  repeat(32+1) begin
    @(posedge tck); // shift_dr
    // LSB first
    sr[32-1] = tdo;
    sr >>= 1;
    // MSB first
    //sr[0] = tdo;
    //sr <<= 1;
    tms = 0;
  end
  tms = 1;
  @(posedge tck); // exit1_dr
  tms = 1;
  @(posedge tck); // update_dr
  tms = 0;
  @(posedge tck); // run_tesT_idle
  tms = 1;
  repeat(3)@(posedge tck); // test_logic_reset
  // store output data
  data = sr;
endtask

