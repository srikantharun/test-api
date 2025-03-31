// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
// KSE3 related tests.

// TODO (kluciani, Silver, Add this test after fixing issue #2366)
task kse_warm_rest_test();

  logic [31:0] addr;
  logic [31:0] rdata;
  axi_pkg::axi_resp_t axi_resp;
  kse3_jtag_resp_t    jtag_resp_exp;

  localparam logic [31:0] WDATA_0 = 32'hFFFF_FFFF;
  localparam logic [31:0] WDATA_1 = 32'h0000_0001;

  jtag_resp_exp.cmd_ignored=1'b0;
  jtag_resp_exp.ahb_error=1'b0;
  jtag_resp_exp.kse_error=1'b0;

  kse3_jtag_tdr_init();

  fork
    // Start long OTP write operation via APU
    axi_32b_reg_write (OTP_PUB_START_ADDR, WDATA_0, axi_resp);
    begin
      repeat(40)
        @ (posedge o_periph_clk);
      // Trigger warm reset via JTAG_DBG_TDR
      do_set_jtag_dbg_tdr();
    end
  join_any

  // Issue OTP operation via JTAG
  kse3_jtag_ahb_write (OTP_PUB_START_ADDR+4, WDATA_1, axi_resp);

  // Check response and behaviour
  kse3_jtag_ahb_read (OTP_PUB_START_ADDR, rdata, jtag_resp_exp);
  if (rdata != WDATA_0)
    `uvm_error("kse_warm_rest_test", $sformatf("WDATA_0: expected = %8x, actual = %8x", WDATA_0, rdata))

  kse3_jtag_ahb_read (OTP_PUB_START_ADDR+4, rdata, jtag_resp_exp);
  if (rdata != WDATA_1)
    `uvm_error("kse_warm_rest_test", $sformatf("WDATA_1: expected = %8x, actual = %8x", WDATA_1, rdata))

endtask

task kse_jtag_test();

  logic [31:0] dest_addr;
  logic [31:0] rdata;
  kse3_jtag_resp_t    jtag_resp_exp;
  axi_pkg::axi_resp_t axi_resp;

  localparam soc_mgmt_haddr_t OTP_PERSO_STR_LEN_ADDR  = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_PERSO_STR_LEN_OFFSET;
  localparam soc_mgmt_haddr_t OTP_TRNG_CFG_ADDR       = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_TRNG_CFG_OFFSET;
  localparam soc_mgmt_haddr_t OTP_ANCHOR_VAL_LEN_ADDR = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR + otp_wrapper_pkg::OTP_ANCHOR_VAL_LEN_OFFSET;
  localparam logic [31:0] KSE3_AOR_INTEG_TEST_CMD    = 32'hCDFF_2003;

  kse3_jtag_tdr_init();

  // Ensure APU reads JTAG_DBG == 0 from AOR
  dest_addr = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR + soc_mgmt_secu_aor_csr_reg_pkg::SOC_MGMT_SECU_AOR_CSR_JTAG_DBG_OFFSET;
  axi_32b_reg_read (dest_addr, rdata, axi_resp);
  check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  if (rdata[0])
    `uvm_error("kse_jtag_test", $sformatf("APU JTAG_DBG AOR read: expected = 0, actual = %0d", rdata[0]))
  else
    `uvm_info("kse_jtag_test", "APU correctly read JTAG_DBG == 0", UVM_NONE)

  // No command allowed when jtag_dbg TDR is 0
  // No error generated but cmd_ignored shall be 1
  // Expect command to be ignored
  jtag_resp_exp.cmd_ignored=1'b1;
  jtag_resp_exp.ahb_error=1'b0;
  jtag_resp_exp.kse_error=1'b0;
  kse3_jtag_ahb_write (OTP_PERSO_STR_LEN_ADDR, 64, jtag_resp_exp);

  do_set_jtag_dbg_tdr();

  // Ensure APU will read JTAG_DBG == 1 from AOR
  dest_addr = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR + soc_mgmt_secu_aor_csr_reg_pkg::SOC_MGMT_SECU_AOR_CSR_JTAG_DBG_OFFSET;
  axi_32b_reg_read (dest_addr, rdata, axi_resp);
  check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  if (!rdata[0])
    `uvm_error("kse_jtag_test", $sformatf("APU JTAG_DBG AOR read: expected = 1, actual = %0d", rdata[0]))
  else
    `uvm_info("kse_jtag_test", "APU correctly read JTAG_DBG == 1", UVM_NONE)

  // Expect command to be executed
  jtag_resp_exp.cmd_ignored=1'b0;
  jtag_resp_exp.ahb_error=1'b0;
  jtag_resp_exp.kse_error=1'b0;
  kse3_jtag_ahb_read (OTP_PERSO_STR_LEN_ADDR, rdata, jtag_resp_exp);
  kse3_jtag_ahb_read (AOR_WR_PROT_START_ADDR, rdata, jtag_resp_exp);


  if (!use_kse3_integr_rom) begin

    `uvm_info("kse_jtag_test", "Start OTP programming via KSE3 JTAG", UVM_NONE)
    // Enable smart programming to speed up OTP operations
    dest_addr = OTP_HOST_BASE_ADDR + otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET;
    kse3_jtag_ahb_write (dest_addr, 32'h0000_0002, jtag_resp_exp);

    // Initialize OTP write-protected sections via KSE3 JTAG TAP.
    // This is possible because OTP is empty, hence we are in chip_wafer_test LCS.
    `uvm_info("kse_jtag_test", "1. Write Length of personalization string to OTP", UVM_NONE)
    kse3_jtag_ahb_write (OTP_PERSO_STR_LEN_ADDR, 64, jtag_resp_exp);
    `uvm_info("kse_jtag_test", "2. Write TRNG configuration to OTP", UVM_NONE)
    kse3_jtag_ahb_write (OTP_TRNG_CFG_ADDR,   32'h0200_9CC0, jtag_resp_exp);
    kse3_jtag_ahb_write (OTP_TRNG_CFG_ADDR+4, 32'h002A_0000, jtag_resp_exp);
    `uvm_info("kse_jtag_test", "3. Write AnchorValue length", UVM_NONE)
    kse3_jtag_ahb_write (OTP_ANCHOR_VAL_LEN_ADDR, 32'd32, jtag_resp_exp);
    `uvm_info("kse_jtag_test", "enter_jtag_access_mode command via JTAG", UVM_NONE)
    kse3_send_enter_jtag_access_mode(jtag_resp_exp);

  end

  //
  // Send command via KSE3 JTAG TAP, expect ignored due to enter_jtag_access_mode not yet executed.
  //
  if (use_kse3_integr_rom) begin
    `uvm_info("kse_jtag_test", "Running AOR self-test command via JTAG", UVM_NONE)
    kse_jtag_send_command(KSE3_AOR_INTEG_TEST_CMD);
  end

endtask

task kse_lcs_test();

  localparam logic [31:0] LCS_OBJ_ID = 32'h8100_0000;

  logic [31:0] dest_addr;
  logic [31:0] rdata;
  kse3_jtag_resp_t    jtag_resp_exp;
  axi_pkg::axi_resp_t axi_resp;

  jtag_resp_exp.cmd_ignored=1'b0;
  jtag_resp_exp.ahb_error=1'b0;
  jtag_resp_exp.kse_error=1'b0;

  do_set_jtag_dbg_tdr();

  // Enable smart programming to speed up OTP operations
  dest_addr = OTP_HOST_BASE_ADDR + otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET;
  kse3_jtag_ahb_write (dest_addr, 32'h0000_0002, jtag_resp_exp);

  `uvm_info("kse_lcs_test", "1. Write Length of personalization string to OTP", UVM_NONE)
  kse3_jtag_ahb_write (OTP_PERSO_STR_LEN_ADDR, 64, jtag_resp_exp);
  `uvm_info("kse_lcs_test", "2. Write TRNG configuration to OTP", UVM_NONE)
  kse3_jtag_ahb_write (OTP_TRNG_CFG_ADDR,   32'h0200_9CC0, jtag_resp_exp);
  kse3_jtag_ahb_write (OTP_TRNG_CFG_ADDR+4, 32'h002A_0000, jtag_resp_exp);
  `uvm_info("kse_lcs_test", "3. Write AnchorValue length", UVM_NONE)
  kse3_jtag_ahb_write (OTP_ANCHOR_VAL_LEN_ADDR, 32'd32, jtag_resp_exp);

  `uvm_info("kse_lcs_test", "enter_jtag_access_mode command via JTAG", UVM_NONE)
  kse3_send_enter_jtag_access_mode(jtag_resp_exp);

  `uvm_info("kse_lcs_test", "GetObject LCS", UVM_NONE)
  kse3_jtag_ahb_write (ROT_BASE_ADDR,   LCS_OBJ_ID, jtag_resp_exp);
  kse_jtag_send_command(kudelski_kse3_pkg::KSE3_CMD_GETOBJECT);
  kse3_jtag_ahb_read (ROT_BASE_ADDR+12, rdata, jtag_resp_exp);
  `uvm_info("kse_lcs_test", $sformatf("LCS=%8x", rdata), UVM_NONE)

  `uvm_info("kse_lcs_test", "Move to chip_perso LCS", UVM_NONE)
  kse3_jtag_ahb_write (ROT_BASE_ADDR,   LCS_OBJ_ID, jtag_resp_exp);
  kse3_jtag_ahb_write (ROT_BASE_ADDR+4, 32'h0000_0002, jtag_resp_exp);
  kse3_jtag_ahb_write (ROT_BASE_ADDR+8, 32'h0000_0002, jtag_resp_exp);
  kse_jtag_send_command(kudelski_kse3_pkg::KSE3_CMD_SETOBJECT);

  do_cold_reset();
  do_set_jtag_dbg_tdr();

  `uvm_info("kse_lcs_test", "enter_jtag_access_mode command via JTAG", UVM_NONE)
  kse3_send_enter_jtag_access_mode(jtag_resp_exp);

  `uvm_info("kse_lcs_test", "GetObject LCS", UVM_NONE)
  kse3_jtag_ahb_write (ROT_BASE_ADDR,   LCS_OBJ_ID, jtag_resp_exp);
  kse_jtag_send_command(kudelski_kse3_pkg::KSE3_CMD_GETOBJECT);
  kse3_jtag_ahb_read (ROT_BASE_ADDR+12, rdata, jtag_resp_exp);
  `uvm_info("kse_lcs_test", $sformatf("LCS=%8x", rdata), UVM_NONE)

  `uvm_info("kse_lcs_test", "Move to user_delivery LCS", UVM_NONE)
  kse3_jtag_ahb_write (ROT_BASE_ADDR,   LCS_OBJ_ID, jtag_resp_exp);
  kse3_jtag_ahb_write (ROT_BASE_ADDR+4, 32'h0000_0002, jtag_resp_exp);
  kse3_jtag_ahb_write (ROT_BASE_ADDR+8, 32'h0000_0003, jtag_resp_exp);
  kse_jtag_send_command(kudelski_kse3_pkg::KSE3_CMD_SETOBJECT);

  do_cold_reset();
  do_set_jtag_dbg_tdr();

  `uvm_info("kse_lcs_test", "enter_jtag_access_mode command via JTAG", UVM_NONE)
  kse3_send_enter_jtag_access_mode(jtag_resp_exp);

  `uvm_info("kse_lcs_test", "init_kse3_adac_itf command via JTAG", UVM_NONE)
  kse3_send_init_kse3_adac_itf(jtag_resp_exp);

endtask

task kse_integration_test();
  logic [31:0]                 rdata;
  axi_pkg::axi_resp_t          axi_resp;

  localparam logic [31:0] KSE3_DRAM_INTEG_TEST_CMD_0 = 32'hBF00_0003;
  localparam logic [31:0] KSE3_DRAM_INTEG_TEST_CMD_1 = 32'hBF00_0103;
  localparam logic [31:0] KSE3_DRAM_INTEG_TEST_CMD_2 = 32'hBF00_0203;
  localparam logic [31:0] KSE3_DRAM_INTEG_TEST_CMD_3 = 32'hBE00_0003;
  localparam logic [31:0] KSE3_IRAM_INTEG_TEST_CMD_0 = 32'hC200_0003;
  localparam logic [31:0] KSE3_IRAM_INTEG_TEST_CMD_1 = 32'hC200_0103;
  localparam logic [31:0] KSE3_IRAM_INTEG_TEST_CMD_2 = 32'hC200_0203;
  localparam logic [31:0] KSE3_AOR_INTEG_TEST_CMD    = 32'hCDFF_2003;
  localparam logic [31:0] KSE3_OTP_WR_INTEG_TEST_CMD = 32'hC400_0003;
  localparam logic [31:0] KSE3_OTP_RD_INTEG_TEST_CMD = 32'hC000_0003;
  //
  // DRAM self-test
  //
  `uvm_info("KSE_MAIN", "Running DRAM self-test command", UVM_NONE)
  kse_send_command(KSE3_DRAM_INTEG_TEST_CMD_0);
  kse_send_command(KSE3_DRAM_INTEG_TEST_CMD_1);
  kse_send_command(KSE3_DRAM_INTEG_TEST_CMD_2);
  kse_send_command(KSE3_DRAM_INTEG_TEST_CMD_3);
  //
  // IRAM self-test
  //
  `uvm_info("KSE_MAIN", "Running IRAM self-test command", UVM_NONE)
  kse_send_command(KSE3_IRAM_INTEG_TEST_CMD_0);
  kse_send_command(KSE3_IRAM_INTEG_TEST_CMD_1);
  kse_send_command(KSE3_IRAM_INTEG_TEST_CMD_2);
  //
  // AOR self-test
  //
  `uvm_info("KSE_MAIN", "Running AOR self-test command", UVM_NONE)
  kse_send_command(KSE3_AOR_INTEG_TEST_CMD);
  //
  // INFO: Read NAGRA_ID and print it out.
  //
  axi_32b_reg_read (ROT_BASE_ADDR + kudelski_kse3_pkg::KSE_NAGRA_ID_OFFSET, rdata, axi_resp);
  `uvm_info("KSE_MAIN", $sformatf("NAGRA ID = %8x", rdata), UVM_NONE)

endtask

task kse_apu_test();
  chip_pkg::chip_axi_addr_t    src_addr;
  chip_pkg::chip_axi_addr_t    dest_addr;
  int unsigned                 transfer_size;
  logic [31:0]                 anchor_value_length;
  logic [31:0]                 perso_string_length;
  logic [31:0]                 chip_id;
  logic [31:0]                 dbg_counter;
  logic [31:0]                 rdata;
  axi_pkg::axi_resp_t          axi_resp;

  // Enable smart programming to speed up OTP operations
  dest_addr = OTP_HOST_BASE_ADDR + otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET;
  axi_32b_reg_write (dest_addr, 32'h0000_0002, axi_resp);
  check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);

  `uvm_info("KSE_MAIN", "***** ENTER_HW_JTAG_ACCESS_MODE sequence START *****", UVM_NONE)
  // ---------------------------------------------------------------------------
  // ENTER_HW_JTAG_ACCESS_MODE sequence
  // ---------------------------------------------------------------------------
  //
  // InitRoT
  //
  `uvm_info("KSE_MAIN", "Running InitRot command", UVM_NONE)
  kse_send_command(kudelski_kse3_pkg::KSE3_CMD_INITROT | kudelski_kse3_pkg::KSE3_CMD_IRQ_DIS_MASK);
  //
  // InitCrypto
  //
  // 1. Write Length of personalization string to KSE3 DRAM
  //
  `uvm_info("KSE_MAIN", "Initializing Personalization string length in DRAM", UVM_NONE)
  perso_string_length = 64;
  dest_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_DRAM_PERSO_STR_LEN_OFFSET;
  axi_32b_reg_write (dest_addr, perso_string_length, axi_resp);
  //
  // 2. Copy TRNG configuration to KSE3 DRAM
  //
  `uvm_info("KSE_MAIN", "Initializing TRNG configuration in DRAM", UVM_NONE)
  dest_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_DRAM_TRNG_CFG_OFFSET;
  axi_32b_reg_write (dest_addr,   32'h0200_9CC0, axi_resp);
  check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  axi_32b_reg_write (dest_addr+4, 32'h002A_0000, axi_resp);
  check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  //
  // 3. Copy Personalization string to KSE3 DRAM
  //
  `uvm_info("KSE_MAIN", "Initializing personalization string in DRAM", UVM_NONE)
  for (int i=0; i<perso_string_length; i=i+4) begin
    dest_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_DRAM_PERSO_STR_VAL_OFFSET + i;
    axi_32b_reg_write (dest_addr, 32'hDEAD_BEEF, axi_resp);
    check_axi_resp (dest_addr, axi_resp_e'(axi_resp), AXI_RESP_OKAY);
  end
  //
  // 4. Run InitCrypto command
  //
  `uvm_info("KSE_MAIN", "Running InitCrypto command", UVM_NONE)
  kse_send_command(kudelski_kse3_pkg::KSE3_CMD_INITCRYPTO | kudelski_kse3_pkg::KSE3_CMD_IRQ_DIS_MASK);

endtask

// ---------------------------------------------------------------------------
// KSE3 command
// ---------------------------------------------------------------------------
task kse_send_command(input logic [31:0] cmd);

  bit                           kse_busy;
  bit                           error;
  chip_pkg::chip_axi_addr_t     kse_addr;
  logic [31:0]                  read_data;
  axi_pkg::axi_resp_t           axi_resp;

  // Poll KSE3 status
  `uvm_info("KSE_SEND_COMMAND", $sformatf("Polling KSE3 START..."), UVM_NONE)
  do begin
    kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
    axi_32b_reg_read (kse_addr, read_data, axi_resp);
    kse_busy = read_data[0];
  end while (kse_busy);
  `uvm_info("KSE_SEND_COMMAND", $sformatf("Polling KSE3 END"), UVM_NONE)

  // Send command
  kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
  axi_32b_reg_write (kse_addr, cmd, axi_resp);
  `uvm_info("KSE_SEND_COMMAND", $sformatf("Sent command = %8x", cmd), UVM_NONE)

  // Poll KSE3 status
  `uvm_info("KSE_SEND_COMMAND", $sformatf("Polling KSE3 START..."), UVM_NONE)
  do begin
    kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
    axi_32b_reg_read (kse_addr, read_data, axi_resp);
    kse_busy = read_data[0];
  end while (kse_busy);
  `uvm_info("KSE_SEND_COMMAND", $sformatf("Polling KSE3 END"), UVM_NONE)

  // Check command return code
  kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_STATUS_OFFSET;
  axi_32b_reg_read (kse_addr, read_data, axi_resp);
  error = read_data != kudelski_kse3_pkg::KSE3_CMD_STATUS_SUCCESS;
  if (error) begin
    `uvm_error("KSE_SEND_COMMAND", $sformatf("ERROR KSE3 command execution failed with STATUS = %8x", read_data))
  end

endtask

task kse_jtag_send_command(input logic [31:0] cmd);

  bit                           kse_busy;
  bit                           error;
  kse3_jtag_haddr_t             kse_addr;
  logic [31:0]                  read_data;
  logic                         jtag_err_exp;

  jtag_err_exp = 1'b0;

  // Poll KSE3 status
  `uvm_info("KSE_SEND_JTAG_COMMAND", $sformatf("Polling KSE3 START..."), UVM_NONE)
  do begin
    kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
    kse3_jtag_ahb_read (kse_addr, read_data, jtag_err_exp);
    kse_busy = read_data[0];
  end while (kse_busy);
  `uvm_info("KSE_SEND_JTAG_COMMAND", $sformatf("Polling KSE3 END"), UVM_NONE)

  // Send command
  kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
  kse3_jtag_ahb_write (kse_addr, cmd, jtag_err_exp);
  `uvm_info("KSE_SEND_JTAG_COMMAND", $sformatf("Sent command = %8x", cmd), UVM_NONE)

  // Poll KSE3 status
  `uvm_info("KSE_SEND_JTAG_COMMAND", $sformatf("Polling KSE3 START..."), UVM_NONE)
  do begin
    kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_CTRL_OFFSET;
    kse3_jtag_ahb_read (kse_addr, read_data, jtag_err_exp);
    kse_busy = read_data[0];
  end while (kse_busy);
  `uvm_info("KSE_SEND_JTAG_COMMAND", $sformatf("Polling KSE3 END"), UVM_NONE)

  // Check command return code
  kse_addr = ROT_BASE_ADDR + kudelski_kse3_pkg::KSE3_CMD_STATUS_OFFSET;
  kse3_jtag_ahb_read (kse_addr, read_data, jtag_err_exp);
  error = read_data != kudelski_kse3_pkg::KSE3_CMD_STATUS_SUCCESS;
  if (error) begin
    `uvm_error("KSE_SEND_JTAG_COMMAND", $sformatf("ERROR KSE3 command execution failed with STATUS = %8x", read_data))
  end

endtask

task do_cold_reset();

  `uvm_info("do_cold_reset", "Cold reset started...", UVM_NONE)
  drv_rst='1;
  #100ns;
  kse3_jtag_tdr_init();
  #100ns;
  drv_rst='0;
  @(posedge o_global_rst_n);
  @(posedge o_periph_clk);
  @(posedge o_periph_clk);

  fast_clk_setup();
  `uvm_info("do_cold_reset", "Out of cold reset", UVM_NONE)

endtask

task do_set_jtag_dbg_tdr();

  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_jtag_dbg = 1'b1;

  `uvm_info("do_set_jtag_dbg_tdr", "Warm reset started...", UVM_NONE)
  // Wait for reset to be released
  @(posedge o_global_rst_n);
  @(posedge o_periph_clk);
  @(posedge o_periph_clk);
  #100ns;
  `uvm_info("do_set_jtag_dbg_tdr", "Out of reset", UVM_NONE)

endtask
