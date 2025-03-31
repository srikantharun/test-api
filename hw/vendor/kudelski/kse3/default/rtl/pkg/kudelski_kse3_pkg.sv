// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
/// KSE paramerters package
///

package kudelski_kse3_pkg;

  /// KSE3 AHB address width
  parameter int unsigned KSE3_AHB_ADDR_W = 13;
  /// KSE3 AHB data width
  parameter int unsigned KSE3_AHB_DATA_W = 32;

  /// KSE3 8-bit APB address width
  parameter int unsigned KSE3_APB_ADDR_W = 9;
  /// KSE3 8-bit APB data width
  parameter int unsigned KSE3_APB_DATA_W = 8;

  /// KSE3 ROM address width
  parameter int unsigned KSE3_ROM_ADDR_W = 15;
  /// KSE3 ROM data width
  parameter int unsigned KSE3_ROM_DATA_W = 36;
  /// KSE3 ROM number of words
  parameter int unsigned KSE3_ROM_WORDS  = 32768;

  /// KSE3 IRAM address width
  parameter int unsigned KSE3_IRAM_ADDR_W = 13;
  /// KSE3 IRAM data width
  parameter int unsigned KSE3_IRAM_DATA_W = 36;
  /// KSE3 IRAM number of words
  parameter int unsigned KSE3_IRAM_WORDS  = 8192;

  /// KSE3 DRAM address width
  parameter int unsigned KSE3_DRAM_ADDR_W = 12;
  /// KSE3 DRAM data width
  parameter int unsigned KSE3_DRAM_DATA_W = 40;
  /// KSE3 DRAM number of words
  parameter int unsigned KSE3_DRAM_WORDS  = 4096;

  /// KSE3 static config input width
  parameter int unsigned KSE3_CONFIG_W = 8;

  /// KSE3 Ring Oscillator input width
  parameter int unsigned KSE3_RO_CLK_W = 8;

  ///////////////////////////
  // KSE Keybus parameters //
  ///////////////////////////
  parameter int unsigned KSE3_KEYBUS_ACK_W  = 2;
  parameter int unsigned KSE3_KEYBUS_SEL_W  = 2;
  parameter int unsigned KSE3_KEYBUS_ADDR_W = 4;
  parameter int unsigned KSE3_KEYBUS_DATA_W = 32;

  /// AHB address type
  typedef logic[KSE3_AHB_ADDR_W-1:0]    kse3_ahb_haddr_t;
  /// AHB data type
  typedef logic[KSE3_AHB_DATA_W-1:0]    kse3_ahb_hdata_t;
  /// APB 8 bits address type
  typedef logic[KSE3_APB_ADDR_W-1:0]    kse3_apb_paddr_t;
  /// APB 8 bits data type
  typedef logic[KSE3_APB_DATA_W-1:0]    kse3_apb_pdata_t;
  /// ROM address type
  typedef logic[KSE3_ROM_ADDR_W-1:0]    kse3_rom_addr_t;
  /// ROM data type
  typedef logic[KSE3_ROM_DATA_W-1:0]    kse3_rom_data_t;
  /// IRAM address type
  typedef logic[KSE3_IRAM_ADDR_W-1:0]   kse3_iram_addr_t;
  /// IRAM data type
  typedef logic[KSE3_IRAM_DATA_W-1:0]   kse3_iram_data_t;
  /// DRAM address type
  typedef logic[KSE3_DRAM_ADDR_W-1:0]   kse3_dram_addr_t;
  /// DRAM data type
  typedef logic[KSE3_DRAM_DATA_W-1:0]   kse3_dram_data_t;
  /// Config type
  typedef logic[KSE3_CONFIG_W-1:0]      kse3_config_t;
  /// Ring Oscillator input type
  typedef logic[KSE3_RO_CLK_W-1:0]      kse_ro_clk_t;
  //////////////////
  // KeyBus types //
  //////////////////
  typedef logic[KSE3_KEYBUS_ACK_W-1:0]  kse_keybus_ack_t;
  typedef logic[KSE3_KEYBUS_SEL_W-1:0]  kse_keybus_sel_t;
  typedef logic[KSE3_KEYBUS_ADDR_W-1:0] kse_keybus_addr_t;
  typedef logic[KSE3_KEYBUS_DATA_W-1:0] kse_keybus_data_t;

  /// KSE3 AHB mailbox data RAM start address
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_START_OFFSET = 'h0000;
  /// KSE3 AHB mailbox data RAM end address
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_END_OFFSET   = 'h11FF;
  /// KSE3 AHB Control Status Registers start address
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_CSR_START_OFFSET  = 'h1200;
  /// KSE3 AHB Control Status Registers end address
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_CSR_END_OFFSET    = 'h123F;


  /// KSE3 SOC_AOR address width
  parameter int unsigned KSE3_OTP_ADDR_W = 8;
  /// KSE3 SOC_AOR address width
  parameter int unsigned KSE3_AOR_ADDR_W = 4;

  /// KSE3 APB OTP start address
  parameter logic[KSE3_APB_ADDR_W-1:0] KSE3_OTP_START_ADDR = 'h000;
  /// KSE3 APB OTP end address
  parameter logic[KSE3_APB_ADDR_W-1:0] KSE3_OTP_END_ADDR   = 'h0FF;
  /// KSE3 APB AOR start address
  parameter logic[KSE3_APB_ADDR_W-1:0] KSE3_AOR_START_ADDR = 'h100;
  /// KSE3 APB AOR end address
  parameter logic[KSE3_APB_ADDR_W-1:0] KSE3_AOR_END_ADDR   = 'h10F;

  //////////////////////////////////
  // KSE CSR interface parameters //
  //////////////////////////////////
  parameter int unsigned KSE3_CMD_TOKEN_W = 8;
  parameter int unsigned KSE3_CMD_SUB_CMD_W = 16;
  parameter int unsigned KSE3_CMD_RFU_W = 6;

  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_CMD_CTRL_OFFSET   = KSE3_CSR_START_OFFSET + 'h0000;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_CMD_STATUS_OFFSET = KSE3_CSR_START_OFFSET + 'h0004;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_CMD_TRK_OFFSET     = KSE3_CSR_START_OFFSET + 'h0008;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_CMD_PERF_OFFSET    = KSE3_CSR_START_OFFSET + 'h000c;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_INT_CTRL_OFFSET    = KSE3_CSR_START_OFFSET + 'h0010;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_PWR_CTRL_OFFSET    = KSE3_CSR_START_OFFSET + 'h0014;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_HW_ID_OFFSET       = KSE3_CSR_START_OFFSET + 'h0018;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_NAGRA_ID_OFFSET    = KSE3_CSR_START_OFFSET + 'h001c;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_DBG_INFO_0_OFFSET  = KSE3_CSR_START_OFFSET + 'h0020;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_DBG_INFO_1_OFFSET  = KSE3_CSR_START_OFFSET + 'h0024;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE_DBG_INFO_2_OFFSET  = KSE3_CSR_START_OFFSET + 'h0028;

  // Masks added to a command;s encoding to disable IRQ generation at the end of command execution.
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_IRQ_DIS_MASK    = 32'h0000_0002;

  // Commands encoding, with start bit = 1.
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_INITROT         = 32'h0100_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_INITCRYPTO      = 32'h0200_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_SETOBJECT       = 32'hA010_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_GETOBJECT       = 32'hA011_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_SETSOCCONFIG    = 32'hA000_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_GETCHALLENGE    = 32'hA003_0001;
  parameter logic[KSE3_AHB_DATA_W-1:0]   KSE3_CMD_UNLOCKACCESS    = 32'hA002_0001;

  // Command status register encodings.
  parameter logic[KSE3_AHB_ADDR_W-1:0]   KSE3_CMD_STATUS_SUCCESS  = 32'h0000_00E5;

  /////////////////////////////////////////////
  // KSE DRAM addresses for command operands //
  /////////////////////////////////////////////
  // InitCrypto
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_PERSO_STR_LEN_OFFSET  = KSE3_DRAM_START_OFFSET + 'h0000;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_TRNG_CFG_OFFSET       = KSE3_DRAM_START_OFFSET + 'h0040;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_PERSO_STR_VAL_OFFSET  = KSE3_DRAM_START_OFFSET + 'h0180;
  // SetObject
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_SET_OBJ_TYPEID_OFFSET = KSE3_DRAM_START_OFFSET + 'h0000;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_ANCHOR_VAL_LEN_OFFSET = KSE3_DRAM_START_OFFSET + 'h0004;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_ANCHOR_VAL_OFFSET     = KSE3_DRAM_START_OFFSET + 'h0008;
  // SetSocConfig
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_SOC_ID_OFFSET         = KSE3_DRAM_START_OFFSET + 'h0000;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_SOC_ID_INV_OFFSET     = KSE3_DRAM_START_OFFSET + 'h0010;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_DBG_COUNTER_OFFSET    = KSE3_DRAM_START_OFFSET + 'h0020;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_DBG_COUNTER_INV_OFFSET= KSE3_DRAM_START_OFFSET + 'h0024;
  parameter logic[KSE3_AHB_ADDR_W-1:0] KSE3_DRAM_SOC_CLASS_OFFSET      = KSE3_DRAM_START_OFFSET + 'h0028;

  parameter logic[KSE3_AHB_DATA_W-1:0] KSE3_DRAM_CA1_AV_TYPEID_VAL    = 32'h8008_0000;
  parameter logic[KSE3_AHB_DATA_W-1:0] KSE3_DRAM_CA2_AV_TYPEID_VAL    = 32'h800C_0000;

endpackage
