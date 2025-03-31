// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>


//! OTP Package
/// Contains all necessary type definitions, constants, and generally useful functions.
///
package otp_wrapper_pkg;

  // 16Kb OTP specific parameters
  // bit-addressable address width
  parameter int unsigned OTP_BIT_ADDR_W = 14;
  // byte-addressable address width
  parameter int unsigned OTP_BYTE_ADDR_W = OTP_BIT_ADDR_W-3;
  // word-addressable address width
  parameter int unsigned OTP_WORD_ADDR_W = OTP_BIT_ADDR_W-5;
  parameter int unsigned OTP_DATA_W = 32;
  parameter int unsigned OTP_LOCK_DEPTH = 8;

  typedef logic [OTP_BIT_ADDR_W-1:0]    otp_addr_t;
  typedef logic [OTP_DATA_W-1:0]        otp_data_t;
  typedef logic [OTP_LOCK_DEPTH-1:0]    otp_lock_t;

  parameter int unsigned OTP_LCS_W = 8;

  // LifeCycle State encodings
  parameter logic [OTP_LCS_W-1:0] LCS_CHIP_WAFER_TEST     = 8'h00;
  parameter logic [OTP_LCS_W-1:0] LCS_CHIP_PERSO          = 8'h01;
  parameter logic [OTP_LCS_W-1:0] LCS_USER_DELIVERY       = 8'h03;
  parameter logic [OTP_LCS_W-1:0] LCS_USER_SECURED        = 8'h07;
  parameter logic [OTP_LCS_W-1:0] LCS_USER_DECOMMISSIONED = 8'h0F;
  parameter logic [OTP_LCS_W-1:0] LCS_CHIP_FIELD_RETURN   = 8'h1F;
  parameter logic [OTP_LCS_W-1:0] LCS_TERMINATED          = 8'h3F;

  parameter logic [OTP_LCS_W-1:0] OTP_MAGIC_WAFER_TEST = 8'h00;
  parameter logic [OTP_LCS_W-1:0] OTP_MAGIC = 8'h5A;

  ////////////////////////////////
  /// OTP address map locations //
  ////////////////////////////////
  /// Anchor value length address
  parameter otp_addr_t OTP_ANCHOR_VAL_LEN_OFFSET      = 14'h0100;
  /// CA1 anchor value address
  parameter otp_addr_t OTP_CA1_ANCHOR_VAL_OFFSET      = 14'h0104;
  /// CA2 anchor value address
  parameter otp_addr_t OTP_CA2_ANCHOR_VAL_OFFSET      = 14'h0258;
  /// TRNG configuration address
  parameter otp_addr_t OTP_TRNG_CFG_OFFSET            = 14'h0144;
  /// Personalization string length address
  parameter otp_addr_t OTP_PERSO_STR_LEN_OFFSET       = 14'h014C;
  /// Personalization string address
  parameter otp_addr_t OTP_PERSO_STR_VAL_OFFSET       = 14'h0150;
  /// DBG counter address
  parameter otp_addr_t OTP_DBG_COUNTER_OFFSET         = 14'h0190;
  /// SoC class address
  parameter otp_addr_t OTP_SOC_CLASS_OFFSET           = 14'h0194;
  /// Chip ID address
  parameter otp_addr_t OTP_CHIP_ID_OFFSET             = 14'h0198;

  //////////////////////////////////
  /// OTP map field sizes (bytes) //
  //////////////////////////////////
  /// Anchor value length size
  parameter int unsigned OTP_ANCHOR_VAL_LEN_SIZE        = 4;
  /// CA1 anchor value size
  parameter int unsigned OTP_CA1_ANCHOR_VAL_SIZE        = 64;
  /// CA2 anchor value size
  parameter int unsigned OTP_CA2_ANCHOR_VAL_SIZE        = 64;
  /// TRNG configuration size
  parameter int unsigned OTP_TRNG_CFG_SIZE              = 8;
  /// Personalization string length size
  parameter int unsigned OTP_PERSO_STR_LEN_SIZE         = 4;
  /// Personalization string size
  parameter int unsigned OTP_PERSO_STR_VAL_SIZE         = 64;
  /// DBG counter size
  parameter int unsigned OTP_DBG_COUNTER_SIZE           = 4;
  /// SoC class size
  parameter int unsigned OTP_SOC_CLASS_SIZE             = 4;
  /// Chip ID size
  parameter int unsigned OTP_CHIP_ID_SIZE               = 16;

endpackage
