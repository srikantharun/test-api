//------------------------------------------------------------------------------
//
//            CADENCE                    Copyright (c) 2013
//                                       Cadence Design Systems, Inc.
//                                       All rights reserved.
//
//  This work may not be copied, modified, re-published, uploaded, executed, or
//  distributed in any way, in any medium, whether in whole or in part, without
//  prior written permission from Cadence Design Systems, Inc.
//------------------------------------------------------------------------------
//
//   Author                : mrodzik@cadence.com
//
//   Date                  : $Date$
//
//   Last Changed Revision : $LastChangedRevision$
//
//------------------------------------------------------------------------------
//   Description
//
//   UHS-II parameters for card model.
//
//------------------------------------------------------------------------------

package uhsii_params_pkg;

  // LINK <-> PHY PHYSICAL LANES STATUS
  const bit [1:0] PLSM_RXTX_EIDL         = 2'b00;
  const bit [1:0] PLSM_RXTX_OFF          = 2'b01; 
  const bit [1:0] PLSM_RXTX_STB          = 2'b10; 
  const bit [1:0] PLSM_RXTX_VLD          = 2'b11;

  // PHY commands
  const bit [3:0] PCMD_NO_COMMAND        = 4'b0000;
  const bit [3:0] PCMD_ENTER_LOOPBACK    = 4'b0001;
  const bit [3:0] PCMD_EXIT_LOOPBACK     = 4'b0011;
  const bit [3:0] PCMD_ENTER_2L_HDIN     = 4'b0101;
  const bit [3:0] PCMD_ENTER_2L_HDOUT    = 4'b0110;
  const bit [3:0] PCMD_EXIT_2L_HD        = 4'b0111; 
  
  // *** Link Symbol Set ***

  const bit [7:0] LSS_SYN0               = 8'hbf; //Synchronization D31.5
  const bit       LSS_SYN0_M             = 1'b0;
  const bit [7:0] LSS_SYN1               = 8'h5a; //Synchronization D26.2
  const bit       LSS_SYN1_M             = 1'b0;
  const bit [7:0] LSS_BSYN0              = 8'ha4; //Synchronization when boot code loading D4.5
  const bit       LSS_BSYN0_M            = 1'b0;
  const bit [7:0] LSS_BSYN1              = 8'h55; //Synchronization when boot code loading D21.2
  const bit       LSS_BSYN1_M            = 1'b0;
  const bit [7:0] LSS_DIR                = 8'h5f; //Direction Switch D31.2
  const bit       LSS_DIR_M              = 1'b0;
  const bit [7:0] LSS_LIDL0              = 8'h7c; //Logical IDLE K28.3
  const bit       LSS_LIDL0_M            = 1'b1;
  const bit [7:0] LSS_LIDL1              = 8'hf0; //Logical IDLE D16.7
  const bit       LSS_LIDL1_M            = 1'b0;
  const bit [7:0] LSS_DIDL0              = 8'hdc; //Logical Idle during data transmission K28.6
  const bit       LSS_DIDL0_M            = 1'b1;
  const bit [7:0] LSS_DIDL1              = 8'h4c; //Logical Idle during data transmission D12.2
  const bit       LSS_DIDL1_M            = 1'b0;
  const bit [7:0] LSS_COM                = 8'hbc; //Comma K28.5
  const bit       LSS_COM_M              = 1'b1;
  const bit [7:0] LSS_PAD                = 8'hf7; //Padding K23.7
  const bit       LSS_PAD_M              = 1'b1;
  const bit [7:0] LSS_SDB                = 8'h1c; //Start of DATA Burst
  const bit       LSS_SDB_M              = 1'b1;
  const bit [7:0] LSS_SOP                = 8'h3c; //Start of Packet
  const bit       LSS_SOP_M              = 1'b1;
  const bit [7:0] LSS_EDB                = 8'hfb; //End of DATA Burst
  const bit       LSS_EDB_M              = 1'b1;
  const bit [7:0] LSS_EOP                = 8'hfd; //End of Packet
  const bit       LSS_EOP_M              = 1'b1;

  // timing limits (IN CLOCK CYLES)
  //const int T_DMT_ENTRY            = 16'h02ee;            //T_DMT_ENTRY = 750 RCLK CYCLES
  const int T_DMT_ENTRY_PCLK_A     = 16'h0232;            //T_DMT_ENTRY IN PCLK RANGE A SI
  const int T_EIDL_ENTRY           = 16'h0004;            // IN SI
  const int T_EIDL_GAP             = 16'h0010;            // SLI, 4/24/2013, Q1, changed 0x08 to 0x10
  const int T_EIDL_RECOVERY        = 16'h0010;            // IN SI
  const int T_DIR_SWITCH           = 16'h0008;            // IN SI 

  // *** UHSII REG OFFSETS ***

  const bit [11:0]  CFG_BASE           = 12'h000;
  const bit [11:0]  INT_BASE           = 12'h100;
  const bit [11:0]  ST_BASE            = 12'h180;
  const bit [11:0]  CMD_BASE           = 12'h200;
  const bit [11:0]  VU_BASE            = 12'hF00;

  // *** UHSII (NATIVE) COMMANDS ***

  const bit [11:0] UHSII_CMD_IOADR_FULL_RESET         = 12'h200;
  const bit [11:0] UHSII_CMD_IOADR_GO_DORMANT_STATE   = 12'h201;
  const bit [11:0] UHSII_CMD_IOADR_DEVICE_INIT        = 12'h202;
  const bit [11:0] UHSII_CMD_IOADR_ENUMERATE          = 12'h203;
  const bit [11:0] UHSII_CMD_IOADR_TRANS_ABORT        = 12'h204;
  
  // *** PKT TYPES ***
  
  const bit [2:0] PKT_TYPE_CCMD        = 3'b000;
  const bit [2:0] PKT_TYPE_DCMD        = 3'b001;
  const bit [2:0] PKT_TYPE_RES         = 3'b010;
  const bit [2:0] PKT_TYPE_DATA        = 3'b011;
  const bit [2:0] PKT_TYPE_MSG         = 3'b111;

  // *** MSG CATEGORIES AND TYPES ***

  const bit [2:0] MSG_CTG_LMSG         = 3'b000;
  const bit [2:0] MSG_CTG_INT          = 3'b011;
  const bit [2:0] MSG_CTG_AMSG         = 3'b100;

  const bit [3:0] LMSG_IDX_FCREQ       = 4'b0000;
  const bit [3:0] LMSG_IDX_FCRDY       = 4'b0001;
  const bit [3:0] LMSG_IDX_STAT        = 4'b0010;

  const bit [3:0] AMSG_IDX_EBSY        = 4'b0000;

  const bit [2:0] ECODE_COND_ERR       = 3'b001;
  const bit [2:0] ECODE_ARG_ERR        = 3'b010;
  const bit [2:0] ECODE_GEN_ERR        = 3'b011;

endpackage : uhsii_params_pkg
