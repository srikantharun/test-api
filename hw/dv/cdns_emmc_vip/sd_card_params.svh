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
//   SD card params included in sd_card_pkg.
//                                                                              
//------------------------------------------------------------------------------

// *** bits in Card Status Reg ***

parameter OUT_OF_RANGE_CSR_BIT        = 31;
parameter ADDRESS_ERROR_CSR_BIT       = 30;
parameter BLOCK_LEN_ERROR_CSR_BIT     = 29;
parameter ERASE_SEQ_ERROR_CSR_BIT     = 28;
parameter ERASE_PARAM_CSR_BIT         = 27;
parameter WP_VIOLATION_CSR_BIT        = 26;
parameter CARD_IS_LOCKED_CSR_BIT      = 25;
parameter LOCK_UNLOCK_FAILED_CSR_BIT  = 24;
parameter COM_CRC_ERROR_CSR_BIT       = 23;
parameter ILLEGAL_COMMAND_CSR_BIT     = 22;
parameter CARD_ECC_FAILED_CSR_BIT     = 21;
parameter CC_ERROR_CSR_BIT            = 20;
parameter ERROR_CSR_BIT               = 19;
parameter CSD_OVERWRITE_CSR_BIT       = 16;
parameter WP_ERASE_SKIP_CSR_BIT       = 15;
parameter CARD_ECC_DISABLED_CSR_BIT   = 14;
parameter ERASE_RESET_CSR_BIT         = 13;
parameter READY_FOR_DATA_CSR_BIT      = 8;
parameter APP_CMD_CSR_BIT             = 5;
parameter AKE_SEQ_ERROR_CSR_BIT       = 3;

// *** bits in Card-Specyfic Data reg ***

parameter WRITE_BLK_MISALIGN_CSD_BIT = 78;
parameter READ_BLK_MISALIGN_CSD_BIT  = 77;

// *** timing values ***

parameter N_CR     =  2;
parameter N_ID     =  5;
parameter N_AC     =  2;
parameter N_RC     =  8;
parameter N_CC     =  8;
parameter N_WR     =  2;
parameter N_SD     =  2;
parameter N_SB     =  2;
parameter N_SB_RD  =  1;
parameter N_SB_WR  =  4;

// *** bits in SDIO R5 flags ***

const int COM_CRC_ERROR_SDIO_FLAG = 7;
const int ILLEGAL_COMMAND_SDIO_FLAG = 6;
const int ERROR_SDIO_FLAG = 3;
const int FUNCTION_NUMBER_SDIO_FLAG = 1;
const int OUT_OF_RANGE_SDIO_FLAG = 0;
