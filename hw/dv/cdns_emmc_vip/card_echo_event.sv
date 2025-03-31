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
//   Packages and classes used for reporting events recorded by SD card.        
//                                                                              
//   File contents  : package card_echo_event_pkg
//                    class   card_echo_event_cl
//                    class   sd_echo_event_cl
//                    class   uhsii_echo_event_cl
//                    class   data_echo_event_cl
//------------------------------------------------------------------------------

package card_echo_event_pkg;

  import sd_tok_pkg::*;
  import uhsii_pkt_pkg::*;

  typedef enum {
    SD_ECHO_EVENT,
    UHSII_ECHO_EVENT,
    DATA_ECHO_EVENT
  } echo_event_e;

  typedef enum bit [3:0] {
    // card identification mode:
    IDLE_ST,      // idle state
    READY_ST,     // ready state
    IDENT_ST,     // identification state

    // data transfer mode:
    STBY_ST,      // stand-by state
    TRAN_ST,      // transfer state
    DATA_ST,      // sending data state
    RCV_ST,       // receiving data state
    PRG_ST,       // programming state
    DIS_ST,       // disconnect state

    // other modes:
    PREBTST_ST,   // (eMMC only)
    BTST_ST,      // (eMMC only)
    SLP_ST,       // (eMMC only)
    IRQ_ST,       // (eMMC only)

    INA_ST,       // inactive state

    PREIDLE_ST    // (eMMC only)
  } card_st_e;

  function static bit is_card_ident_mode(card_st_e card_st);
    return (card_st inside {IDLE_ST, READY_ST, IDENT_ST, PREIDLE_ST, PREBTST_ST, INA_ST});
  endfunction : is_card_ident_mode
  
  function static bit is_card_selected(card_st_e card_st);
    return (card_st inside {TRAN_ST, DATA_ST, RCV_ST, PRG_ST});
  endfunction : is_card_selected

  typedef enum bit [3:0] {
    SDIO_IDLE_ST = 4'b0000, // after reset, before CMD5
    SDIO_RDY_ST  = 4'b1100, // after CMD5 accepted
    SDIO_STBY_ST = 4'b0100, // after CMD3 accepted
    SDIO_INA_ST  = 4'b1000, // inactive state
    SDIO_CMD_ST  = 4'b0001, // active, data bus free
    SDIO_TRN_ST  = 4'b0010  // active, data transf ongoing
  } sdio_st_e;
  
  function static sdio_st_e translate_state (card_st_e card_st);
    case (card_st)
      IDLE_ST:                    translate_state = SDIO_IDLE_ST;
      READY_ST, IDENT_ST:         translate_state = SDIO_RDY_ST;
      STBY_ST:                    translate_state = SDIO_STBY_ST;
      TRAN_ST:                    translate_state = SDIO_CMD_ST;
      DATA_ST, RCV_ST, PRG_ST:    translate_state = SDIO_TRN_ST;
      default:                    translate_state = SDIO_INA_ST;
    endcase
  endfunction : translate_state

  `include "sv_macros.svh"

  // ---------------------------------------------------------------------- //

  virtual class card_echo_event_cl;
    protected echo_event_e echo_event_type;

    function new(echo_event_e echo_event_type);
      this.echo_event_type = echo_event_type;
    endfunction : new

    function echo_event_e get_echo_event_type;
      return this.echo_event_type;
    endfunction : get_echo_event_type

    virtual function string to_string;
      $swrite(to_string, "{card_echo_event type: %s}",
        this.echo_event_type.name());
    endfunction : to_string
  endclass : card_echo_event_cl

  // ---------------------------------------------------------------------- //

  class sd_echo_event_cl extends card_echo_event_cl;
    sd_cmd    scmd;
    sd_rsp    srsp;
    card_st_e state;
    bit       uhsii;
    
    function new(sd_cmd scmd, sd_rsp srsp, card_st_e state, bit uhsii);
      super.new(SD_ECHO_EVENT);
      this.scmd   = scmd;
      this.srsp   = srsp;
      this.state  = state;
      this.uhsii  = uhsii;
    endfunction : new    

    virtual function string to_string;
      if (this == null) return "NULL";
      $swrite(to_string, "{%s: %s; %s%s st:%s}",
        this.echo_event_type.name(),
        this.scmd.to_string,
        this.srsp == null ? "no RSP" : this.srsp.to_string,
        this.uhsii ? " (UHS-II)" : "",
        this.state.name);
    endfunction : to_string
  endclass : sd_echo_event_cl

  // ---------------------------------------------------------------------- //

  class uhsii_echo_event_cl extends card_echo_event_cl;
    uhsii_pkt ucmd;
    uhsii_pkt ures;

    function new(uhsii_pkt cmd, uhsii_pkt res);
      super.new(UHSII_ECHO_EVENT);
      this.ucmd = cmd;
      this.ures = res;
    endfunction : new

    virtual function string to_string;
      if (this == null) return "NULL";
      $swrite(to_string, "{%s: %s; %s}", this.echo_event_type.name(),
        this.ucmd.to_string, this.ures.to_string);
    endfunction : to_string
  endclass : uhsii_echo_event_cl

  // ---------------------------------------------------------------------- //

  class data_echo_event_cl extends card_echo_event_cl;
    bit rw;                     // 1 = write, 0 = read data
    int length;                 // length of data block
    bit crc_err;                // CRC check result: 0 = OK, 1 = error

    bit datagen_mode;           // 1 = datagen is used
    bit data_correct;           // 1 = data with no error, valid iff datagen_mode=1 & rw=1
    int unsigned first_error;   // index of first error byte;
                                // valid iff datagen_mode=1 & data_correct=0 & rw=1
    int unsigned data_checksum; // 32-bit checksum calculated for the data stream

    function new(bit rw, int length);
      super.new(DATA_ECHO_EVENT);
      this.rw       = rw;
      this.length   = length;

      this.crc_err  = `FALSE;
      this.datagen_mode = `FALSE;
      this.data_correct = `FALSE;
      this.first_error  = -1;
    endfunction : new
    
    virtual function string to_string;
      if (this == null) return "NULL";
      $swrite(to_string, "{%s: %s length=%d crc=%s",
        this.echo_event_type.name(),
        this.rw ? "write" : "read",
        this.length,
        this.crc_err ? "ERR" : "OK");
      if (this.datagen_mode) begin
        $swrite(to_string, "%s datagen=%s", to_string, this.datagen_mode ? "yes" : "no");
        if (this.datagen_mode && this.rw) begin
          $swrite(to_string, "%s data_correct=%s",
            to_string, this.data_correct ? "yes" : "no");
          if (!this.data_correct)
            $swrite(to_string, "%s first_error=%d", to_string, this.first_error);
        end
        $swrite(to_string, "%s checksum=%h", to_string, this.data_checksum);
      end
      $swrite(to_string, "%s}", to_string);
    endfunction : to_string
  endclass : data_echo_event_cl

  // ---------------------------------------------------------------------- //
  
endpackage : card_echo_event_pkg

