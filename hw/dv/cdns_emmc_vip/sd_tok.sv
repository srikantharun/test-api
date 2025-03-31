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
//   legacy SD packets
//   
//   File contents  : package sd_tok_pkg
//                    class   sd_tok
//                    class   sd_cmd
//                    class   sd_dat
//                    class   sd_meta                                   
//------------------------------------------------------------------------------

`ifndef UVM
`include "sv_macros.svh"
`endif
`define DATA_INTEGRITY_CHECK_DEBUG2

package sd_tok_pkg;
  `ifndef UVM
  typedef enum byte {
      L1 = 1, L4 = 4, L8 = 8, LERR = 0
  } bus_width_e;
  `endif

  typedef enum bit [2:0] {
    CMD, DAT_RD, DAT_WR, META, RSP
  } sd_token_e;

  typedef enum bit [3:0] {
    NONE_RSP,                          // no response (might indicate cmd error)
    R1, R1B, R2, R3, R4, R5, R6, R7,   // standard response types
    EMPTY_RSP                          // empty response used in UHS-II SD-TRAN
  } sd_rsp_e;

  `ifndef UVM
  typedef enum bit [3:0] {
    IDENT_SPEED,
    DEFAULT_SPEED,
    HIGH_SPEED,
    SDR12,
    SDR25,
    SDR50,
    SDR104,
    DDR50,
    DEFAULT_EMMC,
    SDR_EMMC,
    DDR_EMMC,
    HS200_EMMC,
    HS400_EMMC
  } bus_speed_e;

    function static bit uses_ddr(bus_speed_e bus_speed);
      return bus_speed == DDR50 || bus_speed == DDR_EMMC || bus_speed == HS400_EMMC;
      return (bus_speed inside {DDR50, DDR_EMMC, HS400_EMMC});
    endfunction : uses_ddr

    function static bit uses_fast(bus_speed_e bus_speed);
      return bus_speed == SDR50 || bus_speed == DDR50 || uses_fastest(bus_speed);
      return (bus_speed inside {SDR50, DDR50}) || uses_fastest(bus_speed);
    endfunction : uses_fast

    function static bit uses_fastest(bus_speed_e bus_speed);
      return (bus_speed inside {SDR104, HS200_EMMC, HS400_EMMC});
    endfunction : uses_fastest
    
    function static bit uses_emmc(bus_speed_e bus_speed);
      return (bus_speed inside {DEFAULT_EMMC, SDR_EMMC, DDR_EMMC, HS200_EMMC, HS400_EMMC});
    endfunction : uses_emmc
    
    
    function static int min_clock_period_in_ns(bus_speed_e bus_speed);
      case (bus_speed)
        IDENT_SPEED:             return  2500;
        DEFAULT_SPEED:           return  40;
        HIGH_SPEED:              return  20;
        SDR12:                   return  40;
        SDR25, DDR50:            return  20;
        SDR50:                   return  10;
        SDR104:                  return  5;
        
        DEFAULT_EMMC:            return  40;
        SDR_EMMC, DDR_EMMC:      return  20;
        HS200_EMMC, HS400_EMMC:  return  5;
        default:                 return  10;
      endcase
    endfunction
  `endif

  virtual class sd_tok;
    const sd_token_e tok_kind;
    bit              crc_err;

    function new(sd_token_e tok_kind);
      this.tok_kind = tok_kind;
    endfunction : new

    virtual function string to_string;
      if (this == null)
        return "NULL";
      else
        $swrite(to_string, "sd_tok: %s", tok_kind.name);
    endfunction : to_string
  endclass : sd_tok

  // ---------------------------------------------------------------------- //

  class sd_cmd extends sd_tok;
    bit             app;              // app cmd
    bit [5:0]       index;            // cmd index
    bit [31:0]      arg;              // cmd arg
    bit             cancel_transf;    // cancel transfer request
    bit             power_cycle;      // reset request

    bit             init_boot;        // boot initiation request
    bit             stop_boot;        // boot termination request

    function new();
      super.new(CMD);
    endfunction : new

    virtual function string to_string;
      if (this == null)
        return "NULL";
      else if (this.power_cycle | this.cancel_transf | this.init_boot | this.stop_boot)
        return $sformatf("SD CMD [%0s]", this.power_cycle   ? "power cycle req" :
                                         this.cancel_transf ? "cancel transf"   :
                                         this.init_boot     ? "init boot"       :
                                         this.stop_boot     ? "stop boot"       : "");
      else
        return $sformatf("SD CMD=%s%2d arg=%h crc_err=%b",
            this.app ? "A" : " ", this.index, this.arg, this.crc_err);
    endfunction : to_string
  endclass : sd_cmd

  // ---------------------------------------------------------------------- //

  class sd_rsp extends sd_tok;
    sd_rsp_e        rsp_kind;
    bit [5:0]       index;
    bit [31:0]      contents[];

    // meta info for XTOR:
    int delay_cycles;   // number of cycles; if 0, to be randomized
    bit switch2volt18;  // switch to 1.8V sequence
    int wr_dat_blklen;  // set to non-zero only when write data transfer is about to begin

    function new(sd_rsp_e rsp_kind);
      super.new(RSP);
      this.rsp_kind = rsp_kind;
      this.contents = new[rsp_kind == R2                                 ? 4 :
                         (rsp_kind == EMPTY_RSP || rsp_kind == NONE_RSP) ? 0 : 1];
      this.wr_dat_blklen = -1;
      this.delay_cycles  =  0;
    endfunction : new

    virtual function string to_string;
      if (this == null)
        return "NULL";
      else if (rsp_kind == NONE_RSP)
        return "SD RSP none";
      else if (rsp_kind == EMPTY_RSP)
        return "SD RSP empty";
      else if (rsp_kind == R2)
        return $sformatf("SD RSP (%s) index=%2d contents=%h",
            this.rsp_kind.name, this.index,
           {this.contents[0],   this.contents[1],
            this.contents[2],   this.contents[3]});
      else
        return $sformatf("SD RSP (%s) index=%2d contents=%h%s",
            this.rsp_kind.name, this.index, this.contents[0],
            wr_dat_blklen > -1 ? $sformatf(" wr_dat_blklen=%0d", this.wr_dat_blklen) : "");
    endfunction : to_string
   
    `ifndef UVM
    function void randomize_delay(bus_speed_e bus_speed);
      if (this.delay_cycles > 0) return;
      // N_CR timing
      this.delay_cycles = $urandom_range(uses_fastest(bus_speed) ? 62 : 64, 2); // shouldn't be 61 for fastest?
    endfunction : randomize_delay
    `endif
    
    function bit check_response_error_flag;
      case (rsp_kind)
        R1:
          return contents[0][19] | contents[0][20] | contents[0][21] |
                 contents[0][23] /* 24 or 25 ? */  | contents[0][26] |
                 contents[0][29] | contents[0][30] | contents[0][31] ;
        R5:
          return contents[0][8]  | contents[0][9]  |
                 contents[0][11] | contents[0][15] ;
        default:
          return `FALSE;
      endcase
    endfunction : check_response_error_flag
  endclass : sd_rsp

  // ---------------------------------------------------------------------- //

  class sd_dat extends sd_tok;
    byte        lines;          // number of DAT lines to send/receive data (1, 4 or 8)
    bit [7:0]   data[];         // if empty, only meta data are valid
    bit         token;          // no data, send CRC status token only
    bit         crc_err;        // whether data contains CRC error; if token==1,
                                // CRC status token: 1 -> 101 (error), 0 -> 010 (correct)

    int         delay_cycles;   // number of cycles; if 0, to be randomized
    bit         tuning_block;   // if 1, it is a special block with tuning data
    bit         wr_dat_end;     // cancel ongoing write data transfer
    bit         busy;           // line state after data bulk/status token transmission
    bit         change_speed;   // bus speed change flag
    `ifndef UVM
    bus_speed_e new_speed;      // new bus speed (valid onlu if change_speed=1)
    bus_width_e new_width;      // set to value different than LERR only when data bus width is to be changed
    `endif

    function new(bit meta, bit rw, byte lines);
      super.new(meta ? META : rw ? DAT_WR : DAT_RD);
      this.lines = lines;
      `ifndef UVM
      this.new_width = LERR;
      `endif
      if (meta) this.data = new[0];
    endfunction : new

    virtual function string to_string;
      if (this == null)
        return "NULL";
      $swrite(to_string, "SD DAT %s length=%3d crc_err=%b busy=%b",
        this.lines == 4 ? "L4" : this.lines == 8 ? "L8" : "L1",
        this.data.size, this.crc_err, this.busy);
    `ifdef DATA_INTEGRITY_CHECK_DEBUG2
      if (this.tok_kind == DAT_WR || this.tok_kind == DAT_RD)
        for (int i = 0; i < this.data.size && i < 16; ++i)
          $swrite(to_string, "%s %h", to_string, this.data[i]);
    `endif // DATA_INTEGRITY_CHECK_DEBUG2
    endfunction : to_string
    
    local static int seed = 1;

    `ifndef UVM
    function void randomize_delay(bus_speed_e bus_speed);
      if (this.delay_cycles > 0) return;
      if (this.token) begin
        // N_CRC timing:
        this.delay_cycles = uses_fastest(bus_speed) ? $urandom_range(6, 2) :
                            uses_fast(bus_speed)    ? $urandom_range(8, 2) : 2;
      end
      else begin
        // N_AC timing:
        this.delay_cycles = $urandom_range(72, uses_fast(bus_speed) ? 8 : 2);
        if (!$urandom_range(6))
          this.delay_cycles += $dist_exponential(seed, 100);
        while (this.delay_cycles > 999) // max value
          this.delay_cycles /= $urandom_range(11, 2);
      end
    endfunction : randomize_delay
    `endif
  endclass : sd_dat

  // ---------------------------------------------------------------------- //

  `ifndef UVM
  class sd_meta extends sd_dat;
    
    function new;
      super.new(`TRUE, `FALSE, `FALSE);
    endfunction

    virtual function string to_string;
      if (this == null)
        return "NULL";
      else
        $swrite(to_string, "SD META token=%b crc_err=%b busy=%b %s %s %s",
          this.token, this.crc_err, this.busy,
          this.change_speed ?
            $sformatf("new_speed=%s", this.new_speed.name) : "",
          this.new_width != LERR ?
            $sformatf("new_width=%s", this.new_width.name) : "",
          this.wr_dat_end ?
            "wr_dat_end" : "");
    endfunction : to_string
  endclass : sd_meta
  `endif

endpackage : sd_tok_pkg
