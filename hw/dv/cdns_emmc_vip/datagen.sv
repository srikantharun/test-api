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
//   Author                : (username)@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                 
//   Pseudo-random data generator
//   
//   File contents  : package datagen_pkg
//                    class   datagen_cl                                   
//------------------------------------------------------------------------------

// timeunit 1ns; timeprecision 100ps;

`include "sv_macros.svh"

package datagen_pkg; 
  import tb_pkg::*;
  import components_pkg::*;

  typedef enum int  {RAND, INCR, PATR} datagen_mode_T;
  
  typedef struct {
    datagen_mode_T  datamode;         // Dategen Operation Mode
  
    int unsigned    lfsr1;            // Linear Feedback Shifting Register 1
    int unsigned    lfsr2;            // Linear Feedback Shifting Register 2
    int unsigned    feed1;            // Feedback LFSR1
    int unsigned    feed2;            // Feedback LFSR2
                                      
    int unsigned    crc;              // CRC calculation reg
    int unsigned    crc_user;         // user data crc
    int unsigned    crcpoly;          // CRC polynomial
    int unsigned    crctopb;          // CRC reg top bit
                                      
    int signed      tcnt;             // transfer length counter
    int signed      bcnt;             // block length counter

    int signed      blklen;           // transfer length counter
    int signed      blkcnt;           // transfer length counter
                                         
    bit[7:0]        pattern[$];       // Pattern Queue
    int             patternptr;       // Pattern Queue Pointer
                                      
    int             wordcnt;          // words counter
    bit[31:0]       word;             // current generate word
                                       
    bit[3:0]        ben;              // byteenable
    
    int             cur_xfer_byte;     //
    
  } datagen_st;

  
  class datagen_cl extends component_cl;
    
    datagen_st st;
    bit debug = 0;
    int iter  = 0;
    int iget  = 0;
    string name;
    
    //-------------------------------------------------------------------
    //constructor
    function new (string _name, component_cl _parent);
      super.new(_name,_parent);
      name = _name;
      st.wordcnt=0;
      st.feed1=32'h800007D8;
      st.feed2=32'h80000E74;
      st.crcpoly=32'hEDB88320;
      st.cur_xfer_byte = 0;
    endfunction : new
  
    //-------------------------------------------------------------------
    //new transfer programmer
    function void new_transfer(input int            _datagenmode,
                               input int            _blkcnt,
                               input int            _blklen,
                               input int            _seed,
                               input logic          [7:0]_pattern[]= '{8'd0});
             
      int result;             
      //check
      assert (_pattern.size>0);
      assert (_blklen>0);
      //assert (_blkcnt>0);
      assert (_seed!=0);
      //program transfer paramteres
      result=$cast(st.datamode, _datagenmode);
      assert(result);
      st.cur_xfer_byte = 0;
      st.blklen        = _blklen;
      st.blkcnt        = _blkcnt;
      st.lfsr1         = _seed;
      st.lfsr2         = _seed;
      st.crc           = 32'hFFFFFFFF;
      st.crc_user      = 32'hFFFFFFFF;
      //inital transfer setup
      if (st.datamode==RAND) 
        repeat (32) st.patternptr+=iterate();  // iterate LFSR registers
        
      st.patternptr = 0;                // reset pattern pointer
      st.ben        = 4'h8;             // reset byteen
      st.bcnt       = _blklen;          // set block counter
      st.tcnt       = _blklen*_blkcnt;  // set transfer counter
      
      if (debug)
        $display ("DATAGEN: %s - new transfer len=%d cnt=%d seeds %08x %08x,",
            name,st.blklen,st.blkcnt,st.lfsr1,st.lfsr2);
      
    endfunction : new_transfer
    
    //-------------------------------------------------------------------
    function bit[31:0] iterate;
      //shift LFSRs
      st.lfsr1 = (st.lfsr1 & 1) ? (st.lfsr1 >> 1) ^ st.feed1 : (st.lfsr1 >> 1);
      st.lfsr2 = (st.lfsr2 & 1) ? (st.lfsr2 >> 1) ^ st.feed2 : (st.lfsr2 >> 1);
      //return xored value
      
      if (debug) $display ("DATAGEN: %s - iterate %d  seeds %08x %08x,",name,iter++,st.lfsr1,st.lfsr2);
      return (st.lfsr1 ^ st.lfsr2);
    endfunction
    
    //-------------------------------------------------------------------
    function void calc_crc(inout bit[31:0] crc, input bit[7:0] value);
      int i;
      crc ^= value;
      for (i=7;i>=0;i--) crc = (crc & 1) ? (crc >> 1) ^ st.crcpoly : (crc >> 1) ;
    endfunction : calc_crc

    //-------------------------------------------------------------------
    function bit[3:0] next_ben (bit[3:0] ben);
       return (ben==4'h1) ? 4'h8 : ben>>1;       //iterate be: 1000->0100->0010->0001->1000...
    endfunction : next_ben
    
    //-------------------------------------------------------------------
    function bit[7:0] get_byte (bit[31:0]data,bit[3:0] ben);
      case (ben)
        4'h1   : return data[31:24];
        4'h2   : return data[23:16];
        4'h4   : return data[15:08];
        4'h8   : return data[07:00];
        default: assert (0) else $fatal(1);
      endcase
      return 8'hxx;
    endfunction : get_byte
    
    //-------------------------------------------------------------------
    // get 8-bit value
    function bit[7:0] get8;
      bit[7:0] val = 8'd0;

      //calculate data in pattern mode
      if (st.datamode==PATR) begin
        val = st.pattern[st.patternptr++];
        if (st.patternptr>st.pattern.size) st.patternptr=0;  //patternptr overload
      end
      //calculate data in incremental mode
      if (st.datamode==INCR) begin
        if (st.ben==4'h8) st.word=st.wordcnt++;              //get new INC mode word 
        st.ben = next_ben(st.ben);                           //iterate be: 1000->0100->0010->0001->1000...
        val = get_byte(st.word,st.ben);                      //select byte
      end                                                    
      //calculate data in random mode                        
      if (st.datamode==RAND) begin                                
        if (st.ben==4'h8) st.word=iterate();                 //get new RND mode word 
        st.ben = next_ben(st.ben);                           //iterate be: 1000->0100->0010->0001->1000...
        val = get_byte(st.word,st.ben);                      //select byte
      end
      //update CRC @every byte
      calc_crc(st.crc,val);
      //decrement length @every byte
      if (st.tcnt>0) st.tcnt--;                              //decrement transfer length
      if (st.bcnt>0) st.bcnt--; else st.bcnt=st.blklen-1;    //decrement block length
      //return calculated value
      if (debug) $display ("DATAGEN: %s - get8 %d  val %02x crc %08x",name,iget++,val,st.crc);
      
      //statistics - current xfer byte
      st.cur_xfer_byte++;
      
      return val;
    endfunction : get8
    
    //-------------------------------------------------------------------
    // get 16-bit value
    function bit[15:0] get16;
      if (debug) $display ("DATAGEN: %s - get16 ",name);
      return {get8,get8};
    endfunction: get16
    
    //-------------------------------------------------------------------
    // get 24-bit value
    function bit[23:0] get24;
      if (debug) $display ("DATAGEN: %s - get24 ",name);
      return {get8,get8,get8};
    endfunction: get24
    
    //-------------------------------------------------------------------
    // get 32-bit value
    function bit[31:0] get32;
      if (debug) $display ("DATAGEN: %s - get32 ",name);
      return {get8,get8,get8,get8};
    endfunction: get32
    
    //-------------------------------------------------------------------
    // check CRC value (if CRC==0 return negated value)
    function bit[31:0] check_crc;
      return (st.crc==0)? ~st.crc : st.crc;
    endfunction : check_crc
    
    //-------------------------------------------------------------------
    // get CRC value (blocking task)
    task get_crc(output bit[31:0] crcresult);
      while (st.tcnt>0) @(st.tcnt);
      crcresult = check_crc();
    endtask : get_crc
    
    //-------------------------------------------------------------------
    // try CRC value (non blocking, return 0 if CRC not ready)
    function bit[31:0] try_get_crc;
        return (st.tcnt>0) ? 32'd0 : check_crc(); // return 0 if CRC not ready
    endfunction : try_get_crc
    
    //-------------------------------------------------------------------
    // get block CRC value (blocking task)
    task get_block_crc(output bit[31:0] crcresult);
      while (st.bcnt>0) @(st.bcnt);                          // wait for block end
      st.bcnt = st.blklen;                                   // reload bcnt to avoid multiple task triggering
      crcresult = check_crc();                               // return CRC value
    endtask : get_block_crc
    
    //-------------------------------------------------------------------
    // try get block CRC value (non blocking, return 0 if CRC not ready)
    function bit[31:0] try_get_block_crc;
        return (st.bcnt>0) ? 32'd0 : check_crc();             // return 0 if CRC not ready
    endfunction : try_get_block_crc
    
    //-------------------------------------------------------------------
    // is block CRC value valid ?
    function bit is_block_crc_valid;
        return (st.bcnt>0) ? `NO : `YES;
    endfunction : is_block_crc_valid
    
    //-------------------------------------------------------------------
    function bit is_active;
      return (st.tcnt>0) ? `YES : `NO;
    endfunction : is_active
 
    //-------------------------------------------------------------------
    // capture randgen state
    function datagen_st get_curr_state;
      return this.st;
    endfunction : get_curr_state
    
    //-------------------------------------------------------------------
    // reset radngen state to prevoius state
    function void reset_transfer_state(datagen_st prev_state);
      this.st = prev_state;
    endfunction : reset_transfer_state

    //-------------------------------------------------------------------
    function void calc_user_crc (bit[7:0] value);
      calc_crc(st.crc_user,value[07:00]);
    endfunction : calc_user_crc

    //-------------------------------------------------------------------
    function void calc_user_crc32 (bit[31:0] value, bit[3:0] be);
      if (be[0]) calc_user_crc(value[07:00]);
      if (be[1]) calc_user_crc(value[15:08]);
      if (be[2]) calc_user_crc(value[23:16]);
      if (be[3]) calc_user_crc(value[31:24]);
    endfunction : calc_user_crc32

    //-------------------------------------------------------------------
    function bit[31:0] get_user_crc();
      return st.crc_user;
    endfunction

    //-------------------------------------------------------------------
    function int get_block_no();
      return st.cur_xfer_byte/st.blklen;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_xfer_byte();
      return st.cur_xfer_byte;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_xfer_word();
      return st.cur_xfer_byte/4;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_xfer_dword();
      return st.cur_xfer_byte/8;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_block_byte();
      return st.cur_xfer_byte%st.blklen;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_block_word();
      return get_block_byte/4;
    endfunction
    
    //-------------------------------------------------------------------
    function int get_block_dword();
      return get_block_byte/8;
    endfunction
    
    //-------------------------------------------------------------------
    function string get_position_byte();
      return $psprintf ("%s, block no %d | block byte:%d word:%d dword:%d | transfer byte %d, word:%d dword:%d ",
             this.name,
             get_block_no(),
             get_block_byte(),get_block_word(), get_block_dword(),
             get_xfer_byte(), get_xfer_word(),  get_xfer_dword()
             );
    endfunction
    //-------------------------------------------------------------------
    function string get_position_word();
      return $psprintf ("%s, block no %d | block word:%d dword:%d | transfer word:%d dword:%d ",
             this.name,
             get_block_no(),
             get_block_word(), get_block_dword(),
             get_xfer_word(),  get_xfer_dword()
             );
    endfunction
    //-------------------------------------------------------------------
    function string get_position_dword();
      return $psprintf ("%s, block no %d | block dword:%d | transfer dword:%d ",
             this.name,
             get_block_no(),
             get_block_dword(),
             get_xfer_dword()
             );
    endfunction
    

  endclass : datagen_cl

endpackage : datagen_pkg

