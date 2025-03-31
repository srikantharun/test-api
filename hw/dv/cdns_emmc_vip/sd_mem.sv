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
//   Memory model
//   
//   File contents  : package sd_mem_pkg;
//                    class   sd_mem_cl                                   
//------------------------------------------------------------------------------

`timescale 1ns / 100ps

`include "card_logging.svh"

package sd_mem_pkg;
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  // ----- MEM BLK CLASS -----

  class mem_blk;
    bit [7:0] data[];

    function string to_string;
      if (this == null)
        return "NULL";
      else
        $swrite(to_string, "mem_blk:{%d bytes of data}", data.size);
    endfunction : to_string
  endclass : mem_blk

  const bit STORE_WRITE_DATA = `TRUE;

  // ----- MEMORY CLASS -----

  class sd_mem_cl extends component_cl;
    local mem_blk array[int unsigned];
    local const int blk_len = 512;

    function new(input string               _name,
                 input component_cl         _parent);
      super.new(_name, _parent);
    endfunction : new

    function void put_mem_blk(mem_blk blk, int unsigned addr);
      if (STORE_WRITE_DATA)
        array[addr] = blk;
    endfunction : put_mem_blk

    function mem_blk get_mem_blk(int unsigned addr);
      if (!array.exists(addr))
        get_mem_blk = new;
      else
        return array[addr];
    endfunction : get_mem_blk

    function void remove_mem_blk(int unsigned addr);
      if (array.exists(addr))
        array.delete(addr);
    endfunction : remove_mem_blk
    
    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    task debug_memory_contents;
      int unsigned addr;
      int unsigned queue[$];
  
      string contents;
      mem_blk blk;
            
      queue = '{};
      addr = 0;
      if (array.exists(addr))
        queue.push_back(addr);
      while (array.next(addr))
        queue.push_back(addr);
  
      $swrite(contents, "----- MEMORY CONTENTS: -----");
      while (queue.size() > 0) begin
        addr = queue.pop_front;
        blk = this.get_mem_blk(addr);
        $swrite(contents, "%s\n    %h :\t", contents, addr);
        for (int i = 0; i < 16 && i < blk.data.size; ++i)
          $swrite(contents, "%s %h", contents, blk.data[i]);
      end
      $swrite(contents,
          "%s\n                             ----------------------------",
          contents);
      `DISPLAY_LOGGER_NOTE(contents);
    endtask : debug_memory_contents
  endclass : sd_mem_cl
endpackage : sd_mem_pkg

