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
//   SDIO card model                                                            
//   
//   File contents  : package sdio_card_pkg
//                    class   sdio_card_cl                                     
//------------------------------------------------------------------------------

`timescale 1 ns / 100 ps

package sdio_card_pkg;
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import sd_tok_pkg::*;
  import sd_card_pkg::*;
  import card_echo_event_pkg::*;
  import sd_mem_pkg::*;
  import datagen_pkg::*;

`include "sv_macros.svh"
`include "sd_card_params.svh"

  typedef class sdio_card_cl;

  typedef enum bit {
    FIXED_ADDR = `LOW,
    INCR_ADDR = `HIGH
  } opcode_e;
  
  typedef bit [16:0] sdio_addr_t;
  typedef bit [7:0]  byte_t;
  typedef byte_t fifo_reg_t[$] ;
  
  // ----- SDIO CARD REGISTERS CLASS ----- //
  
  /*
  this wrapper class is needed so that arrays implementing the registers
  are not copied by value (a reference to the class can be used instead)
  */
  
  class sdio_regs_cl;

    local byte_t             cia_sdio_reg[sdio_addr_t];
    local fifo_reg_t         func_sdio_reg[1:7][sdio_addr_t];

    const bit [2:0]          func_num;
    
    local sdio_card_cl       card;

    local int unsigned       wait_units;
    
    function new (sdio_card_cl card, bit [2:0] func_num, int unsigned wait_units);
      this.card       = card;
      this.func_num   = func_num;
      this.wait_units = wait_units;
    endfunction : new

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    task fill_up;
      cia_sdio_reg.delete;
      foreach (func_sdio_reg[i])
        func_sdio_reg[i].delete;

      // generate CCCR:
      cia_sdio_reg[17'h00000] = 8'h54; // SDIO + CCCR version
      cia_sdio_reg[17'h00001] = 8'h04; // SD Phy Layer version
      cia_sdio_reg[17'h00008] = 8'h13; // S4MI, SMB, SDC, default:0
      cia_sdio_reg[17'h0000A] = 8'h10; // CIS pointer (MID)
      cia_sdio_reg[17'h00013] = 8'h01; // SHS, default:0
      cia_sdio_reg[17'h00014] = 8'h07; // support for bus speeds
      
      cia_sdio_reg[17'h00004] = 8'hFF; // int ena (temp)

      // function ready:
      fork
        fork
          begin
            byte_t tmp = 8'h00;
            for (int i = 1; func_num >= i; ++i)
              tmp[i] = `HIGH;
            #((wait_units % 20 + 1) * 1us);
            cia_sdio_reg[17'h00003] = tmp;
            `DISPLAY_LOGGER_NOTE($sformatf("SDIO F ON  f%1d/%05h : %02h", 3'd0, 17'h00003, tmp))
          end
        join_none
      join
      // ... rest is filled with zeros ... //
      
      // generate FBRs:
      for (int unsigned i = 1; func_num >= i; i++) begin
        cia_sdio_reg[{5'd0, i[3:0], 8'h0A}] = {4'h1, i[3:0]}; // CIS pointer (MID)
        // ... the rest is filled with zeros ... //
      end
    endtask : fill_up

    //------------------------------------------------------------------------
    //                  SDIO-specyfic registers accesses
    //------------------------------------------------------------------------

    function byte_t read(bit [2:0] func, sdio_addr_t addr, bit display = `TRUE);
      byte_t val = 8'h00;
      case (func)
        3'd0:
          if (cia_sdio_reg.exists(addr))
            val = cia_sdio_reg[addr];
        default:
          if (func_sdio_reg[func].exists(addr)) begin
            if (func_sdio_reg[func][addr].size >  0)
              val = func_sdio_reg[func][addr].pop_front;
            if (func_sdio_reg[func][addr].size == 0)
              func_sdio_reg[func].delete(addr);
          end
      endcase
      if (display)
        `DISPLAY_LOGGER_NOTE($sformatf("SDIO READ  f%1d/%05h : %02h", func, addr, val))
      return val;
    endfunction : read
    
    task write(bit [2:0] func, sdio_addr_t addr, byte_t val, bit display = `TRUE);
      if (display)
        `DISPLAY_LOGGER_NOTE($sformatf("SDIO WRITE f%1d/%05h : %02h", func, addr, val))
      case (func)
        3'd0:
          if (addr == 17'h00006)
            card.sdio_execute_reset_or_abort(val[3:0]);
          else begin
            if (val == 8'h00)
              cia_sdio_reg.delete(addr);
            else
              cia_sdio_reg[addr] = val;
          end
        default:
          if (func_sdio_reg[func].exists(addr))
            func_sdio_reg[func][addr].push_back(val);
          else
            func_sdio_reg[func][addr] = '{val};
      endcase
      
      if (func == 3'd0)
        case (addr)
          17'h00007,
          17'h00013: begin
            cia_sdio_reg[17'h00013][0] = `TRUE; // RO SHS !
            card.sdio_pass_bus_info_to_xtor; // bus width and/or speed changed
          end
          17'h00004,
          17'h00005:
            card.sdio_update_intr_signal;
        endcase
    endtask : write
    
    function byte_t peek(bit [2:0] func, sdio_addr_t addr, bit display = `TRUE);
      byte_t val = 8'h00;
      case (func)
        3'd0:
          if (cia_sdio_reg.exists(addr))
            val = cia_sdio_reg[addr];
        default:
          if (func_sdio_reg[func].exists(addr) && 
              func_sdio_reg[func][addr].size > 0)
            val = func_sdio_reg[func][addr][0];
      endcase
      if (display)
        `DISPLAY_LOGGER_NOTE($sformatf("SDIO PEEK  f%1d/%05h : %02h", func, addr, val))
      return val;
    endfunction : peek
    
    function bit [2:0] get_sdio_bus_speed;
      return cia_sdio_reg[17'h00013][3:1];
    endfunction : get_sdio_bus_speed

    function bit [1:0] get_sdio_bus_width;
      return cia_sdio_reg[17'h00007][1:0];
    endfunction : get_sdio_bus_width
  endclass : sdio_regs_cl
  
  // ----- SDIO DATA TRANSFER CLASS ----- //
  
  class sdio_transf_cl extends sd_transf_cl;
    local sdio_regs_cl   regs;
    local bit [2:0]      func;
    local opcode_e       opcode;
    local bit            align;
    
    function new ( input bit [16:0]       addr,
                   input bit [2:0]        func,
                   input sdio_regs_cl     regs,
                   input capacity_e       card_cap,
                   input int unsigned     block_length,
                   input int unsigned     block_count,
                   input oper_e           oper,
                   input opcode_e         opcode,
                   input bit              uhsii_based,
                   input bit              align
                 , input datagen_cl       datagen = null
                 );
      super.new(addr, card_cap, null, block_length, block_count, oper, `TRUE, uhsii_based, datagen);
      this.regs   = regs;
      this.func   = func;      
      this.opcode = opcode;
      
      this.max_addr= {15'h7FFF,
                      17'h1FFFF};
      
      if (opcode == FIXED_ADDR) begin
        // in transfer with fixed address 'curr_addr' is used as a simple
        // counter instead of being a real pointer to the current address;
        // 'end_addr' stores the transfer length in bytes
        this.curr_addr = 0;
        this.end_addr  = block_length * block_count;
      end
      else
        // at the beginning of a transfer: curr_addr = start_addr by default
        this.end_addr = this.start_addr + block_length * block_count;
        this.align = align;
    endfunction : new

    // ----- ----- -----

    virtual function string to_string;
      return $sformatf(
          "SDIO %s %s F%0d data transf start_addr=%0h curr_addr=%0h end_addr=%0h blklen=%0d blknum=%0d",
              this.oper.name, this.opcode.name, this.func,
              this.start_addr[16:0], this.curr_addr[16:0], this.end_addr[16:0],
              this.blklen, this.blknum);
    endfunction : to_string

    // ----- ----- -----

    virtual function bit has_next_blk;
      return this.curr_addr < this.end_addr || this.blknum == 0;
    endfunction : has_next_blk
    
    // ----- ----- -----
    
    local function void check_range;
      case (this.opcode)
        INCR_ADDR:
          if (this.curr_addr + this.blklen > this.max_addr)
            this.out_of_range = `TRUE;
        FIXED_ADDR:
          if (this.start_addr > this.max_addr)
            this.out_of_range = `TRUE;
      endcase
    endfunction : check_range
    
    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    virtual function byte_array read_curr_blk;
      int i = 0;
      bit [7:0] data[] = new [this.blklen];

      `DISPLAY_LOGGER_MSG(this.opcode == INCR_ADDR ?
        $sformatf("IO read from F%1d INCR addr=%5h", func, curr_addr) :
        $sformatf("IO read from F%1d FIXD addr=%5h np=%8h", func, start_addr, curr_addr))

      if (this.datagen_mode)
        while (i < data.size) begin
          data[i++] = datagen.get8;
          this.curr_addr++;
        end
      else
        case (this.opcode)
          INCR_ADDR:
            while (i < data.size)
              data[i++] = regs.read(this.func, this.curr_addr++, `FALSE);
          FIXED_ADDR:
            while (i < data.size) begin
              data[i++] = regs.read(this.func, this.start_addr, `FALSE);
              this.curr_addr++;
            end
        endcase
      check_range;
      return data;
    endfunction : read_curr_blk

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
    
    virtual task write_curr_blk(const ref bit [7:0] data[]);
      int i = 0;
      
      `DISPLAY_LOGGER_MSG(this.opcode == INCR_ADDR ?
        $sformatf("IO write to F%1d INCR addr=%5h", func, curr_addr) :
        $sformatf("IO write to F%1d FIXD addr=%5h np=%8h", func, start_addr, curr_addr))

      if (this.datagen_mode || func == 0)
        this.curr_addr += data.size;
      else
        case (this.opcode)
          INCR_ADDR:
            while (i < data.size)
              regs.write(this.func, this.curr_addr++, data[i++], `FALSE);
          FIXED_ADDR:
            while (i < data.size) begin
              regs.write(this.func, this.start_addr, data[i++], `FALSE);
              this.curr_addr++;
            end
        endcase
      check_range;
    endtask : write_curr_blk

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    // function returns 1 if we have to wait with the data output
    // (special SDIO-only multi-block read timing)
    virtual function bit check_rsp_aligned;
      return  this.oper == READ_OPER && align &&
              // for the first block in the transfer only:
              this.curr_addr == (this.opcode == FIXED_ADDR ? 0 : this.start_addr) + this.blklen;
    endfunction : check_rsp_aligned
  endclass : sdio_transf_cl

  // *************************************************************************
  // ~~~~~~~~~~~~~~~~~~~~~~~~~~~ SDIO CARD CLASS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // *************************************************************************
  
  class sdio_card_cl extends sd_card_cl;

    local mailbox #(bit)     mbx_intr;
    local bit                lvs;
  
    local bit                mem_present;

    local sdio_st_e          sdio_st;
    
    local sdio_regs_cl       sdio_regs;
    
    local bit [7:0]          sdio_flags;

    local bit [31:0]         ocr_reg_sdio;

    local semaphore          voltage_init_sdio;

    local process            volt_init_sdio_th_obj;
    local process            int_sched_sdio_th_obj;

    //------------------------------------------------------------------------
    //                      SDIO CARD MODEL CONSTRUCTOR
    //------------------------------------------------------------------------
    function new(input string             _name,
                 input component_cl       _parent,
                 input mailbox #(sd_cmd)  mbx_cmd,
                 input mailbox #(sd_rsp)  mbx_rsp,
                 input mailbox #(sd_dat)  mbx_dat_rd,
                 input mailbox #(sd_dat)  mbx_dat_wr,
                 input mailbox #(bit)     mbx_intr,
                 input mailbox #(bit)     mbx_lvs,
                 input legacy_config_cl   card_config,
                 input sd_mem_cl          data_mem,
                 input bit                uhsii_based,
                 input bit                mem_present,
                 input bit                use_datagen);
      super.new(_name, _parent, mbx_cmd, mbx_rsp, mbx_dat_rd, mbx_dat_wr, mbx_lvs,
                card_config, data_mem, uhsii_based, use_datagen);
      this.mbx_intr    = mbx_intr;
      this.mbx_lvs     = mbx_lvs;
      this.mem_present = mem_present;
      this.sdio_regs   = new (this, 3'd7, this.wait_units);
      if (card_config == null)
        this.card_config = new(SDSC, legacy_config_cl::random_ocr_sdio());
      if (~ this.mem_present) this.data_mem = null;
    endfunction : new

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `ifdef USE_LOGGERS
      this.sdio_regs.init_logging(logger, log_id, this.get_hier_name);
    `endif // USE_LOGGERS
    `INIT_LOGGING_SUBCOMPS_END

    virtual function string get_class_name;
      return "sdio_card_cl";
    endfunction : get_class_name

    virtual function void dispose;
      int z = 0;
      if (data_th_obj != null) begin
        data_th_obj.kill;
        data_th_obj = null;
        ++z;
      end
      if (rcv_th_obj != null) begin
        rcv_th_obj.kill;
        rcv_th_obj = null;
        ++z;        
      end
      if (prg_th_obj != null) begin
        prg_th_obj.kill;
        prg_th_obj = null;
        ++z;
      end
      if (main_th_obj != null) begin
        main_th_obj.kill;
        main_th_obj = null;
        ++z;
      end
      if (select_th_obj != null) begin
        select_th_obj.kill;
        select_th_obj = null;
        ++z;
      end
      if (volt_init_th_obj != null) begin
        volt_init_th_obj.kill;
        volt_init_th_obj = null;
        ++z;
      end
      if (bus_speed_th_obj != null) begin
        bus_speed_th_obj.kill;
        bus_speed_th_obj = null;
        ++z;
      end
      if (misc_th_obj != null) begin
        misc_th_obj.kill;
        misc_th_obj = null;
        ++z;
      end
      if (volt_init_sdio_th_obj != null) begin
        volt_init_sdio_th_obj.kill;
        volt_init_sdio_th_obj = null;
        ++z;
      end
      if (int_sched_sdio_th_obj != null) begin
        int_sched_sdio_th_obj.kill;
        int_sched_sdio_th_obj = null;
        ++z;
      end

      `DISPLAY_LOGGER_NOTE($sformatf("card disposed ... %0d thread(s) killed", z))
    endfunction : dispose
    
    //////////////////////////////////////////////////////////////////////////
    
    //------------------------------------------------------------------------
    //                      various overloaded methods
    //------------------------------------------------------------------------
    
    protected virtual function void change_state_sdio(sdio_st_e new_st);
    `ifdef USE_LOGGERS
      `DISPLAY_LOGGER_INFO($sformatf(
          "SDIO card state changed from <i>%s</i> to <b>%s</b>",
          sdio_st.name, new_st.name))
    `else // USE_LOGGERS
      `DISPLAY_LOGGER_INFO($sformatf(
          "SDIO card state changed from %s to %s",
          sdio_st.name, new_st.name))
    `endif // !USE_LOGGERS
      sdio_st = new_st;
    endfunction : change_state_sdio
    
    protected virtual function void go_to_previous_state(sd_rsp_e rsp_kind, card_st_e prev_st);
      card_st_e tmp_st = card_st;
      super.go_to_previous_state(rsp_kind, prev_st);
      if (card_st != tmp_st) begin
        // i.e. card state change did happen and was backouted:
        sdio_st = translate_state(card_st);
      `ifdef USE_LOGGERS
        `DISPLAY_LOGGER_INFO($sformatf("Going back also to <b>%s</b>", sdio_st.name))
      `else // USE_LOGGERS
        `DISPLAY_LOGGER_INFO($sformatf("Going back also to <b>%s</b>", sdio_st.name))
      `endif // !USE_LOGGERS
      end      
    endfunction : go_to_previous_state   
    
    local task internal_reset_sdio(bit volt_back = `TRUE);
      change_state_sdio(SDIO_IDLE_ST);
      voltage_init_sdio =  new(1);
      if (this.uhsii_based || volt_back)
        ocr_reg_sdio = {8'h00, this.card_config.voltage_window};

      if (volt_init_sdio_th_obj != null) begin
        volt_init_sdio_th_obj.kill;
        volt_init_sdio_th_obj = null;
        `DISPLAY_LOGGER_NOTE("volt_init_sdio_th_obj killed")
      end
      if (int_sched_sdio_th_obj != null) begin
        int_sched_sdio_th_obj.kill;
        int_sched_sdio_th_obj = null;
        `DISPLAY_LOGGER_NOTE("int_sched_sdio_th_obj killed")
      end
      
      if (~this.mem_present) begin
        reset_bus_if;
        data_transf = null;
      end

      this.sdio_regs.fill_up;
      begin
        bit tmp;
        while (this.mbx_intr.try_get(tmp));
        this.sdio_update_intr_signal;
      end      
    endtask : internal_reset_sdio
    
    protected virtual task internal_reset(bit volt_back = `TRUE);
      this.internal_reset_sdio(volt_back);
      super.internal_reset(volt_back);
    endtask : internal_reset
    
    virtual protected function void check_and_set_illegal_command_bit_status;
      csr_reg[ILLEGAL_COMMAND_SDIO_FLAG] = illegal_cmd;
    endfunction : check_and_set_illegal_command_bit_status

    protected virtual task set_register_values;
      super.set_register_values;
      this.sdio_regs.fill_up;
    endtask : set_register_values

    protected virtual function void inappropriate_state;
      `DISPLAY_LOGGER_WARNING($sformatf(
          "%sCMD%0d is illegal in the current state: %s+%s",
          (last_cmd.app || go_for_acmd) ? "A" : " ",
          last_cmd.index, card_st.name, sdio_st.name))
      illegal_cmd = `TRUE;
    endfunction : inappropriate_state
    
    protected virtual function void operation_compl;
      super.operation_compl;
      if (sdio_st == SDIO_TRN_ST)
        change_state_sdio(SDIO_CMD_ST);
    endfunction : operation_compl
    
    local function void memory_cmd;
      `DISPLAY_LOGGER_WARNING($sformatf(
          "SD memory command %sCMD%0d is not supported by pure SDIO card",
          (last_cmd.app || go_for_acmd) ? "A" : " ", last_cmd.index))
      illegal_cmd = `TRUE;
    endfunction : memory_cmd
    
    // -----------------------------------------------------------------------
    
    function void sdio_update_block_length(bit [2:0] func);
      int unsigned tmp_blk_len = 32'd0;
      tmp_blk_len[7:0]   = sdio_regs.peek(3'd0, {6'd0, func, 8'h10});
      tmp_blk_len[15:8]  = sdio_regs.peek(3'd0, {6'd0, func, 8'h11});
      if (tmp_blk_len < 2049 && tmp_blk_len > 0)
        block_length = tmp_blk_len;
      else begin
        incorrect_block_length_sdio:
        assert (0) else begin
        `DISPLAY_LOGGER_ERROR($sformatf("Incorrect block length: %0d", tmp_blk_len))
        end
      end
    endfunction : sdio_update_block_length

//    function void sdio_update_bus_width(bit [1:0] val);
//      case (val)
//        2'b00:    this.bus_width = L1;
//        2'b10:    this.bus_width = L4;
//        default:  this.bus_width = LERR;
//      endcase
//      if (this.last_rsp != null)
//        this.last_rsp.new_bus_width = this.bus_width;
//    endfunction : sdio_update_bus_width
    
    // -----------------------------------------------------------------------
    
    function void sdio_pass_bus_info_to_xtor;
      if (!uhsii_based) begin
        sd_meta bus_meta = new;
        bus_meta.change_speed = `TRUE;
        
        if (volt18_switched)
          case (sdio_regs.get_sdio_bus_speed)
            3'd0:    bus_meta.new_speed = SDR12;
            3'd1:    bus_meta.new_speed = SDR25;
            3'd2:    bus_meta.new_speed = SDR50;
            3'd3:    bus_meta.new_speed = SDR104;
            3'd4:    bus_meta.new_speed = DDR50;
            default: bus_meta.change_speed = `FALSE;
          endcase
        else if (card_st == IDLE_ST  || card_st == READY_ST ||
                 card_st == IDENT_ST || card_st == INA_ST)
          bus_meta.new_speed = IDENT_SPEED;
        else
          case (sdio_regs.get_sdio_bus_speed % 2)
            3'd0:    bus_meta.new_speed = DEFAULT_SPEED;
            3'd1:    bus_meta.new_speed = HIGH_SPEED;
            default: bus_meta.change_speed = `FALSE;
          endcase

        if (bus_speed != bus_meta.new_speed) begin
          `DISPLAY_LOGGER_NOTE($sformatf(
              "Bus speed to be changed from %s to %s", bus_speed.name, bus_meta.new_speed.name))
          bus_speed = bus_meta.new_speed;
        end

        case (sdio_regs.get_sdio_bus_width)
          2'b00:   bus_meta.new_width = L1;
          2'b10:   bus_meta.new_width = L4;
          default: bus_meta.new_width = LERR;
        endcase
        
        if (bus_meta.new_width != LERR && bus_width != bus_meta.new_width) begin
          `DISPLAY_LOGGER_NOTE($sformatf(
              "Bus width to be changed from %s to %s", bus_width.name, bus_meta.new_width.name))
          bus_width = bus_meta.new_width;
        end
        else if (~bus_meta.change_speed)
          bus_meta = null;

        if (bus_meta != null)
          fork fork
            begin
              bus_speed_th_obj = process::self();
              #7ns;
              `WAIT_COND (mbx_rsp.num() == 0, 8.3ns)
              #7ns;
              mbx_dat_rd.put(bus_meta);
              bus_speed_th_obj = null;
            end
          join join_none
      end
    endfunction : sdio_pass_bus_info_to_xtor
    
    // -----------------------------------------------------------------------
    
    task sdio_execute_reset_or_abort(input bit [3:0] val);
      // val: [3] reset; [2:0] Abort Select [x]
      if (val[3]) begin
        // reset
        data_transf = null;
        cancel_ongoing_read_blocks;
        cancel_ongoing_write_blocks;
        if (~this.mem_present)
          internal_reset(`FALSE);
        else
          internal_reset_sdio;
        pass_bus_info_to_xtor;
      end
      else begin
        // stop transf
        if (card_st == RCV_ST) begin
          if (last_rsp == null)
            `DISPLAY_LOGGER_WARNING("SDIO Abort requested probably not with CMD52")
          else
            last_rsp.wr_dat_blklen = 0;
        end

        data_transf = null;
        cancel_ongoing_read_blocks;
      end
    endtask : sdio_execute_reset_or_abort
    
    // -----------------------------------------------------------------------
    
    function void sdio_update_intr_signal;
      bit [7:0] intr_flags    = sdio_regs.peek(3'd0, 17'h00005);
      bit [7:0] intr_enas     = sdio_regs.peek(3'd0, 17'h00004);
      bit       intr_signal_n = `TRUE;
      if (is_card_selected(card_st) && intr_enas[0]) // int ena master
        for (int i = 1; i < 8 && intr_signal_n; ++i)
          intr_signal_n &= ~(intr_flags[i] & intr_enas[i]);
      if (!this.mbx_intr.try_put(intr_signal_n))
        `DISPLAY_LOGGER_WARNING("Cannot update card interrupt signal")
    endfunction : sdio_update_intr_signal
    
    // -----------------------------------------------------------------------

    //////////////////////////////////////////////////////////////////////////
    
    protected virtual task execute_cmd2;
      // ALL_SEND_CID
      if (this.mem_present)
        super.execute_cmd2;
    endtask : execute_cmd2
    
    protected virtual task execute_cmd3;
      // SEND_RELATIVE_ADDR
      // CMD2 is mandatory for combo cards only:
      if (~this.mem_present && card_st == READY_ST)
        card_st = IDENT_ST;
      super.execute_cmd3;
      if (~this.mem_present)
        last_rsp.contents[0][12:0] = {13 {`LOW}}; // reserved for SDIO-only cards
    endtask : execute_cmd3
    
    protected virtual task execute_cmd4;
      // SET_DSR
      if (this.mem_present)
        super.execute_cmd4;
    endtask : execute_cmd4
    
    // =======================================================================
    //                       SDIO-specyfic CMD5 task
    // -----------------------------------------------------------------------
    
    protected virtual task execute_cmd5;
      // IO_SEND_OP_COMMAND
      bit voltage_match = `FALSE;

      if (sdio_st == SDIO_IDLE_ST) begin
        ocr_reg_sdio[30:28] = sdio_regs.func_num;
        ocr_reg_sdio[27]    = this.mem_present;
        ocr_reg_sdio[26]    = this.uhsii_based;

        if (last_cmd.arg[23:0] == 0); // inquiry mode
        else if (voltage_init_sdio.try_get) begin
          if (!uhsii_based)
            for (int i = 23; i >= 8 && ~voltage_match; --i)
              voltage_match = (last_cmd.arg[i] & ocr_reg_sdio[i]);
          if (voltage_match | uhsii_based) begin
            fork : voltage_init_thread
              fork
              begin
                // launch voltage initialization
                bit [31:0] voltage_init_arg = last_cmd.arg;
                volt_init_sdio_th_obj = process::self();
                if (!uhsii_based) begin
                  wait_units = (wait_units % 355000) + 20563;
                  `DISPLAY_LOGGER_INFO($sformatf(
                      "voltage initialization started (SDIO), wait_units=%0dns", wait_units))
                  #(wait_units * 1ns);
                  ocr_reg_sdio[24] = voltage_init_arg[24]; // S18A
                end
                ocr_reg_sdio[31] = `TRUE;
                volt_init_sdio_th_obj = null;
              end
              join
            join_none
            #2ns;
          end
          else begin
            `DISPLAY_LOGGER_INFO($sformatf("Voltage not matched ocr_reg=%0h", ocr_reg))
            change_state_sdio(SDIO_INA_ST);
            if (~ this.mem_present)
              change_state(INA_ST);
          end
        end

        last_rsp = new (R4);
        last_rsp.index = 6'b111111;
        last_rsp.contents[0] = ocr_reg_sdio;
        last_rsp.delay_cycles = 5; // use N_ID delay
        
        if (ocr_reg_sdio[31]) begin
          change_state_sdio(SDIO_RDY_ST);
          if (~ this.mem_present)
            change_state(READY_ST);
        end
      end
      else
        inappropriate_state;
    endtask : execute_cmd5
    
    // ==================================================================== //
    
    // execute_cmd6 -- inherited // SWITCH_FUNC
    
    protected virtual task execute_cmd7;
      // (DE)SELECT_CARD
      super.execute_cmd7;
      if (!illegal_cmd & last_cmd.arg[31:16] == rca_reg)
        // -> select
        change_state_sdio(SDIO_CMD_ST);
      else
        // -> deselect
        change_state_sdio(SDIO_STBY_ST);
      this.sdio_update_intr_signal;
    endtask : execute_cmd7
    
    // execute_cmd8 -- inherited // SEND_IF_COND

    protected virtual task execute_cmd9;
      // SEND_CSD
      if (this.mem_present)
        super.execute_cmd9;
      else
        this.memory_cmd;
    endtask : execute_cmd9

    protected virtual task execute_cmd10;
      // SEND_CID
      if (this.mem_present)
        super.execute_cmd10;
      else
        this.memory_cmd;
    endtask : execute_cmd10
    
    // execute_cmd11 -- inherited // VOLTAGE_SWITCH
    
    protected virtual task execute_cmd12;
      // STOP_TRANSMISSION
      if (this.mem_present)
        super.execute_cmd12;
      else
        this.memory_cmd;
    endtask : execute_cmd12
    
    // execute_cmd13 -- inherited // SEND_STATUS
     
    // execute_cmd14 -- inherited // reserved
    
    protected virtual task execute_cmd15;
      // GO_INACTIVE_STATE
      if (last_cmd.arg[31:16] == rca_reg) begin
        last_rsp = new (NONE_RSP);
        change_state(INA_ST);
        change_state_sdio(SDIO_INA_ST);//??
        pass_bus_info_to_xtor;//??
      end
    endtask : execute_cmd15
    
    protected virtual task execute_cmd16;
      // SET_BLOCKLEN
      if (this.mem_present)
        super.execute_cmd16;
      else
        this.memory_cmd;
    endtask : execute_cmd16

    protected virtual task execute_cmd17;
      // READ_SINGLE_BLOCK
      if (this.mem_present)
        super.execute_cmd17;
      else
        this.memory_cmd;
    endtask : execute_cmd17

    protected virtual task execute_cmd18;
      // READ_MULTIPLE_BLOCK
      if (this.mem_present)
        super.execute_cmd18;
      else
        this.memory_cmd;
    endtask : execute_cmd18

    // execute_cmd19 -- inherited // SEND_TUNING_BLOCK
    
    protected virtual task execute_cmd23;
      // SET_BLOCK_COUNT
      if (this.mem_present)
        super.execute_cmd23;
      else
        this.memory_cmd;
    endtask : execute_cmd23

    protected virtual task execute_cmd24;
      // WRITE_BLOCK // single
      if (this.mem_present)
        super.execute_cmd24;
      else
        this.memory_cmd;
    endtask : execute_cmd24

    protected virtual task execute_cmd25;
      // WRITE_MULTIPLE_BLOCK
      if (this.mem_present)
        super.execute_cmd25;
      else
        this.memory_cmd;
    endtask : execute_cmd25

    //// CMD20-22, CMD26-31 ---- inherited
    
    protected virtual task execute_cmd32;
      // ERASE_WR_BLK_START
      if (this.mem_present)
        super.execute_cmd32;
      else
        this.memory_cmd;
    endtask : execute_cmd32

    protected virtual task execute_cmd33;
      // ERASE_WR_BLK_END
      if (this.mem_present)
        super.execute_cmd33;
      else
        this.memory_cmd;
    endtask : execute_cmd33

    protected virtual task execute_cmd38;
      // ERASE
      if (this.mem_present)
        super.execute_cmd38;
      else
        this.memory_cmd;
    endtask : execute_cmd38
    
    //// CMD34-37, CMD 39-51 ---- inherited

    // =======================================================================
    //                      SDIO-specyfic CMD52-54 tasks
    // -----------------------------------------------------------------------
    
    protected virtual function void clear_sdio_flags_on_read;
      sdio_flags[ERROR_SDIO_FLAG]           = `FALSE;
      sdio_flags[FUNCTION_NUMBER_SDIO_FLAG] = `FALSE;
      sdio_flags[OUT_OF_RANGE_SDIO_FLAG]    = `FALSE;
    endfunction : clear_sdio_flags_on_read

    local task set_r5_flags_for_now;
      sdio_flags[COM_CRC_ERROR_SDIO_FLAG] = csr_reg[COM_CRC_ERROR_CSR_BIT];
      csr_reg[COM_CRC_ERROR_CSR_BIT] = `FALSE;
      
      sdio_flags[ILLEGAL_COMMAND_SDIO_FLAG] = csr_reg[ILLEGAL_COMMAND_CSR_BIT];
      csr_reg[ILLEGAL_COMMAND_CSR_BIT] = `FALSE;
      
      sdio_flags[ERROR_SDIO_FLAG] = csr_reg[ERROR_CSR_BIT];
      csr_reg[ERROR_CSR_BIT] = `FALSE;
      
      sdio_flags[OUT_OF_RANGE_SDIO_FLAG] = csr_reg[OUT_OF_RANGE_CSR_BIT];
      csr_reg[OUT_OF_RANGE_CSR_BIT] = `FALSE;

      sdio_flags[5:4] = sdio_st[1:0];
    endtask : set_r5_flags_for_now
    
    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----
    
    protected virtual task execute_cmd52;
      // IO_RW_DIRECT
      if ( (card_st == TRAN_ST || card_st == DATA_ST || card_st == RCV_ST  || card_st == PRG_ST) &&
           (sdio_st == SDIO_CMD_ST || sdio_st == SDIO_TRN_ST) ) begin
        last_rsp = new(R5);
        last_rsp.index = 6'd52;
        
        if (last_cmd.arg[30:28] > sdio_regs.func_num) begin
          invalid_sdio_func_52:
          assert (0) else begin
          `DISPLAY_LOGGER_ERROR("invalid SDIO function number")
          end
          sdio_flags[FUNCTION_NUMBER_SDIO_FLAG] = `TRUE;
        end
        else if (last_cmd.arg[31]) begin
          sdio_regs.write(
              last_cmd.arg[30:28], // func num
              last_cmd.arg[25:9],  // io reg addr
              last_cmd.arg[7:0]);  // write data
          last_rsp.contents[0][7:0] = last_cmd.arg[27] ? // read after write
              sdio_regs.peek(last_cmd.arg[30:28], last_cmd.arg[25:9]) :
              last_cmd.arg[7:0];
        end
        else
          last_rsp.contents[0][7:0] = sdio_regs.read(
              last_cmd.arg[30:28], // func num
              last_cmd.arg[25:9]); // io reg addr

        set_r5_flags_for_now;
        last_rsp.contents[0][15:8] = sdio_flags;
      end
      else
        inappropriate_state;
    endtask : execute_cmd52

    protected virtual task execute_cmd53;
      // IO_RW_EXTENDED
      if (card_st == TRAN_ST && sdio_st == SDIO_CMD_ST) begin
        if (last_cmd.arg[30:28] > sdio_regs.func_num) begin
          invalid_sdio_func_53:
          assert (0) else begin
          `DISPLAY_LOGGER_ERROR("invalid SDIO function number")
          end
          sdio_flags[FUNCTION_NUMBER_SDIO_FLAG] = `TRUE;
        end
        else if (last_cmd.arg[30:28] == 0 && ~last_cmd.arg[26])
          `DISPLAY_LOGGER_WARNING("Fixed reads/writes to Function 0 are not supported")
        else begin
          sdio_transf_cl sdio_data_transf;

          if (last_cmd.arg[27]) begin
            // SDIO block mode
            block_count = {25'd0, last_cmd.arg[8:0]};
            sdio_update_block_length(last_cmd.arg[30:28]);
          end
          else begin 
            // SDIO byte mode
            block_count = 1;
            block_length = (last_cmd.arg[8:0] == 0 ? 32'd512 : {25'd0, last_cmd.arg[8:0]});
          end
          
          if (block_length == 0 || block_length > 2048) begin
            invalid_block_lenght_sdio:
            assert (0) else begin
            `DISPLAY_LOGGER_ERROR($sformatf("Invalid block length: %0d", block_length))
            end
            return;
          end

          last_rsp = new(R5);
          last_rsp.index = 6'd53;
          set_r5_flags_for_now;
          last_rsp.contents[0][15:8] = sdio_flags;

          sdio_data_transf = new (last_cmd.arg[25:9],  // start addr
                                  last_cmd.arg[30:28], // func num
                                  sdio_regs, card_config.card_cap,
                                  block_length, block_count,
                                  last_cmd.arg[31] ? WRITE_OPER : READ_OPER,
                                  last_cmd.arg[26] ? INCR_ADDR : FIXED_ADDR,
                                  uhsii_based, last_cmd.arg[27], this.datagen);
          data_transf = sdio_data_transf;
        `ifdef USE_LOGGERS
          data_transf.init_logging(logger, log_id, hierarchy);
        `endif // USE_LOGGERS
          if (last_cmd.arg[31]) // for write transfers only:
            last_rsp.wr_dat_blklen = data_transf.get_blklen;
        
          `DISPLAY_LOGGER_INFO($sformatf(
              "new SDIO transfer defined: %s", data_transf.to_string))

          change_state(last_cmd.arg[31] ? RCV_ST : DATA_ST);
          change_state_sdio(SDIO_TRN_ST);

        end
      end
      else
        inappropriate_state;
    endtask : execute_cmd53
    
    protected virtual task execute_cmd54;
      // SDIO
      not_implemented_cmd;
    endtask : execute_cmd54
    
    // ==================================================================== //
    
    protected virtual task execute_cmd55;
      // APP_CMD
      if (this.mem_present)
        super.execute_cmd55;
      else
        this.memory_cmd;
    endtask : execute_cmd55
    
    //// CMD56-63, others ACMD ---- inherited
    
    protected virtual task execute_acmd6;
      // SET_BUS_WIDTH
      if (this.mem_present)
        super.execute_acmd6;
      else
        this.memory_cmd;
    endtask : execute_acmd6
    
    protected virtual task execute_acmd13;
      // SD_STATUS
      if (this.mem_present)
        super.execute_acmd13;
      else
        this.memory_cmd;
    endtask : execute_acmd13

    protected virtual task execute_acmd41;
      // SD_SEND_OP_COND
      if (this.mem_present)
        super.execute_acmd41;
      else
        this.memory_cmd;
    endtask : execute_acmd41
    
    protected virtual task execute_acmd51;
      // SEND_SCR
      if (this.mem_present)
        super.execute_acmd51;
      else
        this.memory_cmd;
    endtask : execute_acmd51
    
    //////////////////////////////////////////////////////////////////////////
    
    // to enforce interrupt factor in card:
    
    function void schedule_interrupt_generation (input bit [2:0] func, input int delay_in_ns);
      if (sdio_regs.func_num >= func && func > 0)
        fork
          fork
            begin
              byte_t int_flags;
              int_sched_sdio_th_obj = process::self();
              #(delay_in_ns * 1ns);

              int_flags  = sdio_regs.peek(3'd0, 17'h00005);
              int_flags |= 1 << func;
              sdio_regs.write(3'd0, 17'h00005, int_flags);
              int_sched_sdio_th_obj = null;
            end
          join_none
        join_none
      else begin
        invalid_sdio_func_requested:
        assert (0) else begin
        `DISPLAY_LOGGER_ERROR("invalid SDIO function number")
        end
      end
    endfunction : schedule_interrupt_generation
    
    // for debug purposes only:
    
    function void schedule_interrupt_suppression(input int delay_in_ns);
      fork
        fork
          begin
            #(delay_in_ns * 1ns);
            sdio_regs.write(3'd0, 17'h00005, 8'h00);
          end
        join_none
      join_none
    endfunction

  endclass : sdio_card_cl
endpackage : sdio_card_pkg
