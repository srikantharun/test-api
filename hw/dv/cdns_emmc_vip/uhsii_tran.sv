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
//   UHS-II TRAN Layer
//   
//   File contents  :  package uhsii_tran_pkg
//                     class   uhsii_tran_cl                                   
//------------------------------------------------------------------------------

`timescale 1ns / 100ps 

package uhsii_tran_pkg;
`include "card_logging.svh"
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import sd_mem_pkg::*;
  import uhsii_params_pkg::*;
  import uhsii_pkt_pkg::*;
  import sd_card_pkg::*;
  import sd_tok_pkg::*;

  // ----- UHSII CARD CAPABILITIES -----

  class uhsii_capabs_cl;
    const bit [3:0]  n_lss_dir;
    const bit [3:0]  n_lss_syn;
    const bit        hiber;              // Support Hibernate Mode

    const bit [7:0]  n_data_gap;
    const bit [11:0] max_blklen;
    const bit [7:0]  n_fcu;
    
    const bit        no_delays;

    function new (bit [3:0]  _n_lss_dir,
                  bit [3:0]  _n_lss_syn,
                  bit        _hiber,              // Support Hibernate Mode
                  bit [7:0]  _n_data_gap,
                  bit [11:0] _max_blklen,
                  bit [7:0]  _n_fcu,
                  bit        _no_delays);
      n_lss_dir   = _n_lss_dir;
      n_lss_syn   = _n_lss_syn;
      hiber       = _hiber;
      n_data_gap  = _n_data_gap;
      max_blklen  = _max_blklen;
      n_fcu       = _n_fcu;
      no_delays   = _no_delays;
    endfunction : new

    function string to_string;
      if (this == null) return "NULL (default UHS-II capabilities)";
      $swrite(to_string, "N_LSS_DIR=%h N_LSS_SYN=%h SHM=%b N_DATA_GAP=%h MAX_BLKLEN=%h N_FCU=%h",
        this.n_lss_dir, this.n_lss_syn, this.hiber, this.n_data_gap, this.max_blklen, this.n_fcu);
    endfunction : to_string
  endclass : uhsii_capabs_cl

  // ----- UHSII TRAN REQ CLASS -----

  class uhsii_req;
    bit          reset;     // 1=reset, 0=normal work
    bit          rw;        // 0=read, 1=write
    bit          cd;        // 0=ccmd, 1=dcmd
    bit          blm;       // block mode flag
    bit          dpm;       // duplex mode flag

    bit [31:0]   addr;      // [31:0] = mem addr or [11:0] = reg addr or SD Arg
    bit [31:0]   pld[];     // CMD/RES payload or contents of SD response
    int          tlen;      // TLEN (either bytes or blocks)
    bit          bc;        // broadcast CCMD

    bit          lsd;       // legacy SD protocol encapsulated
    bit          app;       // App cmnd flag in SD-Tran only
    bit [5:0]    cmd_index; // SD cmnd index in SD-Tran only 

    function string to_string;
      if (this == null)
        return "NULL";
      if (this.reset)
        return "RESET req";

      if (lsd)
        $swrite(to_string, "SD req %s%0d arg=%h in %s (%s rw=%b tlen=%0d)",
          this.app ? "ACMD" : "CMD",
          this.cmd_index,
          this.addr,
          this.cd  ? "DCMD"      : "CCMD",
          this.dpm ? "2L-HD"     : "FD",
          this.rw, this.tlen
        );
      else
        $swrite(to_string, "%s %s %s %s %s %s=%0d \t%s=%h",
          this.cd  ? "DCMD"      : "CCMD",
          this.bc  ? "broadcast" : "p2p      ",
          this.rw  ? "write"     : "read ",
          this.blm ? "blocks"    : "bytes ",
          this.dpm ? "2L-HD"     : "FD   ",
          this.cd  ? "tlen"      : "plen",
          this.cd  ? this.tlen   : pld.size == 4 ? 3 : pld.size,
          this.cd  ? " D addr"   : "IO addr",
          this.cd  ?  addr       :  addr[11:0]
        );
    endfunction : to_string
    
    // legacy SD utility functions
    
    function bit is_reset;
      return ~this.app && ~this.cd && (this.cmd_index == 6'd0 || (
          this.cmd_index == 6'd52 &&
          this.addr[31]    == 1'b1 &&
          this.addr[30:28] == 3'd0 &&
          this.addr[25:9]  == 17'h00006 &&
          this.addr[3]     == 1'b1
      ));
    endfunction : is_reset
    
    function bit is_stop_transf;
      return ~this.app && ~this.cd && (this.cmd_index == 6'd12 || (
          this.addr[31]    == 1'b1 &&
          this.addr[30:28] == 3'd0 &&
          this.addr[25:9]  == 17'h00006 &&
          this.addr[3]     == 1'b0
      ));
    endfunction : is_stop_transf
    
    function int calc_sdio_tlen;
      if (this.addr[27])
        return this.addr[8:0] == 8'd0 ? -1 : this.addr[8:0];
      else
        return 1; // byte mode means single block
    endfunction : calc_sdio_tlen
    
  endclass : uhsii_req

  // ----- UHSII TRAN (NP) RSP CLASS -----

  class uhsii_rsp;
    bit             nak;
    bit [2:0]       ecode;
    int             n_fcu;
    int             blk_len;
    uhsii_req       req;
    bit             fsm_rst;
    bit             go2dormant;
    bit             phy_rst;

    bit             transf_compl; // last burst acked

    local sd_mem_cl          mem_pool;
    protected int unsigned   index;
    protected mem_blk        mem_tmp[$];

    lss_params_cl change_params;

    function new(uhsii_req req, sd_mem_cl mem_pool);
      this.req              =  req;
      this.mem_pool         =  mem_pool;
      this.mem_tmp          =  {};
      this.change_params    =  null;
      this.transf_compl     = `FALSE;
    endfunction : new

    virtual function bit has_next_blk;
      if (!req.cd || this.nak)
        return `FALSE; // no data transfer for CCMD or NAK=1
      if (req.tlen == -1)
        return `TRUE; // any length of data if TLEN is unspecified
      if (req.blm)
        // native DCMD block mode
        return (index + (req.rw ? mem_tmp.size : 0) < req.tlen);
      else
        // native DCMD byte mode
        return (index == 0) && (mem_tmp.size == 0 || !req.rw);
    endfunction : has_next_blk

    virtual function mem_blk get_next_blk();
      return (!req.cd || req.rw) ? null :
        mem_pool.get_mem_blk(req.addr + index++);
    endfunction : get_next_blk

    virtual function void complete_get(bit retry);
      int unsigned last_read;
      if (retry) begin
        if (!req.blm)
          index = 0;
        else begin
          int unsigned last_read = index % n_fcu;
          if (last_read == 0) last_read = n_fcu;
          index -= last_read;
        end
      end
    endfunction

    function void put_next_blk(mem_blk blk);
      if (req.cd && req.rw)
        mem_tmp.push_back(blk);
    endfunction : put_next_blk

    virtual function void complete_put(bit retry);
      if (retry)
        mem_tmp = {};
      else while (mem_tmp.size > 0)
        mem_pool.put_mem_blk(mem_tmp.pop_front, req.addr + index++);
    endfunction : complete_put

    function string to_string;
      if (this == null)
        return "NULL";
      to_string = (req == null ? "req missing" : req.to_string);
      $swrite(to_string, "%s   -->  nak=%b", to_string, this.nak);
      if (req != null && req.cd)
        $swrite(to_string, "%s n_fcu=%d", to_string, n_fcu);
      else begin
        if (fsm_rst)
          $swrite(to_string, "%s fsm_rst", to_string);
        if (go2dormant)
          $swrite(to_string, "%s go2dormant", to_string);
        if (phy_rst)
          $swrite(to_string, "%s phy_rst", to_string);
      end
    endfunction : to_string

    virtual task wait_to_send_ebsy(output bit send);
      send = `FALSE;
    endtask : wait_to_send_ebsy
    
    virtual function bit start_data_transfer;
      return req.cd & ~this.nak;
    endfunction : start_data_transfer
  endclass : uhsii_rsp

  // ----- UHSII TRAN (SD) RSP CLASS -----

  class uhsii_rsp_sd extends uhsii_rsp;
    local mem_blk   rd_blk;
    local bit       wr_blk;

    bit             stop_transf;    // CMD12 or reset received
    bit             transf_ended;   // busy signal from SD-tran
    bit             ebsy_expected;  
    bit             ebsy_reached;    

    local bit       read_retry;
    
    bit             r1_r5_err;

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    function new (uhsii_req req, sd_mem_cl mem_pool);
      super.new(req, mem_pool);
      this.rd_blk        =  null;
      this.wr_blk        = `FALSE;
      this.stop_transf   = `FALSE;
      this.ebsy_expected = `FALSE;
      this.ebsy_reached  = `FALSE;
      this.transf_ended  = `FALSE;
      assert (req != null && req.lsd) else $fatal(1, "internal sd-tran error");
    endfunction : new

    virtual function bit has_next_blk();
      has_next_blk = ((stop_transf | transf_ended) ?
        `FALSE : super.has_next_blk);
    endfunction : has_next_blk

    virtual function mem_blk get_next_blk();
      if (read_retry && mem_tmp.size > 0) begin
        assert (mem_tmp.size > (index % n_fcu)) else $fatal(1,
            "Internal card model error: read_retry=%0b mem_tmp.size=%0d index=%0d n_fcu=%0d",
            read_retry, mem_tmp.size, index, n_fcu);
        get_next_blk = mem_tmp[index % n_fcu];
      end
      else begin
        assert (rd_blk != null) else $fatal(1,
            "Internal card model error: no rd_blk when get_next_blk invoked");
        mem_tmp.push_back(rd_blk);
        get_next_blk = rd_blk;
        rd_blk = null;
        read_retry = `FALSE;
      end
      ++index;
    endfunction : get_next_blk

    virtual function void complete_get(bit retry);
      if (retry)
        index -= mem_tmp.size;
      else
        mem_tmp = '{};
      read_retry = retry;
    endfunction : complete_get

    virtual function void complete_put(bit retry);
      if (retry)
        mem_tmp = {};
      else
        wr_blk = `TRUE;
    endfunction : complete_put

    task put_rd_blk(input mem_blk blk);
      rd_blk = blk;
      wait (rd_blk == null || stop_transf);
    endtask : put_rd_blk

    task get_wr_blk(output mem_blk blk);
      if (has_next_blk)
        wait (wr_blk || stop_transf);
      if (mem_tmp.size > 0) begin
        blk = mem_tmp.pop_front;
        ++index;
        if (mem_tmp.size == 0)
          wr_blk = `FALSE;
      end
      else
        blk = null;
    endtask : get_wr_blk

    function bit has_next_wr_dat;
      return mem_tmp.size > 0;
    endfunction : has_next_wr_dat

    virtual task wait_to_send_ebsy(output bit send);
      if (stop_transf | transf_compl | transf_ended) begin
        // EBSY is sent only if transfer has been completed or stopped or for erase
        if (ebsy_expected & !ebsy_reached)
          wait (ebsy_reached | !ebsy_expected);
        send = ebsy_expected & ebsy_reached;
        ebsy_expected = `FALSE; // doubled EBSY is sent once per transaction
      end
      else
        send = `FALSE;
    endtask : wait_to_send_ebsy

    virtual function bit start_data_transfer;
      return req.cd & ~this.nak & ~this.r1_r5_err;
    endfunction : start_data_transfer
  endclass : uhsii_rsp_sd

  // *** CHECKING ADDRESSES ***

  /** Asserts the specified address is not reserved in UHSII register space. */
  function bit ensure_reg_addr_is_not_reserved(input bit [11:0] ioadr);
    return
      ((ioadr >= 12'h000  &&  ioadr <= 12'h005) || // Capabilities Register
       (ioadr >= 12'h008  &&  ioadr <= 12'h00D) || // Settings     Register
       (ioadr == 12'h040) || (ioadr == 12'h041) || // Preset       Register
       (ioadr == 12'h100) || (ioadr == 12'h101) || // Interrupt    Register
       (ioadr == 12'h180) ||                       // Status       Register
       (ioadr >= 12'h200  ||  ioadr <= 12'h204));  // Command      Register
  endfunction : ensure_reg_addr_is_not_reserved

  function bit ensure_reg_addr_is_command(input bit [11:0] ioadr);
    ensure_reg_addr_is_command = (ioadr >= 12'h200 && ioadr <= 12'h204);
  endfunction : ensure_reg_addr_is_command

  function bit ensure_reg_addr_can_be_written(input bit [11:0] ioadr);
    return
      ((ioadr >= 12'h008  &&  ioadr <= 12'h00D) || // Settings  Register
       (ioadr == 12'h100) || (ioadr == 12'h101));  // Interrupt Register
  endfunction : ensure_reg_addr_can_be_written

  function bit ensure_plen_is_within_valid_range(input bit [11:0] ioadr,
                                                 input int        plen);
    // keep in mind that plen equals: 0, 1, 2 or 3 (which means 4).
    return (plen < 2) ? `TRUE : (plen == 3 ?
            ensure_reg_addr_is_not_reserved(ioadr + 3) :
            ensure_reg_addr_is_not_reserved(ioadr + 1) );
  endfunction : ensure_plen_is_within_valid_range

  function bit ensure_plen_has_valid_value(input longint plen);
    ensure_plen_has_valid_value = (plen >= 0 && plen <= 4 && plen != 3);
    assert (ensure_plen_has_valid_value)
    else $error("Internal error: plen is %d", plen);
  endfunction : ensure_plen_has_valid_value

  // ===== UHSII TRAN CLASS =====

  class uhsii_tran_cl extends component_cl;
    local mailbox #(uhsii_req)             mbx_req;
    local mailbox #(uhsii_rsp)             mbx_rsp;
    local mailbox #(sd_cmd)                mbx_sd_cmd;
    local mailbox #(sd_rsp)                mbx_sd_rsp;
    local mailbox #(sd_dat)                mbx_dat_wr;
    local mailbox #(sd_dat)                mbx_dat_rd;

    local sd_card_cl                       sd_leg;

    local uhsii_req                        req;
    local uhsii_rsp                        rsp;

    local int unsigned                     reg_mem[bit[11:0]];
    local sd_mem_cl                        data_mem;
 
    local bit [3:0]                        own_node_id;
    local bit                              initialized;

    local uhsii_rsp_sd                     curr_transf;

    local process                          main_th_obj = null,
                                           ebsy_th_obj = null;

    struct {
      bit cmd_nak;
    } error_gen;

    semaphore error_gen_sem;

    // -------------------------------------------------------------------- //

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    function new(input string                _name,
                 input component_cl          _parent,
                 input mailbox #(uhsii_req)  mbx_req,
                 input mailbox #(uhsii_rsp)  mbx_rsp,
                 input sd_card_cl            sd_leg,
                 input mailbox #(sd_cmd)     mbx_sd_cmd,
                 input mailbox #(sd_rsp)     mbx_sd_rsp,
                 input mailbox #(sd_dat)     mbx_dat_wr,
                 input mailbox #(sd_dat)     mbx_dat_rd,
                 input bit                   sdmem_flag,
                 input bit                   sdio_flag,
                 input sd_mem_cl             data_mem = null,
                 input uhsii_capabs_cl       card_capabs = null);
      super.new(_name, _parent);

      this.mbx_req     = mbx_req;
      this.mbx_rsp     = mbx_rsp;
      this.sd_leg      = sd_leg;
      this.mbx_sd_cmd  = mbx_sd_cmd;
      this.mbx_sd_rsp  = mbx_sd_rsp;
      this.mbx_dat_wr  = mbx_dat_wr;
      this.mbx_dat_rd  = mbx_dat_rd;
      this.data_mem    = data_mem;
      
      this.error_gen_sem = new (1);

      if (data_mem == null)
        this.data_mem = new("memory", this);

      `DISPLAY_LOGGER_INFO($sformatf("initializing UHSII capabilities %s", card_capabs.to_string));
      if (card_capabs != null)
        this.set_start_config({46'h00000000000, sdio_flag, sdmem_flag, 16'h0100},
                              {24'h000000,
                               card_capabs.n_lss_dir,  card_capabs.n_lss_syn, 16'h0000,
                               card_capabs.hiber,      15'h0000},
                              {24'h000000,
                               card_capabs.n_data_gap, card_capabs.max_blklen, 4'h2,
                               card_capabs.n_fcu,      8'h00},
                               64'h0000000000000000);
      else
        this.set_start_config;
    endfunction : new

    task start;
      fork
        run;
      join_none
    endtask : start

    function string get_class_name;
      return "uhsii_tran_cl";
    endfunction : get_class_name

    function void dispose;
      uhsii_rsp_sd sd_transf;

      if (main_th_obj != null)
        main_th_obj.kill;
      if (ebsy_th_obj != null)
        ebsy_th_obj.kill;

      if (curr_transf != null)
        if ($cast(sd_transf, curr_transf))
          sd_transf.stop_transf = `TRUE;
    endfunction : dispose

    task run();
      `DISPLAY_LOGGER_NOTE("run method of UHSII_TRAN started")
      main_th_obj = process::self();
      // send start param values from TRAN registers
      rsp = new (null, null);
      clear_and_copy_config;
      rsp.change_params = this.refresh_config;
      mbx_rsp.put(rsp);

      // *** main thread ***
      forever begin
        mbx_req.get(req);
        process_transaction(req, rsp);
        mbx_rsp.put(rsp);
      end
    endtask : run

    task process_transaction(input  uhsii_req req,
                             output uhsii_rsp rsp);
      if (req.reset)
        execute_reset(rsp);
      else if (req.lsd)
        process_transaction_sd(req, rsp);
      else
        process_transaction_np(req, rsp);
    endtask : process_transaction

    // -------------------------------------------------------------------- //

    // ***** NATIVE PROT OPERATION *****

    task process_transaction_np(input uhsii_req req, output uhsii_rsp rsp);
      this.error_gen_sem.get(1);
      if (error_gen.cmd_nak) begin
        error_gen.cmd_nak = `FALSE;
        this.error_gen_sem.put(1);
        `DISPLAY_LOGGER_NOTE($sformatf(
            "Error injection: NAK into %s NP CMD", req.bc ? "broadcast" : "p2p"))
        rsp = respond_with_error(req, $urandom(5) ? ECODE_GEN_ERR :
                                      $urandom(3) ? ECODE_ARG_ERR :
                                                    ECODE_COND_ERR);
        return;
      end
      this.error_gen_sem.put(1);

      if (req.cd)
        // DCMD shall always be p2p
        rsp = process_dcmd(req);
      // CCMD
      else if (!ensure_reg_addr_is_not_reserved(req.addr[11:0]))
        rsp = respond_with_error(req, ECODE_COND_ERR);
      else if (! ensure_plen_has_valid_value(req.pld.size))
        rsp = null;
      else if (! ensure_plen_is_within_valid_range(req.addr[11:0],
                                                   req.pld.size))
        rsp = respond_with_error(req, ECODE_GEN_ERR);
      else if (ensure_reg_addr_is_command(req.addr[11:0]))
        rsp = req.rw ?
          execute_uhsii_command(req) :
          respond_with_error(req, ECODE_COND_ERR); // should be write oper
      else if (req.bc)
        rsp = req.rw ?
          set_common_config(req) :
          inquiry_config(req);
      else
        rsp = req.rw ?
          write_reg(req) :
          read_reg(req);
    endtask : process_transaction_np

    // --- transaction processing details ---
    
    local function void debug_uhsii_config_reg_space(input uhsii_req req);
      for (int i = 0; i < req.pld.size; ++i) begin
        case (req.addr[11:0] + i)
          // generic settings register:
          12'h008:
            //if (req.pld[i][0] != reg_mem[12'h008][0])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("Power Control Mode set to %s",
                  req.pld[i][0] ? "LPM" : "Fast Mode"))
          12'h009:
            //if (req.pld[i][31] != reg_mem[12'h009][31])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("Config Completion set to %0b",
                  req.pld[i][31]))
          // PHY settings register
          12'h00A:
            //if (req.pld[i][7:6] != reg_mem[12'h00A][7:6])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("Speed range set to %s",
                  req.pld[i][7:6] == 2'b00 ? "Range A" :
                  req.pld[i][7:6] == 2'b01 ? "Range B" :
                                             "Reserved"))
          12'h00B: begin
            //if (req.pld[i][3:0] != reg_mem[12'h00B][3:0])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("N_LSS_SYN set to %0d (x4)",
                  req.pld[i][3:0] == 0 ? 16 : req.pld[i][3:0]))
            //if (req.pld[i][7:4] != reg_mem[12'h00B][7:4])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("N_LSS_DIR set to %0d (x8)",
                  req.pld[i][3:0] == 0 ? 16 : req.pld[i][3:0]))
          end
          // LINK/TRAN settings register
          12'h00C: begin
            //if (req.pld[i][15:8] != reg_mem[12'h00C][15:8])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("N_FCU set to %0d",
                  req.pld[i][15:8] == 0 ? 256 : req.pld[i][15:8]))
            //if (req.pld[i][17:16] != reg_mem[12'h00C][17:16])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("MAX_RETRY_NUM set to %0d",
                  req.pld[i][17:16]))
            //if (req.pld[i][31:20] != reg_mem[12'h00C][31:20])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("MAX_BLKLEN set to %0d",
                  req.pld[i][31:20]))
          end
          12'h00D:
            //if (req.pld[i][7:0] != reg_mem[12'h00D][7:0])
              `DISPLAY_LOGGER_DEBUG(1, $sformatf("N_DATA_GAP set to %0d",
                  req.pld[i][7:0]))
        endcase
      end
    endfunction : debug_uhsii_config_reg_space

    function uhsii_rsp read_reg(input uhsii_req req);
      for (int i = 0; i < req.pld.size; ++i)
        req.pld[i] = reg_mem[req.addr[11:0] + i];
      read_reg = new (req, null);
    endfunction : read_reg

    function uhsii_rsp write_reg(input uhsii_req req);
      uhsii_rsp rsp = new (req, null);
      if (ensure_reg_addr_can_be_written(req.addr[11:0])) begin
        debug_uhsii_config_reg_space(req);
        for (int i = 0; i < req.pld.size; ++i)
          reg_mem[req.addr[11:0] + i] = req.pld[i];
        rsp.change_params = this.refresh_config;
      end
      else
        rsp = respond_with_error(req, ECODE_GEN_ERR);
      return rsp;
    endfunction : write_reg

    function uhsii_rsp inquiry_config(input uhsii_req req);
      uhsii_rsp rsp;
      if (req.addr[11:0] >= 12'h000 &&
          req.addr[11:0] <= 12'h005) begin
        for (int i = 0; i < req.pld.size; ++i)
          req.pld[i] = negotiate_config(req.addr[11:0] + i, req.pld[i]);
        rsp = new (req, null);
        return rsp;
      end
      else
        return respond_with_error(req);
    endfunction : inquiry_config

    function uhsii_rsp set_common_config(input uhsii_req req);
      if (req.addr[11:0] >= 12'h008 &&
          req.addr[11:0] <= 12'h00D)
        return write_reg(req);
      else
        return respond_with_error(req);
    endfunction : set_common_config

    function uhsii_rsp process_dcmd(input uhsii_req req);
      uhsii_rsp rsp = new (req, this.data_mem);
      int unsigned temp = reg_mem[12'h00C];
      if (req.blm) begin
        rsp.n_fcu   = (temp[15:8] == 8'h00 ? 256 : temp[15:8]);
        rsp.blk_len = temp[31:20];
      end
      return rsp;
    endfunction : process_dcmd

    // *** UHSII COMMAND EXECUTION ***

    function uhsii_rsp execute_uhsii_command(input uhsii_req req);
      case (req.addr[11:0])
        UHSII_CMD_IOADR_FULL_RESET:
          return execute_full_reset(req);
        UHSII_CMD_IOADR_GO_DORMANT_STATE:
          return execute_go_dormant_state(req);
        UHSII_CMD_IOADR_DEVICE_INIT:
          return execute_device_init(req);
        UHSII_CMD_IOADR_ENUMERATE:
          return execute_enumerate(req);
        UHSII_CMD_IOADR_TRANS_ABORT:
          return execute_trans_abort(req);
        default: begin
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unknown command addr: %h", req.addr))
          return respond_with_error(req);
        end
      endcase
    endfunction : execute_uhsii_command

    /** Executes FULL_RESET UHS-II cmd. */
    local function uhsii_rsp execute_full_reset(input uhsii_req req);
      uhsii_rsp rsp  = new (req, null);
      initialized    = `FALSE;
      rsp.phy_rst    = `TRUE; // tells the link to reset its FSMs and PHY!
      `DISPLAY_LOGGER_NOTE("Executing FULL RESET")

      clear_and_copy_config;
      rsp.change_params = this.refresh_config;

      if (curr_transf != null) begin
        curr_transf.stop_transf = `TRUE;
        curr_transf.ebsy_expected = `FALSE;
      end

      if (sd_leg != null)
        fork
          begin
            sd_cmd cnc = new;
            sd_rsp tmp;
            cnc.power_cycle = `TRUE;
            mbx_sd_cmd.put(cnc);
            mbx_sd_rsp.get(tmp);
          end
        join_none
        `DISPLAY_LOGGER_NOTE("FULL RESET +finished+")
      return rsp;
    endfunction : execute_full_reset


    local function uhsii_rsp execute_go_dormant_state(input uhsii_req req);
      uhsii_rsp rsp = new (req, null);
      rsp.go2dormant = `TRUE; // tells the link to tell the XTOR to switch off PHY
      `DISPLAY_LOGGER_NOTE("Executing GO TO DORMANT")
      return rsp;
    endfunction : execute_go_dormant_state


    local function uhsii_rsp execute_device_init(input uhsii_req req);
      uhsii_rsp rsp = new (req, null);
      bit [3:0] cdcp, gn, gd, gap, dap;
      if (!req.bc || req.pld.size != 1)
        rsp = respond_with_error(req, ECODE_ARG_ERR);
      else if (initialized);
      else begin
        {cdcp, gn}     = reg_mem[12'h040][7:0];
        {gd, gap, dap} = req.pld[0][31:20];
        `DISPLAY_LOGGER_NOTE($sformatf(
            "Executing DEVICE INIT: cdcp=%h gn=%h gd=%h gap=%h dap=%h",
            cdcp, gn, gd, gap, dap))
        if (gd == gn) begin
          if (dap == 4'h0)
            dap = 4'h1;
          if (cdcp == 0) begin
            while (gap > cdcp && dap > cdcp)
              ++cdcp; // sets power in a greedy way
            if (cdcp > 0)
              initialized = `TRUE;
          end
          if (gap >= cdcp && dap >= cdcp) begin
            gap -= cdcp;
            initialized = `TRUE;
          end
        end

        req.pld[0][27:24] = gap;
        req.pld[0][19] = initialized & req.pld[0][19]; // completion flag
      end
    
      return rsp;
    endfunction : execute_device_init

    local function uhsii_rsp execute_enumerate(input uhsii_req req);
      uhsii_rsp rsp  = new (req, null);
      bit [3:0] id_f = req.pld.size > 0 ? req.pld[0][31:28] : 4'h0,
                id_l = req.pld.size > 0 ? req.pld[0][27:24] : 4'h0;

      `DISPLAY_LOGGER_NOTE($sformatf(
          "Executing ENUMERATE: id_f=%h id_l=%h", id_f, id_l))
  
      if (!req.bc) begin
        rsp = respond_with_error(req, ECODE_ARG_ERR);
        return rsp;
      end

      if (id_l == 4'h0) begin
        own_node_id = (id_f == 4'hF ?
          (own_node_id == 4'hF ?
            4'h1 :
            (own_node_id + 4'h1)) :
          (id_f + 4'h1));
        id_f = own_node_id;
        id_l = own_node_id;
      end
      else begin
        own_node_id = (id_l == 4'hF ?
          4'h1 :
          (id_l + 4'h1));
        if (id_f == 4'h0 || id_f == own_node_id)
          rsp.nak = `TRUE; // error
        else
          id_l = own_node_id;
      end

      if (req.pld.size > 0) begin
        req.pld[0][31:28] = id_f;
        req.pld[0][27:24] = id_l;
        `DISPLAY_LOGGER_NOTE($sformatf(
            "'%H' accepted as device ID debug: id_f=%h id_l=%h",
            own_node_id, id_f, id_l))
        if (sd_leg != null)
          sd_leg.enumerate_executed(own_node_id);
        return rsp;
      end
      else
        return respond_with_error(req);
    endfunction : execute_enumerate

    local function uhsii_rsp execute_trans_abort(input uhsii_req req);
      uhsii_rsp rsp = new (req, null);
      if (req.bc)
        rsp.nak = `TRUE; // should be p2p ccmd
      else
        rsp.fsm_rst = `TRUE; // tells the link to reset its FSMs
      `DISPLAY_LOGGER_NOTE("Executing TRANS ABORT")
      return rsp;
    endfunction : execute_trans_abort

    function bit [3:0] get_own_node_id;
      return this.own_node_id;
    endfunction : get_own_node_id

    function bit [5:0] get_last_sd_cmd_index;
      return (this.req == null || ~this.req.lsd) ? -1 : this.req.cmd_index;
    endfunction : get_last_sd_cmd_index
    
    // returns 1 if and only if last received cmd was SD-TRAN CCMD
    function bit get_last_sd_cmd_was_ccmd;
      return this.req != null && this.req.lsd && ~this.req.cd;
    endfunction : get_last_sd_cmd_was_ccmd
    
    // returns 1 if and only if last received cmd was SD-TRAN DCMD
    function bit get_last_sd_cmd_was_dcmd;
      return this.req != null && this.req.lsd && this.req.cd;
    endfunction : get_last_sd_cmd_was_dcmd

    // *** ERROR RESPONSES ***

    function uhsii_rsp respond_with_error(input uhsii_req req,
                                          input bit [2:0] ecode = ECODE_GEN_ERR);
      respond_with_error        = new (req, null);
      respond_with_error.nak    = `TRUE;
      respond_with_error.ecode  = ecode;
    endfunction : respond_with_error

    // *** UHSII REG FIELDS ACCESS ***

    /** Loads default values into capabilities and preset registers
        (upon simulation start). */
    function void set_start_config(
        // [23:16] = appl typ; [14] = DADR len; [13:8] = lanes;
        input bit [63:0] gen_capab = 64'h0000000000010100,

        // [39:36] = N_LSS_DIR; [35:32] = N_LSS_SYN; [15] = hibernate support;
        // [5:4] = PHY major rev; [3:0] = PHY minor rev;
        input bit [63:0] phy_capab = 64'h0000004400000000,

        // [39:32] = N_DATA_GAP; [31:20] = MAX_BLKLEN; [18:16] = dev typ;
        // [15:8] = N_FCU; [5:4] = LINK/TRAN major rev;
        // [3:0] = LINK/TRAN minor rev;
        input bit [63:0] link_tran_capab = {64'h0000000220020000},

        // [7:4] = CDCP; [3:0] = GN
        input bit [63:0] presets = 64'h0000000000000000
    );
      this.reg_mem[12'h000] = gen_capab[31:0];
      this.reg_mem[12'h001] = gen_capab[63:32];
      this.reg_mem[12'h002] = phy_capab[31:0];
      this.reg_mem[12'h003] = phy_capab[63:32];
      this.reg_mem[12'h004] = link_tran_capab[31:0];
      this.reg_mem[12'h005] = link_tran_capab[63:32];
      this.reg_mem[12'h040] = presets[31:0];
      this.reg_mem[12'h041] = presets[63:32];
    endfunction : set_start_config

    /** Clears settings, interrupts and status registers, than loads default values from
        capabilities into settings register. Shall be invoked upon device reset. */
    function void clear_and_copy_config;
      int unsigned temp_sett;

      // load capabilities into settings  
      for (int i = 0; i < 6; ++i) begin
        temp_sett = this.reg_mem[i];
        case (i)
          0: temp_sett = {20'h00000,          // reserved, config compl = 0
                          temp_sett[11:8],    // lanes copied
                          8'h00};             // reserved, LPM = 0
  
          1: temp_sett =  32'h00000000;       // reserved
  
          2: temp_sett = {26'h0000000,        // reserved, speed = 0
                          temp_sett[5:4],     // PHY major rev copied
                          4'h0};              // reserved
  
          3: temp_sett = {24'h000000,         // reserved
                          temp_sett[7:0]};    // N_LSS_DIR + N_LSS_SYN copied
  
          4: temp_sett = {temp_sett[31:20],   // MAX_BLKLEN copied
                          4'h3,               // max retry num = 2'b11
                          temp_sett[15:8],    // N_FCU copied
                          8'h00};             // reserved
  
          5: temp_sett = {24'h000000,         // reserved
                          temp_sett[7:0]};    // N_DATA_GAP copied
        endcase
        
        this.reg_mem[i+8] = temp_sett;
      end
      
      // clear interrupts
      this.reg_mem[12'h100] = 64'h0000000000000000;
      this.reg_mem[12'h101] = 64'h0000000000000000;

      // clear status:
      this.reg_mem[12'h180] = 64'h0000000000000000;
    endfunction : clear_and_copy_config

    /** Sets some parameter values in Generic Capabilities register.*/
    function void set_config(input bit [3:0]   n_lss_dir,
                             input bit [3:0]   n_lss_syn,
                             input bit         hibernate,
                             input bit [7:0]   n_data_gap,
                             input bit [11:0]  max_blklen,
                             input bit [7:0]   n_fcu);
        this.reg_mem[12'h003][7:4]      = n_lss_dir;
        this.reg_mem[12'h003][3:0]      = n_lss_syn;
        this.reg_mem[12'h002][15]       = hibernate;
        this.reg_mem[12'h005][7:0]      = n_data_gap;
        this.reg_mem[12'h004][31:20]    = max_blklen;
        this.reg_mem[12'h004][15:8]     = n_fcu;
    endfunction : set_config

    /** Chooses parameter values which satisfy capabilities of the device
        and settings requested by the host. */
    function bit [31:0] negotiate_config(input bit [11:0] ioadr,
                                         input bit [31:0] given_sett);
      bit [31:0] sel_sett = given_sett;
      bit [31:0] own_sett = reg_mem[ioadr];

      case (ioadr)
        12'h000: begin
          sel_sett[14:8]  = own_sett[14:8]  ;
          sel_sett[23:16] = own_sett[23:16] ;
        end

        12'h001: /* do nothing */;

        12'h002: begin
          // hibernate support:
          sel_sett[15]  =  own_sett[15]  & given_sett[15];
          // PHY major rev:
          sel_sett[5:4] = (own_sett[5:4] < given_sett[5:4]) ?
                           own_sett[5:4] : given_sett[5:4];
        end

        12'h003: begin
          // N_LSS_DIR:
          sel_sett[7:4] = (own_sett[7:4] > given_sett[7:4]) ?
                           own_sett[7:4] : given_sett[7:4];
          // N_LSS_SYN:
          sel_sett[3:0] = (own_sett[3:0] > given_sett[3:0]) ?
                           own_sett[3:0] : given_sett[3:0];
        end

        12'h004: begin
          // MAX_BLKLEN:
          sel_sett[31:20] = (own_sett[31:20] < given_sett[31:20]) ?
                             own_sett[31:20] : given_sett[31:20];
          // N_FCU
          sel_sett[15:8] = (
                (own_sett[15:8]   == 8'h00 ? 9'd256 : {1'b0, own_sett[15:8]  }) <
                (given_sett[15:8] == 8'h00 ? 9'd256 : {1'b0, given_sett[15:8]}) ) ?
                             own_sett[15:8] : given_sett[15:8];
          // LINK/TRAN major rev:
          sel_sett[5:4] = (own_sett[5:4]  < given_sett[5:4]) ?
                           own_sett[5:4]  : given_sett[5:4];
        end

        12'h005:
          // N_DATA_GAP:
          sel_sett[7:0] = (own_sett[7:0] > given_sett[7:0]) ?
                           own_sett[7:0] : given_sett[7:0];
      endcase
  
      return sel_sett;
    endfunction : negotiate_config

    function lss_params_cl refresh_config;
      string temp_string;
      int unsigned temp  = reg_mem[12'h00B];
      int n_lss_dir   = {1'b0,
                        (temp[7:4] == 0 ? 5'b10000 : temp[7:4]),
                          3'b000}; // x8
      int n_lss_syn   = {1'b0,
                        (temp[3:0] == 0 ? 5'b10000 : temp[3:0]),
                         2'b00}; // x4
  
      bit [7:0] n_fcu = reg_mem[12'h00C][15:8];
      if (n_fcu == 0) n_fcu = 9'h100;

      refresh_config = new( n_lss_dir,
                            n_lss_syn,
                            reg_mem[12'h00D][7:0],    // N_DATA_GAP
                            reg_mem[12'h00A][7:6],    // RCLK RANGE
                            reg_mem[12'h008][0] &     // LPM
                            reg_mem[12'h009][31],     // config compl
                            n_fcu,
                            reg_mem[12'h00C][31:20],  // MAX_BLKLEN
                            reg_mem[12'h00C][17:16]); // MAX_RETRY_NUM
      $swrite(temp_string, "DEBUG: -- IO space reg contents");
    `ifdef USE_LOGGERS
      $swrite(temp_string,
          "%s</br>000: %h</br>001: %h</br>002: %h</br>003: %h</br>004: %h</br>005: %h",
          temp_string,
          reg_mem[12'h000], reg_mem[12'h001], reg_mem[12'h002],
          reg_mem[12'h003], reg_mem[12'h004], reg_mem[12'h005]);
      $swrite(temp_string,
          "%s</br>008: %h</br>009: %h</br>00A: %h</br>00B: %h</br>00C: %h</br>00D: %h</br>",
          temp_string,
          reg_mem[12'h008], reg_mem[12'h009], reg_mem[12'h00A],
          reg_mem[12'h00B], reg_mem[12'h00C], reg_mem[12'h00D]);
      `DISPLAY_LOGGER_MSG($sformatf(
          "refresh_config in UHSII_TRAN</br>%s", temp_string))
    `else // USE_LOGGERS
      $swrite(temp_string,
          "%s\n000: %h\n001: %h\n002: %h\n003: %h\n004: %h\n005: %h",
          temp_string,
          reg_mem[12'h000], reg_mem[12'h001], reg_mem[12'h002],
          reg_mem[12'h003], reg_mem[12'h004], reg_mem[12'h005]);
      $swrite(temp_string,
          "%s\n008: %h\n009: %h\n00A: %h\n00B: %h\n00C: %h\n00D: %h\n",
          temp_string,
          reg_mem[12'h008], reg_mem[12'h009], reg_mem[12'h00A],
          reg_mem[12'h00B], reg_mem[12'h00C], reg_mem[12'h00D]);
      `DISPLAY_LOGGER_MSG($sformatf(
          "refresh_config in UHSII_TRAN\n%s", temp_string))
      `endif // !USE_LOGGERS
    endfunction : refresh_config

    // -------------------------------------------------------------------- //

    // ***** LEGACY SD OPERATION *****

    local task process_transaction_sd(input  uhsii_req ureq,
                                      output uhsii_rsp ursp);
      uhsii_rsp_sd ursp_sd;
      sd_cmd cmd = new;
      sd_rsp rsp;
      sd_dat dat;

      cmd.app   = ureq.app;
      cmd.index = ureq.cmd_index;
      cmd.arg   = ureq.addr;
      
      this.error_gen_sem.get(1);
      if (error_gen.cmd_nak) begin
        sd_leg.enforce_none_rsp = `TRUE;
        error_gen.cmd_nak = `FALSE;
        `DISPLAY_LOGGER_NOTE("Error injection: NAK into SD CMD")
      end
      this.error_gen_sem.put(1);

      mbx_sd_cmd.put(cmd);
      mbx_sd_rsp.get(rsp);

      if (rsp == null || rsp.rsp_kind == NONE_RSP) begin
        ursp = respond_with_error(ureq, ECODE_COND_ERR);
        return;
      end
      else begin
        ursp_sd = new (ureq, ureq.cd ? data_mem : null);
      `ifdef USE_LOGGERS
        ursp_sd.init_logging(logger, log_id, hierarchy);
      `endif // USE_LOGGERS
        ureq.pld = rsp.contents;
  
        if (ureq.is_reset || ureq.is_stop_transf) begin
          ursp_sd.fsm_rst = `TRUE;
          if (curr_transf != null) begin
            curr_transf.stop_transf = `TRUE;
            if (ureq.is_reset)
              curr_transf.ebsy_expected = `FALSE;
          end
        end
  
        if (!ureq.app && ureq.cd && ureq.blm) begin
          if (ureq.cmd_index == 6'd17 || ureq.cmd_index == 6'd24)
            ursp_sd.req.tlen = 1;
          else if (ureq.cmd_index == 6'd53)
            ursp_sd.req.tlen = ureq.calc_sdio_tlen;
        end

        if (rsp.check_response_error_flag)
          ursp_sd.r1_r5_err = `TRUE;
        else if (ureq.cd) begin
          ursp_sd.n_fcu = reg_mem[12'h00C][15:8];
          if (ursp_sd.n_fcu == 0) ursp_sd.n_fcu = 256;
          if (ureq.blm)
            ursp_sd.blk_len = sd_leg.get_curr_blklen;
          else
            sd_leg.set_temp_blklen(ureq.tlen);
  
          curr_transf = ursp_sd;
          
          curr_transf.ebsy_expected = `TRUE;
          #3ns;
          ureq.rw  = ! mbx_dat_rd.try_peek(dat);
          
          if (ureq.rw)
            fork sd_tran_wr_dat_th; join_none
          else
            fork sd_tran_rd_dat_th; join_none
        end
        else if (ureq.cmd_index == 6'd38 && !ureq.app && !ureq.app) begin
          curr_transf = ursp_sd;
          fork
            begin
              ebsy_th_obj = process::self();
              curr_transf.ebsy_expected = `TRUE;
              curr_transf.transf_ended  = `TRUE;
              wait_for_ebsy;
              ebsy_th_obj = null;
            end
          join_none
        end
      end
      ursp = ursp_sd;
    endtask : process_transaction_sd

    // Waits for SD-Tran to finish operation, then sets flag which triggers sending EBSY
    local task wait_for_ebsy;
      sd_dat meta;
      while (!curr_transf.ebsy_reached && curr_transf.ebsy_expected) begin
        mbx_dat_rd.get(meta);
        curr_transf.ebsy_reached = (~meta.busy && meta.data.size == 0);
      end
    endtask : wait_for_ebsy

    // -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- //

    local task sd_tran_rd_dat_th;
      mem_blk tmp_blk;
      sd_dat dat;
      sd_cmd cnc;
      sd_rsp tmp;

      `DISPLAY_LOGGER_NOTE("Starting sd_tran_rd_dat_th")
      while (curr_transf.has_next_blk) begin
        mbx_dat_rd.get(dat);
        if (dat.data.size > 0) begin
          tmp_blk = new;
          tmp_blk.data = dat.data;
          curr_transf.put_rd_blk(tmp_blk);
        end
        curr_transf.transf_ended = dat.busy;
      end

      if (!curr_transf.transf_ended &&
          !curr_transf.stop_transf)
        wait (curr_transf.stop_transf ||
              curr_transf.transf_compl);

      if (curr_transf.req.tlen != -1 &&
          curr_transf.req.cmd_index != 6'd17 &&
          curr_transf.req.cmd_index != 6'd53 &&
          curr_transf.ebsy_expected &&
         !curr_transf.transf_ended &&
         !curr_transf.stop_transf) begin
        cnc = new;
        cnc.cancel_transf = `TRUE;                
        mbx_sd_cmd.put(cnc);
        mbx_sd_rsp.get(tmp);
      end
      wait_for_ebsy;
    endtask : sd_tran_rd_dat_th

    // -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- //

    local task sd_tran_wr_dat_th;
      mem_blk tmp_blk = null;
      sd_dat dat;
      sd_cmd cnc;
      sd_rsp tmp;
      
      `DISPLAY_LOGGER_NOTE("Starting sd_tran_wr_dat_th")
      while (curr_transf.has_next_blk ||
             curr_transf.has_next_wr_dat) begin
        curr_transf.get_wr_blk(tmp_blk);
        if (tmp_blk != null) begin
          dat = new(`FALSE, `TRUE, `FALSE);
          dat.data = tmp_blk.data;
          mbx_dat_wr.put(dat);
        end
        #1.5ns;
        while (mbx_dat_rd.try_get(dat))
          curr_transf.transf_ended = dat.busy;
      end

      if (!curr_transf.transf_ended &&
          !curr_transf.stop_transf)
        wait (curr_transf.stop_transf ||
              curr_transf.transf_compl);

      if (curr_transf.req.tlen != -1 &&
          curr_transf.req.cmd_index != 6'd24 &&
          curr_transf.req.cmd_index != 6'd53 &&
          curr_transf.ebsy_expected) begin
        cnc = new;
        cnc.cancel_transf = `TRUE;
        mbx_sd_cmd.put(cnc);
        mbx_sd_rsp.get(tmp);
      end
      wait_for_ebsy;
    endtask : sd_tran_wr_dat_th

    // -------------------------------------------------------------------- //

    local task execute_reset(output uhsii_rsp rsp);
      sd_cmd cnc;
      rsp = new (null, null);
      `DISPLAY_LOGGER_INFO("RESET in CM-TRAN")
      clear_and_copy_config;
      rsp.change_params = this.refresh_config;
      rsp.fsm_rst = `TRUE;
      own_node_id = 4'h0;
      if (curr_transf != null) begin
        curr_transf.stop_transf = `TRUE;
        curr_transf.ebsy_expected = `FALSE;
      end
      if (this.sd_leg != null) begin
        sd_cmd cnc = new;
        sd_rsp tmp;
        cnc.power_cycle = `TRUE;
        mbx_sd_cmd.put(cnc);
        mbx_sd_rsp.get(tmp);
      end
    endtask : execute_reset

  endclass : uhsii_tran_cl
endpackage : uhsii_tran_pkg

