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
//   UHS-II card model
//   
//   File contents  : package uhsii_card_pkg
//                    class   uhsii_card_cl                                  
//------------------------------------------------------------------------------

`timescale 1ns / 100ps

package uhsii_card_pkg;
`include "card_logging.svh"
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import card_echo_event_pkg::*;
  import sd_mem_pkg::*;
  import uhsii_pkt_pkg::*;
  import uhsii_link_pkg::*;
  import uhsii_tran_pkg::*;
  import sd_tok_pkg::*;
  import sd_card_pkg::*;
  import sdio_card_pkg::*;
  import datagen_pkg::*;

  class uhsii_card_cl extends component_cl;
    virtual uhsii_link_phy16_if.INTR pins;
    
    int                          rclk_pinit;

    local mailbox #(uhsii_req)   mbx_req;
    local mailbox #(uhsii_rsp)   mbx_rsp;

    local mailbox #(sd_cmd)      mbx_sd_cmd;
    local mailbox #(sd_rsp)      mbx_sd_rsp;
    local mailbox #(sd_dat)      mbx_dat_wr;
    local mailbox #(sd_dat)      mbx_dat_rd;
    local mailbox #(bit)         mbx_lvs;
    local mailbox #(bit)         mbx_intr;

    sd_mem_cl                    sd_mem;

    uhsii_link_cl                link;
    uhsii_tran_cl                cm_tran;
    sd_card_cl                   sd_leg;
    sdio_card_cl                 sdio_leg;
    
    local process                intr_signal_th_obj = null;
    
    local legacy_config_cl       card_conf;

    function new(input string                _name,
                 input component_cl          _parent,
                 input virtual
                 uhsii_link_phy16_if.INTR    _pins,
                 input mailbox #(uhsii_pkt)  mbx_tx,
                 input mailbox #(uhsii_pkt)  mbx_rx,
                 input uhsii_capabs_cl       card_capabs,
                 input bit                   sd_present,
                 input bit                   sdio_present,
                 input bit                   use_datagen);
      super.new(_name, _parent);
      this.pins     = _pins;
      mbx_req       = new;
      mbx_rsp       = new;
      
      sd_mem        = new("memory", this);

      if (sd_present | sdio_present) begin
        card_conf   = new (SDXC, legacy_config_cl::default_ocr_sd_leg);
        mbx_sd_cmd  = new(1);
        mbx_sd_rsp  = new(1);
        mbx_dat_wr  = new(1);
        mbx_dat_rd  = new(1);
      end
      else begin
        card_conf   = null;
        mbx_sd_cmd  = null;
        mbx_sd_rsp  = null;
        mbx_dat_wr  = null;
        mbx_dat_rd  = null;
      end
      
      if (sdio_present)
        mbx_intr = new (1);
      else
        mbx_intr = null;
      
      if (sdio_present) begin
        sd_leg = null;
        sdio_leg = new(sd_present ? "sd_tran+sdio" : "sdio", this,
                       mbx_sd_cmd, mbx_sd_rsp,
                       mbx_dat_rd, mbx_dat_wr, mbx_intr, mbx_lvs,
                       card_conf, sd_mem, `TRUE, sd_present, use_datagen);
      end
      else if (sd_present) begin
        sd_leg      = new("sd_tran",  this,
                          mbx_sd_cmd, mbx_sd_rsp,
                          mbx_dat_rd, mbx_dat_wr, mbx_lvs,
                          card_conf,  sd_mem, `TRUE, use_datagen);
        sdio_leg    = null;
      end
      else begin
        sd_leg      = null;
        sdio_leg    = null;
      end

      cm_tran       = new("cm_tran",  this,
                          mbx_req,    mbx_rsp,
                          sdio_leg != null ? sdio_leg : sd_leg,
                          mbx_sd_cmd, mbx_sd_rsp,
                          mbx_dat_wr, mbx_dat_rd,
                          sd_present, sdio_present,
                          sd_mem,     card_capabs);

      link          = new("link",     this,
                          mbx_tx,     mbx_rx,
                          mbx_rsp,    mbx_req,
                          cm_tran,
                          card_capabs == null ? `FALSE : card_capabs.no_delays);
    endfunction : new

    `CARD_LOGGING_UTILS

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `ifdef USE_LOGGERS
      cm_tran.init_logging(logger, log_id, this.get_hier_name);
      link.init_logging(logger, log_id, this.get_hier_name);
      if (sd_leg != null)
        sd_leg.init_logging(logger, log_id, this.get_hier_name);
      if (sdio_leg != null)
        sdio_leg.init_logging(logger, log_id, this.get_hier_name);
      `endif // USE_LOGGERS
    `INIT_LOGGING_SUBCOMPS_END
  

    task start;
      fork
        link.run;
        cm_tran.run;
        if (sd_leg != null)   sd_leg.run;
        if (sdio_leg != null) sdio_leg.run;
        intr_signal_th;
      join_none
    endtask : start
    
    local task intr_signal_th;
      if (this.sdio_leg != null) begin
        bit intr_signal_n  = `HIGH;
        intr_signal_th_obj = process::self();
        pins.intr_n <= intr_signal_n;

        forever begin
          mbx_intr.get(intr_signal_n);
          `DISPLAY_LOGGER_INFO($sformatf("Updated card interrupt signal -> %0b", intr_signal_n))
          pins.intr_n <= intr_signal_n;
        end
      end
    endtask : intr_signal_th
  
    function string get_class_name;
      return "uhsii_card_cl";
    endfunction : get_class_name

    function void dispose;
      if (sd_leg != null)   sd_leg.dispose;
      if (sdio_leg != null) sdio_leg.dispose;
      link.dispose;
      cm_tran.dispose;
      if (intr_signal_th_obj != null)
        intr_signal_th_obj.kill;
    endfunction : dispose

    function string to_string;
      if (this == null)
        return "null";
      else if (sd_leg != null)
        return $sformatf("UHS-II SDmem card seed=%h", sd_leg.random_seed);
      else if (sdio_leg != null)
        return $sformatf("UHS-II SDIO card seed=%h", sdio_leg.random_seed);
      else
        return "UHS-II NP-only card";
    endfunction : to_string

    function void init_datagen(input int             randgen_mode,
                               input int             blkcnt,
                               input int             blklen,
                               input int             seed,
                               input logic [7:0]     pattern[] = '{8'd0});
      if (sd_leg != null)
        this.sd_leg.init_datagen(randgen_mode, blkcnt, blklen, seed, pattern);
      else if (sdio_leg != null)
        this.sdio_leg.init_datagen(randgen_mode, blkcnt, blklen, seed, pattern);
      else begin
        no_sd_tran_error:
        assert (0) else begin
        `DISPLAY_LOGGER_ERROR("There is no SD-Tran")
        end
      end
    endfunction : init_datagen

    function void register_event_echo(
        input mailbox #(card_echo_event_cl) event_echo);
      link.register_event_echo(event_echo);
      if (sd_leg != null)
        sd_leg.register_event_echo(event_echo);
      else if (sdio_leg != null)
        sdio_leg.register_event_echo(event_echo);
    endfunction : register_event_echo
    
    function sdio_card_cl get_sdio_impl();
      return this.sdio_leg;
    endfunction : get_sdio_impl

  endclass : uhsii_card_cl
endpackage : uhsii_card_pkg
