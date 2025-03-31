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
//   SD 4.0 slot/card interface
//
//   File contents  : pakage sd_slot_pkg 
//                  : class  sd_slot_cl                                    
//------------------------------------------------------------------------------

package sd_slot_pkg;
  timeunit 1ns; timeprecision 100ps;

`include "sv_macros.svh"
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import sd_xtor_pkg::*;
  import sd_card_pkg::*;
  import sdio_card_pkg::*;
  import uhsii_xtor_pkg::*;
`ifdef CARD_COVER
  import uhsii_link_pkg::*;
`endif // CARD_COVER
  import uhsii_tran_pkg::*;
  import uhsii_card_pkg::*;
  import emmc_card_pkg::*;
  import datagen_pkg::*;
  import card_echo_event_pkg::*;
`ifdef CARD_COVER
  import cdns_sd4hc_legacy_pkg::*;
`endif // CARD_COVER

  virtual class abstract_slot_listener_cl;
    `PURE virtual function void
    register_sd_card(sd_xtor_cl xtor, sd_card_cl card);
    `ENDPUREFUNCTION
    `PURE virtual function void
    register_uhsii_card(uhsii_xtor_cl xtor, uhsii_card_cl card);
    `ENDPUREFUNCTION
  endclass : abstract_slot_listener_cl
  
  class sd_slot_cl extends
    `ifdef USE_LOGGERS
      active_log_component_cl;
    `else // USE_LOGGERS
      active_component_cl;
    `endif // !USE_LOGGERS
  
    virtual sd_4v00_if             sd_interface;
    virtual uhsii_link_phy16_if    uhsii_phy_interface;
    virtual uhsii_pkt_chk          uhsii_pkt_chk_if;

    local bit                      use_datagen;

    abstract_slot_listener_cl      slot_list;

    //logging
    local string                   log_id;
    local string                   slot;

    logic card_inserted;
    logic bounce_period;
    logic bounce_pattern;

    //fast simulation mode
    logic fast_timing;
    bit   use_uhsii;

    //cards models
    sd_xtor_cl sd_xtor;
    sd_card_cl sd_card;
  `ifdef CARD_COVER
    cdns_sd4hc_legacy_monitor legacy_monitor = null;
  `endif // CARD_COVER

    uhsii_xtor_cl uhsii_xtor;
    uhsii_card_cl uhsii_card;

    mailbox #(card_echo_event_cl) card_events = new(0);
    
  `ifdef CARD_COVER
    uhsii_retry_cover_cl       retry_cov;
    uhsii_crc_err_inj_cover_cl crc_err_inj_cov;
    sd_err_flag_cover_cl       err_flag_cov;
  `endif // CARD_COVER

    function new(
        input string                         _name = "sd_slot_cl",
        input string                         _slot,
        input component_cl                   _parent,
      `ifdef USE_LOGGERS
        input logger_cl                      _logger,
      `endif // USE_LOGGERS
        input virtual sd_4v00_if             _sd_interface,
        input virtual uhsii_link_phy16_if    _uhsii_phy_interface,
        input virtual uhsii_pkt_chk          _uhsii_pkt_chk,
        input bit                            _use_datagen = `TRUE);
      super.new(_name, _parent
        `ifdef USE_LOGGERS
          , _logger
        `endif // USE_LOGGERS
        );

      slot                  = _slot;
      sd_interface          = _sd_interface;
      uhsii_phy_interface   = _uhsii_phy_interface;
      uhsii_pkt_chk_if      = _uhsii_pkt_chk;
      use_datagen           = _use_datagen;
      card_inserted         = 1'b0;
      bounce_period         = 1'b0;
      bounce_pattern        = 1'b0;
      fast_timing           = 1'b1;
      sd_interface.sdwp_n_o = 1'bz;
      sd_interface.sdcd_n_o = 1'bz;
      slot_list             = null;
    `ifdef CARD_COVER
      retry_cov             = new;
      crc_err_inj_cov       = new;
      err_flag_cov          = new;
    `endif // CARD_COVER
    endfunction

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // get class name function for reports
    function string get_class_name();
      return "sd_slot_cl";
    endfunction : get_class_name

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // create subcomponnets
    protected function void make();
    endfunction : make

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // link subcomponnets
    protected function void link_up();
      assert (sd_interface!=null) else $fatal(1, 
        "sd_interface==null @sd_slot object, can't operate without valid sd slot interface assigned");
    endfunction : link_up

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // run component tasks
    protected task run();
    `ifdef USE_LOGGERS
      log_id = $sformatf("CARD_SLOT_%s", slot);
      assert(logger.new_report(log_id, "6",
          {"CARD SLOTS", $sformatf("CARD SLOT#%s",slot)},
          $sformatf("%s.html", log_id)) );

      logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
            "TB starts support for slot %s.", slot));
    `else // USE_LOGGERS
      $display ($psprintf("TB starts support for slot: %s", this.get_name));
    `endif // !USE_LOGGERS

      sd_interface.sdcd_n_o = 1'b1; //card removed
      fork 
        turn_uhsii_phy_off;
        turn_sdif_off;
        bounce_pattern_generator;
        sdcd_driver;
      join_none
    endtask : run

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // set real timing for bouncing 
    function void set_real_timing;
      fast_timing = 1'b0;
    endfunction : set_real_timing

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // disable phy if uhsii not used
    task turn_uhsii_phy_off;
      uhsii_phy_interface.mode <= 1'bZ;
      uhsii_phy_interface.nrst <= 1'b1;
      #5ns;
      uhsii_phy_interface.nrst <= 1'b0;
      #25ns;
      uhsii_phy_interface.tds  <= 2'b01; // OFF
      uhsii_phy_interface.tdrs <= 2'b01;
      uhsii_phy_interface.pinit_pcmd <= 4'bZZZZ;
      uhsii_phy_interface.intr_n <= 1'bZ;
    endtask : turn_uhsii_phy_off

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // output Z's on sd_if if no SD legacy/UHS-I card is used
    task turn_sdif_off;
      sd_interface.cmd_o <= 1'bZ;
      sd_interface.dat_o <= 8'hZZ;
    endtask : turn_sdif_off

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // inserting card
     task insert_card(bit                 uhsii,
                      bit                 sdio,
                      legacy_config_cl    legacy_card_conf,
                      uhsii_capabs_cl     uhsii_card_capabs,
                      string              name = "",
                      bit                 write_protect,
                      int                 fastest_out_delay,
                      int                 fastest_out_window);
      bit legacy_monitor_active = 0;
      sd_interface.card_removed <= 1'b0;
      if (sd_xtor != null || uhsii_xtor != null) begin
        this.remove_card;
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), WARNING, this.get_hier_name,
      `else // USE_LOGGERS
        $display (
      `endif // !USE_LOGGERS
          "The previous card was not removed from the slot before a new card was insterted in it!");
        #8ns;
      end

      if (uhsii) begin
        uhsii_xtor = new({"uhsii_xtor",name}, null, uhsii_phy_interface, 1'b1);
        uhsii_card = new({"uhsii_card",name}, null, uhsii_phy_interface,
                          uhsii_xtor.mbx_tx, uhsii_xtor.mbx_rx, uhsii_card_capabs, ~sdio, sdio, use_datagen);
                                                              // no combo cards! ~~ ^^^ ~~
        // Adding the SD legacy monitor shouldn't be needed here but
        // functional coverage metrics had "conflict" items when this monitor
        // wasn't instantiated.
        `ifdef CARD_COVER
        if (legacy_monitor == null)
          legacy_monitor = new({"cdns_sd4hc_legacy_monitor_",name}, "unused", this, logger, 0);
        `endif // CARD_COVER
        uhsii_xtor.add_pkt_echo_if(uhsii_pkt_chk_if);
        if (this.card_events != null)
          uhsii_card.register_event_echo(this.card_events);
        if (slot_list != null)
          slot_list.register_uhsii_card(uhsii_xtor, uhsii_card);
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
            "%s inserted in %s", uhsii_card.to_string, slot));
        uhsii_xtor.init_logging(logger, log_id, this.get_hier_name);
        uhsii_card.init_logging(logger, log_id, this.get_hier_name);
      `endif // USE_LOGGERS
      `ifdef CARD_COVER
        uhsii_card.link.set_uhsii_card_covergroups(this.retry_cov, this.crc_err_inj_cov);
        if (uhsii_card.sd_leg != null)
          uhsii_card.sd_leg.set_legacy_card_covergroups(this.err_flag_cov);
        else if (uhsii_card.sdio_leg != null)
          uhsii_card.sdio_leg.set_legacy_card_covergroups(this.err_flag_cov);
      `endif // CARD_COVER
        uhsii_xtor.start;
        uhsii_card.start;
      end
      else begin
        if (legacy_card_conf.card_cap == EMMC_BYTE || legacy_card_conf.card_cap == EMMC_SECTOR) begin
          emmc_card_cl emmc_card;
          sd_xtor = new({"sd_xtor_",name}, null, sd_interface, `TRUE, `FALSE);
        `ifdef CARD_COVER
          if (legacy_monitor == null)
            legacy_monitor = new({"cdns_sd4hc_legacy_monitor_",name}, $psprintf("cdns_sd4hc_legacy_monitor_slot%0d",slot), this, logger, 1);
          else
            legacy_monitor.new_logger({"cdns_sd4hc_legacy_monitor_",name});
          legacy_monitor_active = 1;
        `endif // CARD_COVER
          emmc_card = new 
              ({"emmc_",name}, null,
                 sd_xtor.mbx_cmd,     sd_xtor.mbx_rsp,
                 sd_xtor.mbx_dat_rd,  sd_xtor.mbx_dat_wr,
                 legacy_card_conf,    use_datagen);
          sd_card = emmc_card;
        end
        else if (sdio) begin
          sdio_card_cl sdio_card;
          sd_xtor = new({"sdio_xtor_",name}, null, sd_interface,`FALSE, `TRUE);
          `ifdef CARD_COVER
          if (legacy_monitor == null)
            legacy_monitor = new({"cdns_sd4hc_legacy_monitor_",name}, $psprintf("cdns_sd4hc_legacy_monitor_slot%0d",slot), this, logger, 0);
          else
            legacy_monitor.new_logger({"cdns_sd4hc_legacy_monitor_",name});
          legacy_monitor_active = 1;
          `endif // CARD_COVER
          sdio_card = new
              ({"sdio_card_",name},   null,
                 sd_xtor.mbx_cmd,     sd_xtor.mbx_rsp,
                 sd_xtor.mbx_dat_rd,  sd_xtor.mbx_dat_wr,
                 sd_xtor.mbx_intr,    sd_xtor.mbx_lvs,
                 legacy_card_conf,
                 null, `FALSE, `FALSE, use_datagen);
          sd_card = sdio_card;
        end
        else begin
          sd_xtor = new({"sd_xtor_",name}, null, sd_interface, `FALSE, `FALSE);
        `ifdef CARD_COVER
          if (legacy_monitor == null)
            legacy_monitor = new({"cdns_sd4hc_legacy_monitor_",name}, $psprintf("cdns_sd4hc_legacy_monitor_slot%0d",slot), this, logger);
          else
            legacy_monitor.new_logger({"cdns_sd4hc_legacy_monitor_",name});
          legacy_monitor_active = 1;
        `endif // CARD_COVER
          sd_card = new
              ({"sd_card_",name},     null,
                 sd_xtor.mbx_cmd,     sd_xtor.mbx_rsp,
                 sd_xtor.mbx_dat_rd,  sd_xtor.mbx_dat_wr, sd_xtor.mbx_lvs,
                 legacy_card_conf,    null, `FALSE, use_datagen);
        end
        sd_xtor.set_fastest_speed_out_delay( fastest_out_delay, fastest_out_delay); //set SDR104/HS200 ODLY time
        sd_xtor.set_fastest_speed_out_window(fastest_out_window,fastest_out_window);//set SDR104/HS200 data window time
        if (this.card_events != null)
          sd_card.register_event_echo(this.card_events);
        if (slot_list != null)
          slot_list.register_sd_card(sd_xtor, sd_card);
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
            "%s inserted in %s", sd_card.to_string, slot));
        sd_xtor.init_logging(logger, log_id, this.get_hier_name);
        sd_card.init_logging(logger, log_id, this.get_hier_name);
      `endif // USE_LOGGERS
        sd_xtor.start;
        sd_card.start;
      `ifdef CARD_COVER
        sd_card.set_legacy_card_covergroups(this.err_flag_cov);
        if (legacy_monitor != null && legacy_monitor_active) begin
          legacy_monitor.vif = sd_interface;
          legacy_monitor.run_phase();
        end
      `endif // CARD_COVER
      end
      use_uhsii = uhsii;
      card_inserted = 1'b1;
      sd_interface.sdwp_n_o = ~write_protect;
      sd_interface.check_emmc <= (legacy_card_conf == null ? `FALSE :
                                       (legacy_card_conf.card_cap == EMMC_BYTE ||
                                        legacy_card_conf.card_cap == EMMC_SECTOR) );
    endtask : insert_card

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // remove card 
    task remove_card();
      sd_interface.card_removed <= 1'b1;
      #25ns;
      if (sd_xtor != null) begin
        sd_card.register_event_echo(null);
        if (slot_list != null)
         slot_list.register_sd_card(null, null);
        sd_xtor.dispose;
        if (sd_card != null)
          sd_card.dispose;
        turn_sdif_off;
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
      `else // USE_LOGGERS
        $display($sformatf(
      `endif // !USE_LOGGERS
            "%s removed from %s", sd_card.to_string, slot));
      
      end
      if (uhsii_xtor != null) begin
        uhsii_card.register_event_echo(null);
        if (slot_list != null)
         slot_list.register_uhsii_card(null, null);
        uhsii_xtor.dispose;
        if (uhsii_card != null)
          uhsii_card.dispose;
        turn_uhsii_phy_off;
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
      `else // USE_LOGGERS
        $display($sformatf(
      `endif // !USE_LOGGERS
            "%s removed from %s", uhsii_card.to_string, slot));
      end
    `ifdef CARD_COVER
      if (legacy_monitor != null)
         legacy_monitor.dispose();
    `endif // CARD_COVER
      uhsii_xtor = null;
      uhsii_card = null;
      sd_xtor = null;
      sd_card = null;
    `ifdef CARD_COVER
//      legacy_monitor = null;
    `endif // CARD_COVER
      use_uhsii = 1'b0;
      card_inserted = 1'b0;
      sd_interface.sdwp_n_o = 1'bz;
    endtask : remove_card
    
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // tries to get SDIO entity if present in the slot (SDIO card with legacy IF or SDIO residing upon SD-TRAN in UHS-II card)
    local function sdio_card_cl get_sdio_entity;
      sdio_card_cl sdio_card = null;

      if (uhsii_xtor != null && uhsii_card != null)
        sdio_card = uhsii_card.get_sdio_impl;
      else if (sd_xtor != null && sd_card != null) begin
        if (! $cast(sdio_card, sd_card) )
          sdio_card = null;
      end
      
      return sdio_card;
    endfunction : get_sdio_entity
    
    
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // schedules an interrupt to be reported by function 'func' after 'delay'
    // (to enforce interrupt factor in card)
    function void schedule_interrupt_generation (input bit [2:0] func, input int delay_in_ns);
      sdio_card_cl sdio_card = get_sdio_entity;

      if (sdio_card != null) begin
        sdio_card.schedule_interrupt_generation(func, delay_in_ns);
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), NOTE, this.get_hier_name, $sformatf(
      `else // USE_LOGGERS
        $display($sformatf(
      `endif // !USE_LOGGERS
          "SDIO interrupt scheduled in the card model: slot=%s func=%0d delay=%0dns", slot, func, delay_in_ns));
      end
      else begin
        no_sdio_card_in_slot: assert (0) else
      `ifdef USE_LOGGERS
        logger.message(stoq(log_id), ERROR, this.get_hier_name, $sformatf(
      `else // USE_LOGGERS
        $error($sformatf(
      `endif // !USE_LOGGERS
          "No card currently in slot %s or the card is not an SDIO card", slot));
      end
    endfunction : schedule_interrupt_generation
    
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // schedules clear of all the interrupts reported IO functions after 'delay'
    // (for debug purposes only)
    function void schedule_interrupt_suppression(input int delay_in_ns);
      sdio_card_cl sdio_card = get_sdio_entity;
      
      if (sdio_card != null)
        sdio_card.schedule_interrupt_suppression(delay_in_ns);
    endfunction
    
    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    function bit is_card_in_slot;
      return (this.sd_xtor != null && this.sd_card != null) || (this.uhsii_xtor != null && this.uhsii_card != null);
    endfunction : is_card_in_slot

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // makes slot behave as if card was inserted or removed (for operation with external card models)
    task set_external_card(input bit insert, input bit write_protect, input bit emmc_mode);
      assert (! card_inserted)
      else $error ("Cannot set external card model due to card present in the slot");
      sd_interface.card_removed <= ~insert;
      sd_interface.sdcd_n_o = ~insert;
      sd_interface.sdwp_n_o =  insert ? ~write_protect : 1'bz;
      sd_interface.check_emmc <= emmc_mode;
    endtask

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // inserting card 
    task program_card_datagen (input int rm, int bcnt, int dtbs, bit [31:0] datagen_seed);
      if (use_uhsii) begin
        assert (uhsii_card!=null) uhsii_card.init_datagen(rm,bcnt,dtbs,datagen_seed);
        else                      $fatal(1,"Attempt to programm card data generator in empty SD slot");
      end else begin
        assert (sd_card!=null)    sd_card.init_datagen(rm,bcnt,dtbs,datagen_seed);  
        else                      $fatal(1,"Attempt to programm card data generator in empty SD slot");
      end
    endtask : program_card_datagen

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // card insert / remove pattern generator 
     task bounce_pattern_generator;
      //card detection pin debpune time 
      time card_detect_bounce_time;
      time sdcd_n_bounce;

      forever begin
        // wait card inserted / card removed time 
        @(card_inserted); 
        
        bounce_period = 1'b1;
        //randomize debounce period
        if (fast_timing) card_detect_bounce_time = $urandom_range(0,1000)*1ns;
        else             card_detect_bounce_time = $urandom_range(0,10)*1ms;
        fork
          //simulate pin connector bouncing behavior
          fork
            #card_detect_bounce_time;
            while (bounce_period) begin
              bounce_pattern=~bounce_pattern;
              if (fast_timing) sdcd_n_bounce=$urandom_range( 1, 50)*1ns;
              else             sdcd_n_bounce=$urandom_range(10,500)*1us;
              #sdcd_n_bounce;
            end
          join_any 
          disable fork;
          bounce_pattern = 1'b0;
        join
        // end of debouncing period
        bounce_period = 1'b0;
      end
    endtask : bounce_pattern_generator

    //!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // card insert / remove pattern mixer 
    task sdcd_driver;
      forever begin
        @(bounce_pattern or card_inserted or bounce_period);
        if (bounce_period) sd_interface.sdcd_n_o = bounce_pattern;   // apply debounce pattern in bounce period
        else               sd_interface.sdcd_n_o = ~card_inserted;   // inster/remove card after bounce period
      end
      forever begin
      #1000;
      end
    endtask :  sdcd_driver

  endclass : sd_slot_cl
endpackage : sd_slot_pkg
