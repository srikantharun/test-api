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
//   SD UHS-II Transactor
//   
//   File contents  : package uhsii_xtor_pkg 
//                    class  uhsii_xtor_cl                                   
//------------------------------------------------------------------------------

`timescale 1ns / 100ps 

package uhsii_xtor_pkg;
`include "card_logging.svh"
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import uhsii_pkt_pkg::*;
  import uhsii_params_pkg::*;

  class uhsii_xtor_cl extends component_cl;

    static const int sync_delay = 4;

    virtual uhsii_link_phy16_if.LINK    phy_bus;
    virtual uhsii_pkt_chk.PUT_PKT       pkt_echo = null;
    mailbox #(uhsii_pkt)                mbx_tx;
    mailbox #(uhsii_pkt)                mbx_rx;
    local bit                           is_card,
                                        is_host;

    local uhsii_pkt                     pkt_tx, 
                                        pkt_rx;

    local event                         phy_deact_ev,
                                        phy_reset_ev;

    local process                       reset_th_obj = null,
                                        phy_init_th_obj = null,
                                        tx_main_th_obj = null,
                                        rx_main_th_obj = null;

    // for error generation in card

    struct {
      bit single_sdb;
      bit single_edb;
      bit double_sdb;
      bit double_edb;

      bit lidl;
      bit didl;
      bit dir;
      bit syn;
    } error_gen;

    semaphore error_gen_sem;

    function new(input string               _name,
                 input component_cl         _parent,
                 input virtual
                 uhsii_link_phy16_if.LINK   _phy_bus,
                 input int                  is_device);
      super.new(_name, _parent);
      this.phy_bus       =  _phy_bus;
      this.mbx_tx        =  new(2);
      this.mbx_rx        =  new(5);

      this.is_card       = (is_device == 1);
      this.is_host       = (is_device == 0);

      this.lss_params    = null;

      this.error_gen_sem = new (1);

      assert (is_device == 0 || is_device == 1)
      else $fatal (1, "param DEVICE shall be equal 0 or 1.");
    endfunction : new

    task start;
      fork
        run;
      join_none
    endtask : start
  
    function string get_class_name;
      return "sd_card_cl";
    endfunction : get_class_name

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    task run();
      initialize;
      fork
        reset_th;
        phy_init_th;
        tx_main_th;
        rx_main_th;
      join_none
    endtask : run

    function void dispose;
      if (pkt_echo != null)
        fork pkt_echo.reset_checker; join_none
      if (reset_th_obj != null)
        reset_th_obj.kill;
      if (phy_init_th_obj != null)
          phy_init_th_obj.kill;
      if (tx_main_th_obj != null)
        tx_main_th_obj.kill;
      if (rx_main_th_obj != null)
        rx_main_th_obj.kill;
    endfunction : dispose
  
    // -----------------------------------------------------------------------
    // XTOR INTERNAL STATE
    // -----------------------------------------------------------------------

    const bit   scrambler_on =  `TRUE;

    int         lss_cntr = 0;
    int         sync_cntr = 0;
    int         pkt_rx_delay = 0;
  
    typedef enum {
      // FD
      EIDL_TX_ST,
      STBL_TX_ST,
      SYN_TX_ST,
      BSYN_TX_ST,
  
      LIDL_TX_ST,
      DIDL_TX_ST,
  
      PKT_INIT_TX_ST,
      PKT_DATA_TX_ST,
      PKT_FINAL_TX_ST,

      STBH_TX_ST,

      // 2L-HD out
      WAIT_ENTER_2LHD_OUT_TX_ST,
      ENTER_2LHD_OUT_TX_ST,
      PREAMBLE_2LHD_OUT_TX_ST,
      SYNC_2LHD_OUT_TX_ST,

      PKT_2L_INIT_TX_ST,
      PKT_2L_DATA_TX_ST,
      PKT_2L_FINAL_TX_ST,

      DIDL_2L_TX_ST,

      POSTAMBLE_2LHD_OUT_TX_ST,
      EXIT_2LHD_OUT_TX_ST,
      DIR_TX_ST,

      // 2L-HD in
      ENTER_2LHD_IN_TX_ST,
  
      OFF_TX_ST,

      WAIT_EXIT_2LHD_IN_TX_ST,
      EXIT_2LHD_IN_TX_ST,

      WAIT_DIR_TX_ST
    } tx_st_e;

    typedef enum {
      EIDL_RX_ST,
      STBL_RX_ST,
      SYN_RX_ST,
      BSYN_RX_ST,
      DIR_RX_ST,
      VLD_RX_ST,
      PKT_RX_ST,
      VLD_2L_RX_ST,
      PKT_2L_RX_ST,
      STBH_RX_ST,
      OFF_RX_ST
    } rx_st_e;

    tx_st_e tx_st = EIDL_TX_ST;
    rx_st_e rx_st = EIDL_RX_ST;

    lss_params_cl lss_params;

    bit         didl_tx          = `FALSE; // 1 when to transmit DIDL instead of LIDL
    bit         go2dormant       = `FALSE;
    bit         go4reset         = `FALSE;
    bit         rx2lhd           = `FALSE;
    bit         active           = `FALSE; // set 1 upon first LIDL reception, set 0 upon reset
    bit         fast_lpm         = `FALSE; // set 1 upon first EIDL transmission (due to LPM)
    bit         pcmd_acked       = `FALSE;

    bit         curr_pkt_rx_sdb  = `FALSE;
    bit [8:0]   data_rx[$] = {}, data_rx_odd[$] = {},
                data_tx[$] = {}, data_tx_odd[$] = {};

    // -----------------------------------------------------------------------
    // XTOR INTERNAL METHODS
    // -----------------------------------------------------------------------

    // ***** PASSING PARAMS TO CHECKERS *****

    local task drive_params_bus;
      phy_bus.n_lss_dir    <= lss_params.n_lss_dir;
      phy_bus.n_lss_syn    <= lss_params.n_lss_syn;
      phy_bus.n_data_gap   <= lss_params.n_data_gap;
      phy_bus.lpm          <= lss_params.lpm;
      phy_bus.active       <= this.active;
      phy_bus.go4reset     <= this.go4reset;
      phy_bus.go2dormant   <= this.go2dormant;
    endtask : drive_params_bus

    // ***** SENDING LSSES *****

    local task send_off;
      phy_bus.tds <= PLSM_RXTX_OFF;
      phy_bus.tdm <= '0;
      phy_bus.td  <= '0;
      lss_cntr    += 2;
    endtask : send_off

    local task send_off_odd;
      phy_bus.tdrs <= PLSM_RXTX_OFF;
      phy_bus.tdrm <= '0;
      phy_bus.tdr  <= '0;
    endtask : send_off_odd

    local task send_eidl;
      phy_bus.tds <= PLSM_RXTX_EIDL;
      phy_bus.tdm <= '0;
      phy_bus.td  <= '0;
      lss_cntr    += 2;
    endtask : send_eidl

    local task send_stbl;
      phy_bus.tds <= PLSM_RXTX_STB;
      phy_bus.tdm <= '0;
      phy_bus.td  <= '0;
      lss_cntr    += 2;
    endtask : send_stbl

    local task send_stbl_odd;
      phy_bus.tdrs <= PLSM_RXTX_STB;
      phy_bus.tdrm <= '0;
      phy_bus.tdr  <= '0;
    endtask : send_stbl_odd

    local task send_stbh;
      phy_bus.tds <= PLSM_RXTX_STB;
      phy_bus.tdm <= '1;
      phy_bus.td  <= '1;
      lss_cntr    += 2;
    endtask : send_stbh

    local task send_stbh_odd;
      phy_bus.tdrs <= PLSM_RXTX_STB;
      phy_bus.tdrm <= '1;
      phy_bus.tdr  <= '1;
    endtask

    local task send_com_lss(bit both_lanes = `FALSE);
      phy_bus.tds        <= PLSM_RXTX_VLD;
      phy_bus.tdm[0]     <= LSS_COM_M;
      phy_bus.td[7:0]    <= LSS_COM;
      lss_cntr           += 1;

      if (both_lanes) begin
        phy_bus.tdrs       <= PLSM_RXTX_VLD;
        phy_bus.tdrm[0]    <= LSS_COM_M;
        phy_bus.tdr[7:0]   <= LSS_COM;
      end
    endtask : send_com_lss

    local task send_plain_syn_lss;
      send_com_lss;
      if ($urandom() % 2) begin
        phy_bus.tdm[1]   <= LSS_SYN0_M;
        phy_bus.td[15:8] <= LSS_SYN0;
      end
      else begin
        phy_bus.tdm[1]   <= LSS_SYN1_M;
        phy_bus.td[15:8] <= LSS_SYN1;
      end
    endtask : send_plain_syn_lss

    local task send_boot_syn_lss;
      send_com_lss;
      if ($urandom() % 2) begin
        phy_bus.tdm[1]    <= LSS_BSYN0_M;
        phy_bus.td[15:8]  <= LSS_BSYN0;
      end
      else begin
        phy_bus.tdm[1]    <= LSS_BSYN1_M;
        phy_bus.td[15:8]  <= LSS_BSYN1;
      end
    endtask : send_boot_syn_lss

    local task send_lidl_lss;
      send_com_lss;
      if ($urandom() % 2) begin
        phy_bus.tdm[1]    <= LSS_LIDL0_M;
        phy_bus.td[15:8]  <= LSS_LIDL0;
      end
      else begin
        phy_bus.tdm[1]    <= LSS_LIDL1_M;
        phy_bus.td[15:8]  <= LSS_LIDL1;
      end
    endtask : send_lidl_lss

    local task send_didl_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      if ($urandom() % 2) begin
        phy_bus.tdm[1]    <= LSS_DIDL0_M;
        phy_bus.td[15:8]  <= LSS_DIDL0;
      end
      else begin
        phy_bus.tdm[1]    <= LSS_DIDL1_M;
        phy_bus.td[15:8]  <= LSS_DIDL1;
      end
  
      if (both_lanes) begin
        if ($urandom() % 2) begin
          phy_bus.tdrm[1]    <= LSS_DIDL0_M;
          phy_bus.tdr[15:8]  <= LSS_DIDL0;
        end
        else begin
          phy_bus.tdrm[1]    <= LSS_DIDL1_M;
          phy_bus.tdr[15:8]  <= LSS_DIDL1;
        end
      end
    endtask : send_didl_lss
  
    local task send_dir_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      phy_bus.tdm[1]   <= LSS_DIR_M;
      phy_bus.td[15:8] <= LSS_DIR;
  
      if (both_lanes) begin
        phy_bus.tdrm[1]    <= LSS_DIR_M;
        phy_bus.tdr[15:8]  <= LSS_DIR;
      end
    endtask : send_dir_lss

    // ----------------------
  
    local task send_sdb_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      phy_bus.tdm[1]   <= LSS_SDB_M;
      phy_bus.td[15:8] <= LSS_SDB;
      if (both_lanes) begin
        phy_bus.tdrm[1]    <= LSS_SDB_M;
        phy_bus.tdr[15:8]  <= LSS_SDB;
      end
    endtask : send_sdb_lss

    local task send_sop_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      phy_bus.tdm[1]   <= LSS_SOP_M;
      phy_bus.td[15:8] <= LSS_SOP;
      if (both_lanes) begin
        phy_bus.tdrm[1]    <= LSS_SOP_M;
        phy_bus.tdr[15:8]  <= LSS_SOP;
      end
    endtask : send_sop_lss

    local task send_eop_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      phy_bus.tdm[1]   <= LSS_EOP_M;
      phy_bus.td[15:8] <= LSS_EOP;
      if (both_lanes) begin
        phy_bus.tdrm[1]    <= LSS_EOP_M;
        phy_bus.tdr[15:8]  <= LSS_EOP;
      end
    endtask : send_eop_lss

    local task send_edb_lss(bit both_lanes = `FALSE);
      send_com_lss(both_lanes);
      phy_bus.tdm[1]   <= LSS_EDB_M;
      phy_bus.td[15:8] <= LSS_EDB;
      if (both_lanes) begin
        phy_bus.tdrm[1]    <= LSS_EDB_M;
        phy_bus.tdr[15:8]  <= LSS_EDB;
      end
    endtask : send_edb_lss

    // ***** SENDING PKTS *****

    local task check_new_pkt;
      if (pkt_tx == null && mbx_tx.num() > 0) begin
        mbx_tx.get(pkt_tx);
        if (pkt_tx != null) begin
          this.go2dormant = pkt_tx.go2dormant;
          this.go4reset   = pkt_tx.go4reset;

          if (pkt_tx.change_params != null) begin
            this.lss_params = pkt_tx.change_params;
            if (is_card)
              `DISPLAY_LOGGER_NOTE($sformatf(
                  "LSS params changed in XTOR: %s %s",
                  this.lss_params.to_string,
                  tx_st.name))
          end

          if (pkt_tx.go2dormant || pkt_tx.go4reset ||
              pkt_tx.change_params != null)
            drive_params_bus;
  
          if (pkt_tx.switch2didl)
            this.didl_tx = `TRUE;
          else if (pkt_tx.switch2lidl)
            this.didl_tx = `FALSE;
  
          // now ignore meta-only pkts
          if (pkt_tx.pkt_type == META_PKT) begin
            if (pkt_echo != null)
              pkt_echo.put_tx(pkt_tx);
            pkt_tx = null;
          end
        end
      end
    endtask : check_new_pkt

    local task send_pkt_init(bit both_lanes = `FALSE);
      assert (pkt_tx != null)
      else $fatal(1, "XTOR internal error");

      if (pkt_tx.sdb && lss_cntr < 2) begin
        send_sdb_lss(both_lanes);
        inject_sdb_error;
      end
      else begin
        send_sop_lss(both_lanes);
        tx_st = both_lanes ? PKT_2L_DATA_TX_ST : PKT_DATA_TX_ST;
        if (pkt_tx.pkt_dir == INCOMING)
          // pkt is bypassed, no need to encode
          pkt_tx.pkt_dir = OUTGOING;
        else begin
          pkt_tx.encode_pkt;
          pkt_tx.add_crc;
        end
        //calculates also db error, must operate on encoded pkt:
        inject_sop_error;
        if (is_card)
          `DISPLAY_LOGGER_MSG(pkt_tx.to_string)
        pkt_tx.put_send_data(data_tx, scrambler_on);
        if (pkt_tx.odd_data_pkt != null)
          pkt_tx.odd_data_pkt.put_send_data(
            data_tx_odd, scrambler_on);
      end
    endtask : send_pkt_init

    // *** *** ***

    local task send_pkt_data(bit both_lanes = `FALSE);
      send_pkt_data_1lane(data_tx, `FALSE);
      if (both_lanes)
        send_pkt_data_1lane(data_tx_odd, `TRUE);
      else
        send_off_odd;
      inject_payload_error;

      if (data_tx.size == 0 || (both_lanes && data_tx_odd.size == 0)) begin
        tx_st = both_lanes ? PKT_2L_FINAL_TX_ST : PKT_FINAL_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_pkt_data
  
    local task send_pkt_data_1lane(ref bit [8:0] data[$],
                                   input bit     odd = `FALSE);
      logic [8:0] temp_data[2];
      int size = data.size;
      if (data.size < 2) begin
        `DISPLAY_LOGGER_WARNING("not enough data to send in XTOR, two bytes needed")
        if (data.size == 1) begin
          temp_data[0] = data.pop_front;
          temp_data[1] = 9'hXXX; // this should never happen
        end
      end
      else begin
        temp_data[0] = data.pop_front;
        temp_data[1] = data.pop_front;
      end

      if (odd) begin
        phy_bus.tdrs        <= PLSM_RXTX_VLD;
        phy_bus.tdrm[0]     <= temp_data[0][8];
        phy_bus.tdr [7:0]   <= temp_data[0][7:0];
        phy_bus.tdrm[1]     <= temp_data[1][8];
        phy_bus.tdr [15:8]  <= temp_data[1][7:0];
      end
      else begin
        phy_bus.tds         <= PLSM_RXTX_VLD;
        phy_bus.tdm[0]      <= temp_data[0][8];
        phy_bus.td [7:0]    <= temp_data[0][7:0];
        phy_bus.tdm[1]      <= temp_data[1][8];
        phy_bus.td [15:8]   <= temp_data[1][7:0];
      end
    endtask : send_pkt_data_1lane

    // *** *** ***

    local task send_pkt_final(bit both_lanes = `FALSE);
      bit immediately =  pkt_tx.repeat_msg;

      if (lss_cntr == 0) begin
        send_eop_lss(both_lanes);
        inject_eop_error;
      end
      else begin // pkt_tx.edb
        send_edb_lss(both_lanes);
        inject_edb_error;
      end

      if (lss_cntr == 3 || ! pkt_tx.edb) begin
        if (pkt_tx.init_2lhd_in)
          this.rx2lhd = `TRUE;
        if (scrambler_on) pkt_tx.scramble; // descrambles again for later reference
        if (pkt_echo != null)
          pkt_echo.put_tx(pkt_tx);
        pkt_tx.sent = `TRUE;
        pkt_tx = null;
        lss_cntr = 0;          
        
        if ((didl_tx & !rx2lhd) | immediately)
          check_new_pkt;
         
        tx_st =
          rx2lhd ?
            STBH_TX_ST :
            both_lanes ?
            // didl_tx=1 here guaranteed
              (pkt_tx == null ?
                POSTAMBLE_2LHD_OUT_TX_ST :
                lss_params.n_data_gap == 0 ?
                  PKT_2L_INIT_TX_ST :
                  DIDL_2L_TX_ST) :
              (didl_tx & !immediately) ?
                (pkt_tx != null && lss_params.n_data_gap == 0 ?
                  PKT_INIT_TX_ST :
                  DIDL_TX_ST) :
                (pkt_tx != null && immediately ?
                  PKT_INIT_TX_ST :
                  fast_lpm ?
                    STBH_TX_ST :
                    LIDL_TX_ST);
      end
    endtask : send_pkt_final

    // ----- 2L-HD OUT -----

    local task send_wait_enter_2lhd_out;
      send_didl_lss;
      inject_didl_error;
      send_off_odd;
      if (lss_cntr > T_DIR_SWITCH/2) begin
        tx_st = ENTER_2LHD_OUT_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_wait_enter_2lhd_out

    local task send_enter_2lhd_out;
      send_dir_lss;
      send_off_odd;
      inject_dir_error;
      if (lss_cntr == 1)
        phy_bus.pinit_pcmd <= PCMD_ENTER_2L_HDOUT;
      else if (phy_bus.pack) begin
        phy_bus.pinit_pcmd <= PCMD_NO_COMMAND;
        tx_st = PREAMBLE_2LHD_OUT_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_enter_2lhd_out

    local task send_preamble_2lhd_out;
      send_dir_lss;
      send_stbl_odd;
      inject_dir_error;
      if (lss_cntr >= T_EIDL_RECOVERY) begin
        tx_st = SYNC_2LHD_OUT_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_preamble_2lhd_out

    local task send_sync_2lhd_out;
      send_dir_lss(`TRUE);
      inject_dir_error;
      if (lss_cntr >= lss_params.n_lss_dir) begin
        tx_st = PKT_2L_INIT_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_sync_2lhd_out

    local task send_postamble_2lhd_out;
      send_dir_lss;
      send_stbh_odd;
      inject_dir_error;
      if (lss_cntr >= T_EIDL_ENTRY/2) begin
        tx_st = EXIT_2LHD_OUT_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_postamble_2lhd_out

    local task send_exit_2lhd_out;
      send_dir_lss;
      send_off_odd;
      inject_dir_error;
      if (lss_cntr == 1)
        phy_bus.pinit_pcmd <= PCMD_EXIT_2L_HD;
      else if (phy_bus.pack) begin
        phy_bus.pinit_pcmd <= PCMD_NO_COMMAND;
        tx_st = WAIT_DIR_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_exit_2lhd_out

    // ----- 2L-HD IN -----

    local task send_enter_2lhd_in;
      send_off;
      if (lss_cntr == 2)
        phy_bus.pinit_pcmd <= PCMD_ENTER_2L_HDIN;
      else if (phy_bus.pack) begin
        phy_bus.pinit_pcmd <= PCMD_NO_COMMAND;
        tx_st = OFF_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_enter_2lhd_in

    local task send_wait_exit_2lhd_in;
      send_off;
      if (lss_cntr >= T_DIR_SWITCH) begin
        tx_st = EXIT_2LHD_IN_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_wait_exit_2lhd_in

    local task send_exit_2lhd_in;
      send_off;
      if (lss_cntr == 2)
        phy_bus.pinit_pcmd <= PCMD_EXIT_2L_HD;
      else if (phy_bus.pack) begin
        phy_bus.pinit_pcmd <= PCMD_NO_COMMAND;
        tx_st = STBL_TX_ST;
        lss_cntr = 0;
      end
    endtask : send_exit_2lhd_in

    // ----- ERRORS GENERATION -----

    `define INJECT_PHY_ERROR this.phy_bus.force_err <= `HIGH;
    `define INJECT_PHY_NO_ERR this.phy_bus.force_err <= `LOW;

    local task inject_sdb_error;
      if (lss_cntr == 1)
        error_gen_sem.get(1);
      if (error_gen.double_sdb) begin
        `INJECT_PHY_ERROR
        if (lss_cntr == 2)
          error_gen.double_sdb = `FALSE;
      end
      else if (error_gen.single_sdb) begin
        if (lss_cntr == 2 || ($urandom % 2 == 1)) begin
          `INJECT_PHY_ERROR
          error_gen.single_sdb = `FALSE;
        end
      end
      else
        `INJECT_PHY_NO_ERR
      if (lss_cntr == 2)
        error_gen_sem.put(1);
    endtask : inject_sdb_error

    local task inject_edb_error;
      if (lss_cntr == 2)
        error_gen_sem.get(1);
      if (error_gen.double_edb) begin
        `INJECT_PHY_ERROR
        if (lss_cntr == 3)
          error_gen.double_edb = `FALSE;
      end
      else if (error_gen.single_edb) begin
        if (lss_cntr == 2 || ($urandom % 2 == 1)) begin
          `INJECT_PHY_ERROR
          error_gen.single_edb = `FALSE;
        end
      end
      else
        `INJECT_PHY_NO_ERR
      if (lss_cntr == 3)
        error_gen_sem.put(1);
    endtask : inject_edb_error

    local int inject_error_cntr = -1;

    local task inject_sop_error;
      if (pkt_tx.sop_error)
        `INJECT_PHY_ERROR
      else
        `INJECT_PHY_NO_ERR
      // for payload errors:
      inject_error_cntr = pkt_tx.payload_error ?
        ($urandom % (pkt_tx.data.size / 2)) : -1;
    endtask : inject_sop_error

    local task inject_eop_error;
      error_gen_sem.get(1);
      if (pkt_tx.eop_error)
        `INJECT_PHY_ERROR
      else
        `INJECT_PHY_NO_ERR
      error_gen_sem.put(1);
    endtask : inject_eop_error

    local task inject_payload_error;
      error_gen_sem.get(1);
      if (inject_error_cntr < 0)
        `INJECT_PHY_NO_ERR
      else if (inject_error_cntr-- == 0) begin
        `INJECT_PHY_ERROR
        inject_error_cntr = $urandom % 35;
        case (inject_error_cntr) 
          0: inject_error_cntr = ($urandom % (pkt_tx.data.size * 2));
          1, 2:    ; // do nothing
          default: inject_error_cntr = 0; // to make continous injections possible
        endcase
      end
      else
        `INJECT_PHY_NO_ERR
      error_gen_sem.put(1);
    endtask : inject_payload_error

    /*  LSS errors (DIDL, LIDL, DIR, SYN) are not cleared automatically, but they can be injected
        many times until the error flag is cleared by the error controller  */

    task inject_lidl_error;
      error_gen_sem.get(1);
      if (inject_error_cntr == 0) begin
        `INJECT_PHY_ERROR
        if ($urandom_range(3) > 0)
          inject_error_cntr = 0;
        else
          --inject_error_cntr;
      end
      else begin
        `INJECT_PHY_NO_ERR
        if (inject_error_cntr == -1 && error_gen.lidl && !$urandom(7))
          inject_error_cntr = $urandom_range(111);
        if (inject_error_cntr > 0)
          --inject_error_cntr;
      end
      error_gen_sem.put(1);
    endtask : inject_lidl_error

    task inject_didl_error;
      error_gen_sem.get(1);
      if (inject_error_cntr == 0) begin
        `INJECT_PHY_ERROR
        if (!$urandom_range(3))
          inject_error_cntr = 0;
        else
          --inject_error_cntr;
      end
      else begin
        `INJECT_PHY_NO_ERR
        if (inject_error_cntr == -1 && error_gen.didl && !$urandom_range(lss_params.n_fcu))
          inject_error_cntr = $urandom_range(lss_params.n_data_gap);
        else if (inject_error_cntr > 0)
          --inject_error_cntr;
      end
      error_gen_sem.put(1);
    endtask : inject_didl_error

    task inject_dir_error;
      error_gen_sem.get(1);
      if (inject_error_cntr == 0) begin
        `INJECT_PHY_ERROR
        if (!$urandom_range(3))
          inject_error_cntr = 0;
        else
          --inject_error_cntr;
      end
      else begin
        `INJECT_PHY_NO_ERR
        if (inject_error_cntr == -1 && error_gen.dir)
          inject_error_cntr = $urandom_range(lss_params.n_lss_dir);
        else if (inject_error_cntr > 0)
          --inject_error_cntr;
      end
      error_gen_sem.put(1);
    endtask : inject_dir_error

    task inject_syn_error;
      error_gen_sem.get(1);
      if (inject_error_cntr == 0) begin
        `INJECT_PHY_ERROR
        if (!$urandom_range(3))
          inject_error_cntr = 0;
        else
          --inject_error_cntr;
      end
      else begin
        `INJECT_PHY_NO_ERR
        if (inject_error_cntr == -1 && error_gen.syn)
          inject_error_cntr = ($urandom_range(lss_params.n_lss_syn));
        else if (inject_error_cntr > 0)
          --inject_error_cntr;
      end
      error_gen_sem.put(1);
    endtask : inject_syn_error

    // ***** RECEIVING LSSES/PKTS *****

    task receive_sync_lss;
      if (phy_bus.rd[7:0] == LSS_COM &&
          phy_bus.rdm[0] == LSS_COM_M) begin
        if ( (phy_bus.rd[15:8] == LSS_BSYN0 &&
              phy_bus.rdm[1] == LSS_BSYN0_M) ||
             (phy_bus.rd[15:8] == LSS_BSYN1 &&
              phy_bus.rdm[1] == LSS_BSYN1_M) )
          rx_st = BSYN_RX_ST;
        else if ( (phy_bus.rd[15:8] == LSS_SYN0 &&
                   phy_bus.rdm[1] == LSS_SYN0_M) ||
                  (phy_bus.rd[15:8] == LSS_SYN1 &&
                   phy_bus.rdm[1] == LSS_SYN1_M) )
          rx_st = SYN_RX_ST;
        else if (phy_bus.rd[15:8] == LSS_DIR &&
                 phy_bus.rd[1] == LSS_DIR_M)
          rx_st = DIR_RX_ST;
        else if ( (phy_bus.rd[15:8] == LSS_LIDL0 &&
                   phy_bus.rdm[1] == LSS_LIDL0_M) ||
                  (phy_bus.rd[15:8] == LSS_LIDL1 &&
                   phy_bus.rdm[1] == LSS_LIDL1_M) ||
                  (phy_bus.rd[15:8] == LSS_DIDL0 &&
                   phy_bus.rdm[1] == LSS_DIDL0_M) ||
                  (phy_bus.rd[15:8] == LSS_DIDL1 &&
                   phy_bus.rdm[1] == LSS_DIDL1_M) ) begin
          rx_st = VLD_RX_ST;
          if (!active) begin
            active = `TRUE;
            drive_params_bus;
          end
        end
        else if (phy_bus.rd[15:8] == LSS_SOP &&
                 phy_bus.rdm[1]  == LSS_SOP_M)
          rx_st = PKT_RX_ST;

        if (rx_st == BSYN_RX_ST ||
            rx_st == SYN_RX_ST)
          ++sync_cntr;
      end
    endtask : receive_sync_lss

    task receive_any_lss;
      if (phy_bus.rd[7:0] == LSS_COM &&
          phy_bus.rdm[0] == LSS_COM_M) begin
        case (phy_bus.rd[15:8])
          LSS_DIR:
            if (phy_bus.rdts      == PLSM_RXTX_VLD &&
                phy_bus.rdt[7:0]  == LSS_COM &&
                phy_bus.rdtm[0]   == LSS_COM_M &&
                phy_bus.rdt[15:8] == LSS_DIR &&
                phy_bus.rdtm[1]   == LSS_DIR_M &&
                tx_st == OFF_TX_ST)
              rx_st = VLD_2L_RX_ST;
  
          LSS_LIDL0,
          LSS_LIDL1,
          LSS_DIDL0,
          LSS_DIDL1: ;
            /* do nothing */
  
          LSS_SOP:
            if (phy_bus.rdm[1] == LSS_SOP_M) begin
              rx_st = PKT_RX_ST;
              if (pkt_rx != null) pkt_rx_delay = 3;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_SOP received")
  
          LSS_SDB:
            if (phy_bus.rdm[1] == LSS_SDB_M) begin
              curr_pkt_rx_sdb = `TRUE;
              if (pkt_rx != null) pkt_rx_delay = 3;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_SDP received")
  
          LSS_EDB:
            if (phy_bus.rdm[1] == LSS_EDB_M) begin
              if (pkt_rx != null) pkt_rx.edb = `TRUE;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_EDP received")
        
          LSS_PAD,
          LSS_SYN0,
          LSS_SYN1,
          LSS_BSYN0,
          LSS_BSYN1,
          LSS_EOP:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unexpected LSS rd=%h",
               {phy_bus.rdm[1],  phy_bus.rd[15:8]}))
        
          default:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown LSS rd=%h",
               {phy_bus.rdm[1],  phy_bus.rd[15:8]}))
        endcase
      end
    endtask : receive_any_lss

    task receive_pkt_bytes;
      if (phy_bus.rd[7:0] == LSS_COM &&
          phy_bus.rdm[0] == LSS_COM_M) begin
      // receive the LSS which follows the comma
        case (phy_bus.rd[15:8])
          LSS_EOP:
            if (phy_bus.rdm[1] == LSS_EOP_M) begin
              receive_pkt_compl;
              rx_st = VLD_RX_ST;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_EOP received")
  
          LSS_SOP,
          LSS_PAD,
          LSS_LIDL0,
          LSS_LIDL1,
          LSS_DIDL0,
          LSS_DIDL1,
          LSS_SYN0,
          LSS_SYN1,
          LSS_BSYN0,
          LSS_BSYN1,
          LSS_SDB,
          LSS_EDB:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unexpected LSS rd=%h", {phy_bus.rdm[1],  phy_bus.rd[15:8]}))
        
          default:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown LSS rd=%h", {phy_bus.rdm[1],  phy_bus.rd[15:8]}))
        endcase
      end
      else begin
        // receive 2 data or PAD bytes:
        data_rx.push_back({phy_bus.rdm[0], phy_bus.rd[7:0]});
        data_rx.push_back({phy_bus.rdm[1], phy_bus.rd[15:8]});
      end
    endtask : receive_pkt_bytes
  
    task receive_pkt_compl;
      pkt_rx = new;
      pkt_rx.add_rec_data(data_rx, scrambler_on);
      data_rx = {};
      if (data_rx_odd.size > 0) begin
        pkt_rx.odd_data_pkt = new;
        pkt_rx.odd_data_pkt.add_rec_data(data_rx_odd, scrambler_on);
        data_rx_odd = {};
      end
      pkt_rx.sdb = curr_pkt_rx_sdb;
      curr_pkt_rx_sdb = `FALSE;

      pkt_rx.check_crc;
      if (!pkt_rx.crc_error)
        pkt_rx.decode_pkt;
      pkt_rx_delay = 0;
    endtask : receive_pkt_compl

    /** Passes the last received packet to upper layers after some timeout. */
    task pass_pkt_to_link;
      if (pkt_rx != null)
        if (++pkt_rx_delay > 2 || phy_bus.rds != PLSM_RXTX_VLD || pkt_rx.pkt_type == CCMD_PKT) begin
          mbx_rx.put(pkt_rx);
          if (is_card)
            `DISPLAY_LOGGER_MSG(pkt_rx.to_string)
          if (pkt_echo != null)
            pkt_echo.put_rx(pkt_rx);
          pkt_rx = null;
          pkt_rx_delay = 0;
        end
    endtask : pass_pkt_to_link

    task receive_2l_any_lss;
      if ((phy_bus.rdts === PLSM_RXTX_OFF ||
           phy_bus.rdts === PLSM_RXTX_EIDL ||
          (phy_bus.rdts === PLSM_RXTX_STB &&
           phy_bus.rds[0] === 1'b1)) &&
           phy_bus.rds  === PLSM_RXTX_VLD &&
           phy_bus.rd[7:0]  == LSS_COM &&
           phy_bus.rdm[0]   == LSS_COM_M &&
           phy_bus.rd[15:8] == LSS_DIR &&
           phy_bus.rdm[1]   == LSS_DIR_M) begin
        // return to FD
        rx_st = DIR_RX_ST;
        rx2lhd = `FALSE;
      end
      else if (phy_bus.rdts !== PLSM_RXTX_VLD)
        `DISPLAY_LOGGER_WARNING("invalid symbol received in 2L-HDin on DSL")
      else if (phy_bus.rd[7:0] == LSS_COM &&
               phy_bus.rdm[0]  == LSS_COM_M) begin      
        case (phy_bus.rd[15:8])
          LSS_DIR,
          LSS_DIDL0,
          LSS_DIDL1: ;
            /* do nothing */
  
          LSS_SOP:
            if (phy_bus.rdm[1] == LSS_SOP_M) begin
              rx_st = PKT_2L_RX_ST;
              data_rx     = {};
              data_rx_odd = {};
              if (pkt_rx != null) pkt_rx_delay = 3;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_SOP received")

          LSS_SDB:
            if (phy_bus.rdm[1] == LSS_SDB_M) begin
              curr_pkt_rx_sdb = `TRUE;
              if (pkt_rx != null) pkt_rx_delay = 3;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_SDP received")

          LSS_EDB:
            if (phy_bus.rdm[1] == LSS_EDB_M) begin
              if (pkt_rx != null) pkt_rx.edb = `TRUE;
            end
            else
              `DISPLAY_LOGGER_WARNING("invalid LSS_EDP received")

          LSS_LIDL0,
          LSS_LIDL1,
          LSS_PAD,
          LSS_SYN0,
          LSS_SYN1,
          LSS_BSYN0,
          LSS_BSYN1,
          LSS_EOP:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unexpected/incorrect LSS rd=%h rdt=%h",
                {phy_bus.rdm[1],  phy_bus.rd[15:8]},
                {phy_bus.rdtm[1], phy_bus.rdt[15:8]}))

          default:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown LSS rd=%h rdt=%h",
                {phy_bus.rdm[1],  phy_bus.rd[15:8]},
                {phy_bus.rdtm[1], phy_bus.rdt[15:8]}))
        endcase
      end
    endtask : receive_2l_any_lss

    task receive_2l_pkt_bytes;
      if (phy_bus.rdts !== PLSM_RXTX_VLD)
        `DISPLAY_LOGGER_WARNING("invalid symbol received in 2L-HDin on DSL")
      else if (phy_bus.rd[7:0]  == LSS_COM &&
               phy_bus.rdm[0]   == LSS_COM_M) begin
        if (phy_bus.rdtm !== phy_bus.rdm ||
            phy_bus.rdt  !== phy_bus.rd)
          `DISPLAY_LOGGER_WARNING($sformatf(
              "different LSS received on 2 lanes: rd=%h rdt=%h",
              {phy_bus.rdm[1],  phy_bus.rd[15:8]},
              {phy_bus.rdtm[1], phy_bus.rdt[15:8]}))
        else
          // receive the LSS which follows the comma
          case (phy_bus.rd[15:8])
            LSS_EOP:
              if (phy_bus.rdm[1] == LSS_EOP_M) begin
                receive_pkt_compl;
                rx_st = VLD_2L_RX_ST;
              end
              else
                `DISPLAY_LOGGER_WARNING("invalid LSS_EOP received")
    
            LSS_SOP,
            LSS_PAD,
            LSS_LIDL0,
            LSS_LIDL1,
            LSS_DIDL0,
            LSS_DIDL1,
            LSS_SYN0,
            LSS_SYN1,
            LSS_BSYN0,
            LSS_BSYN1,
            LSS_SDB,
            LSS_EDB:
              `DISPLAY_LOGGER_WARNING($sformatf(
                  "unexpected/incorrect LSS rd=%h rdt=%h",
                  {phy_bus.rdm[1],  phy_bus.rd[15:8]},
                  {phy_bus.rdtm[1], phy_bus.rdt[15:8]}))

            default:
              `DISPLAY_LOGGER_WARNING($sformatf(
                  "unknown LSS rd=%h",
                  {phy_bus.rdm[1],  phy_bus.rd[15:8]}))
          endcase
      end
      else begin
        // receive 2x2 data or PAD bytes:
        data_rx.push_back({phy_bus.rdm[0], phy_bus.rd[7:0]});
        data_rx.push_back({phy_bus.rdm[1], phy_bus.rd[15:8]});
        data_rx_odd.push_back({phy_bus.rdtm[0], phy_bus.rdt[7:0]});
        data_rx_odd.push_back({phy_bus.rdtm[1], phy_bus.rdt[15:8]});
      end
    endtask : receive_2l_pkt_bytes

    task reset_phy;
      #2ns;
      phy_bus.nrst          <= `LOW;
      lss_params = new;
      #15us;
      phy_bus.nrst          <= `HIGH; 
    endtask : reset_phy
  
    task initialize;
      send_eidl;
      send_off_odd;
      `INJECT_PHY_NO_ERR
      inject_error_cntr = -1;

      lss_params   =  new;
      drive_params_bus;
    endtask : initialize

    // -----------------------------------------------------------------------
    // RESET
    // -----------------------------------------------------------------------

    task reset_th;
      uhsii_pkt pkt_tmp;
      reset_th_obj = process::self();

      phy_bus.nrst            <= `LOW;

      `INJECT_PHY_NO_ERR
      inject_error_cntr = -1;

      #1ns;

      phy_bus.det_en           <= 1'b1;
      phy_bus.rclktrmen        <= 1'b1;
      phy_bus.cnfg_r1          <= 32'd0;
      phy_bus.cnfg_r2          <= 32'd0;

      phy_bus.mode             <= 1'b0;
      phy_bus.pinit_pcmd       <= 4'b0000;


      if (is_card) begin
        // power on reset in card:
        wait (phy_bus.rst_n);
        reset_phy;
      end

      forever begin
        bit reset_through_pin;
        @(negedge phy_bus.rst_n, phy_reset_ev);
        `INJECT_PHY_NO_ERR
        if (pkt_echo != null)
           fork
            fork
              pkt_echo.reset_checker;
            join_none
          join
        inject_error_cntr = -1;
        -> phy_deact_ev;

        reset_through_pin = !phy_bus.rst_n;
        if (reset_through_pin) begin
          `DISPLAY_LOGGER_INFO("RESET came through RST_N pin")
          
          phy_bus.nrst          <= `LOW;
          @(posedge phy_bus.rst_n);
        end
        else begin
          wait (phy_bus.mode === `LOW);
          #1ns;
        end
        
        while (mbx_tx.try_get(pkt_tmp)) #7ns;
        while (mbx_rx.try_get(pkt_tmp)) #2ns;
        pkt_tx = null;
        tx_st = EIDL_TX_ST;
        rx_st = EIDL_RX_ST;

        if (is_card & reset_through_pin) begin
          pkt_tmp = new;
          pkt_tmp.pkt_type = META_PKT;
          pkt_tmp.power_cycle = `TRUE;
          mbx_rx.put(pkt_tmp);
        end

        reset_phy;
        #1ns;
        initialize;
        end
    endtask : reset_th


    // -----------------------------------------------------------------------
    // PHY INIT
    // -----------------------------------------------------------------------

    task phy_init_th();
      phy_init_th_obj = process::self();

      if (is_host) begin
        @(negedge phy_bus.rst_n);
        @(posedge phy_bus.rst_n);
      end

      forever begin
        if (is_card) 
          wait (phy_bus.det === 1'b1);
        this.fast_lpm        = `FALSE;

        phy_bus.pinit_pcmd  <= {lss_params.range, 2'b00};
        repeat (2) @(posedge phy_bus.pclk);

        #1ns
        phy_bus.mode        <= 1'b1;
        #1ns
        phy_bus.pinit_pcmd  <= PCMD_NO_COMMAND;

        @(phy_deact_ev);
        drive_params_bus; 
        this.go2dormant      = `FALSE;
        this.active          = `FALSE;

        if (!phy_bus.rst_n || this.go4reset);
        else if (is_card) begin
          int t = (lss_params.range == 0 ? 1 : 2) * T_DMT_ENTRY_PCLK_A / 3;
          while (t-- > 0 && phy_bus.rst_n)
            @(posedge phy_bus.pclk, negedge phy_bus.rst_n);
        end
        else if (is_host)
          repeat ((lss_params.range == 0 ? 1 : 2) * T_DMT_ENTRY_PCLK_A + 2)
            @(posedge phy_bus.pclk);

        #0.2ns;
        phy_bus.mode        <= 1'b0;
        phy_bus.pinit_pcmd  <= 4'b000;
        this.go4reset        = `FALSE;

        drive_params_bus;

        if (is_host)
          wait (pkt_tx != null);
      end
    endtask : phy_init_th

    // -----------------------------------------------------------------------
    // TX PROC
    // -----------------------------------------------------------------------

    task tx_main_th();
      tx_main_th_obj = process::self();
      #2;

      forever begin
        if (! phy_bus.rst_n) begin
          send_eidl;
          lss_cntr = 0;
          tx_st = EIDL_TX_ST;
          `INJECT_PHY_NO_ERR
          inject_error_cntr = -1;
        end
        else if (phy_bus.lock) begin
          // error injection
          case (tx_st)
            EIDL_TX_ST, STBL_TX_ST, STBH_TX_ST, ENTER_2LHD_IN_TX_ST, OFF_TX_ST,
            WAIT_EXIT_2LHD_IN_TX_ST, EXIT_2LHD_IN_TX_ST, DIR_TX_ST: begin
              `INJECT_PHY_NO_ERR // no errors
              inject_error_cntr = -1;
            end

            default: ; // do nothing, decision on errors is made in dedicated methods
          endcase

          case (tx_st)
            EIDL_TX_ST: begin
              send_eidl;
              check_new_pkt;
              if (lss_cntr >= ((active | is_card) ? 1 : 3) * T_EIDL_GAP &&
                 (active ? (pkt_tx != null ||
                           (fast_lpm && !lss_params.lpm &&
                            (is_host || rx_st == STBL_RX_ST)) ) :
                            (is_host || rx_st == STBL_RX_ST)) ) begin
                lss_cntr = 0;
                tx_st = STBL_TX_ST;
              end
              else if (rx_st == EIDL_RX_ST && lss_cntr >= T_EIDL_GAP && go2dormant)
                -> phy_deact_ev;
              else if (rx_st == EIDL_RX_ST && lss_cntr >= T_EIDL_GAP && go4reset)
                -> phy_reset_ev;
            end
         
            STBL_TX_ST: begin
              send_stbl;
              if (lss_cntr >= T_EIDL_RECOVERY &&
                  (active ||
                  (is_host && rx_st == STBL_RX_ST) ||
                  (is_card && sync_cntr > sync_delay) ||
                   rx_st == DIR_RX_ST) ) begin
                lss_cntr = 0;
                tx_st = (rx_st == DIR_RX_ST  ? DIR_TX_ST :
                         rx_st == BSYN_RX_ST ? BSYN_TX_ST :
                                               SYN_TX_ST);
              end
            end
  
            SYN_TX_ST,
            BSYN_TX_ST: begin
              if (tx_st == BSYN_TX_ST)
                send_boot_syn_lss;
              else
                send_plain_syn_lss;
              inject_syn_error;
  
              if (active ? lss_cntr >= lss_params.n_lss_syn :
                  ((is_host && ((rx_st == BSYN_RX_ST && tx_st == BSYN_TX_ST) ||
                                (rx_st == SYN_RX_ST && tx_st == SYN_TX_ST)) ) ||
                   (is_card && rx_st == VLD_RX_ST)) ) begin
                lss_cntr = 0;
                tx_st = (pkt_tx != null && active) ? PKT_INIT_TX_ST : LIDL_TX_ST;
              end
              else if (is_card && !active && rx_st == EIDL_RX_ST) begin
                lss_cntr = 0;
                tx_st = STBH_TX_ST;
              end
            end
        
            LIDL_TX_ST,
            DIDL_TX_ST:
            begin
              if (tx_st == DIDL_TX_ST) begin
                send_didl_lss;
                inject_didl_error;
               end
              else begin
                send_lidl_lss;
                inject_lidl_error;
                fast_lpm &= lss_params.lpm; // complete exit from LPM
              end
            
              check_new_pkt;
              if (pkt_tx != null && active) begin
                if (tx_st == LIDL_TX_ST ||
                    lss_cntr >= lss_params.n_data_gap) begin
                  if (pkt_tx.init_2lhd_out) begin
                    if (rx_st == OFF_RX_ST || rx_st == EIDL_RX_ST) begin
                      // !! MC - SLI PHY REQUIREMENT
                      tx_st = WAIT_ENTER_2LHD_OUT_TX_ST;
                      lss_cntr = 0;
                    end
                  end
                  else begin
                    tx_st = PKT_INIT_TX_ST;
                    lss_cntr = 0;
                  end
                end
              end
              else if (!didl_tx && (fast_lpm ||
                                   ((lss_params.lpm | go2dormant | go4reset) &&
                                    (rx_st == EIDL_RX_ST || is_host)) )) begin
                tx_st = STBH_TX_ST;
                lss_cntr = 0;
              end
              else if (tx_st == DIDL_TX_ST && !didl_tx)
                tx_st = LIDL_TX_ST;
            end
  
            PKT_INIT_TX_ST:
              send_pkt_init;
  
            PKT_DATA_TX_ST:
              send_pkt_data;
  
            PKT_FINAL_TX_ST:
              send_pkt_final;
        
            STBH_TX_ST: begin
              send_stbh;
              if (lss_cntr >= T_EIDL_ENTRY) begin
                tx_st = rx2lhd ? ENTER_2LHD_IN_TX_ST : EIDL_TX_ST;
                lss_cntr = 0;
                if (go2dormant)
                  -> phy_deact_ev;
                fast_lpm |= lss_params.lpm; // complete entry to LPM
              end
            end


           // --- 2L-HD out --

            WAIT_ENTER_2LHD_OUT_TX_ST:
              send_wait_enter_2lhd_out;

            ENTER_2LHD_OUT_TX_ST:
              send_enter_2lhd_out;

            PREAMBLE_2LHD_OUT_TX_ST:
              send_preamble_2lhd_out;

            SYNC_2LHD_OUT_TX_ST:
              send_sync_2lhd_out;

            PKT_2L_INIT_TX_ST:
              send_pkt_init(`TRUE);

            PKT_2L_DATA_TX_ST:
              send_pkt_data(`TRUE);

            PKT_2L_FINAL_TX_ST:
              send_pkt_final(`TRUE);

            DIDL_2L_TX_ST: begin
              send_didl_lss(`TRUE);
              inject_didl_error;
            
              check_new_pkt;
              if (lss_cntr >= lss_params.n_data_gap) begin
                // there should always be at least one packet 
                tx_st = PKT_2L_INIT_TX_ST;
                lss_cntr = 0;
              end
            end

            POSTAMBLE_2LHD_OUT_TX_ST:
              send_postamble_2lhd_out;
          
            EXIT_2LHD_OUT_TX_ST:
              send_exit_2lhd_out;

            WAIT_DIR_TX_ST: begin
              send_dir_lss;
              inject_dir_error;
              if (rx_st == DIR_RX_ST) begin
                tx_st = DIDL_TX_ST;
                lss_cntr = 0;
              end
            end

            // --- 2L-HD in --

            ENTER_2LHD_IN_TX_ST:
              send_enter_2lhd_in;

            OFF_TX_ST: begin
              send_off;
              if (!rx2lhd) begin
                tx_st = WAIT_EXIT_2LHD_IN_TX_ST;
                lss_cntr = 0;
              end
            end

            WAIT_EXIT_2LHD_IN_TX_ST:
              send_wait_exit_2lhd_in;

            EXIT_2LHD_IN_TX_ST:
              send_exit_2lhd_in;

            DIR_TX_ST: begin
              send_dir_lss;
              inject_dir_error;
              if (rx_st == VLD_RX_ST)
                tx_st = (fast_lpm ? STBH_TX_ST : LIDL_TX_ST);
              lss_cntr = 0;
            end

            default:
              `DISPLAY_LOGGER_WARNING($sformatf(
                  "unknown tx_out_byte_r: %s", tx_st))
          endcase
        end
        else begin
          `INJECT_PHY_NO_ERR
          inject_error_cntr = -1;
        end

        // wait for clock
        @(posedge phy_bus.pclk, negedge phy_bus.rst_n);
      end
    endtask : tx_main_th

    // -----------------------------------------------------------------------
    // RX PROC
    // -----------------------------------------------------------------------
  
    task rx_main_th();
      rx_main_th_obj = process::self();
      #3;

      forever begin
        @(posedge phy_bus.pclk, negedge phy_bus.rst_n);
        if (! phy_bus.rst_n) begin
          rx_st = EIDL_RX_ST;
          pkt_rx = null;
          pkt_rx_delay = 0;
          sync_cntr = 0;
          rx2lhd = `FALSE;
          data_rx     = {};
          data_rx_odd = {};
        end
        else
          case (phy_bus.rds)
            PLSM_RXTX_OFF: begin
              rx_st = OFF_RX_ST;
              data_rx     = {};
              data_rx_odd = {};
            end

            PLSM_RXTX_EIDL: begin
              rx_st = EIDL_RX_ST;
              sync_cntr = 0;
              data_rx     = {};
              data_rx_odd = {};
            end

            PLSM_RXTX_STB: begin
              rx_st = phy_bus.rd[0] === 1'b1 ? STBH_RX_ST : STBL_RX_ST;
              data_rx     = {};
              data_rx_odd = {};
            end

            PLSM_RXTX_VLD:
              case (rx_st)
                VLD_RX_ST:    receive_any_lss;
                PKT_RX_ST:    receive_pkt_bytes;

                VLD_2L_RX_ST: receive_2l_any_lss;
                PKT_2L_RX_ST: receive_2l_pkt_bytes;
              
                default:      receive_sync_lss;
              endcase
          endcase
        pass_pkt_to_link;
      end
    endtask : rx_main_th

    // ==================================================================== //

    function void add_pkt_echo_if(virtual uhsii_pkt_chk.PUT_PKT pkt_echo);
      this.pkt_echo = pkt_echo;
    endfunction : add_pkt_echo_if

  endclass : uhsii_xtor_cl
endpackage : uhsii_xtor_pkg
