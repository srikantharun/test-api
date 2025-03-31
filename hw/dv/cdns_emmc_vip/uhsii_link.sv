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
//   UHS-II link layer
//
//   File contents  : package uhsii_link_pkg
//                    class   uhsii_link_cl
//------------------------------------------------------------------------------

`timescale 1ns / 100ps

package uhsii_link_pkg;
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
  import uhsii_params_pkg::*;
  import uhsii_pkt_pkg::*;
  import uhsii_tran_pkg::*;
  import sd_card_pkg::*;
`ifdef CARD_COVER
  `include "uhsii_card_cover.svh"
`endif // CARD_COVER

  typedef enum {
    /** Idle device can execute any command: CCMD - sends RES, stays in
     TRANSF_IDLE; write DCMD - sends RES and transits to TRANSF_IN_WAIT;
     read DCMD - sends RES, then FCREQ and transits to TRANSF_OUT_ACTIVE.
     The state roughly corresponds to TP_IDLE and TP_WAIT states of TPSM
     in TRAN. */
    TRANSF_IDLE,

    /** Device responds with FCRDY to FCREQ and goes to TRANSF_IN_ACTIVE.
     In case of CCMD, device executes it, responds with RES and stays in
     TRANSF_IN_WAIT. The state roughly corresponds to TP_INTERVAL and
     TP_C_INTERVAL of TPSM in TRAN. */
    TRANSF_IN_WAIT,

    /** Device accepts DATA pkts, sends STAT upon EDB and transits to
     TRANSF_IDLE or TRANSF_IN_WAIT. The state corresponds to TP_DIN
     of TPSM in TRAN. */
    TRANSF_IN_ACTIVE,

    /** Upon FCRDY, device sends data pkts and transits to TRANSF_OUT_WAIT.
     The state roughly corresponds to TP_DOUT of TPSM in TRAN. */
    TRANSF_OUT_ACTIVE,

    /** Device waits for STAT. Afterwards sends FCREQ and transits to
     TRANSF_OUT_ACTIVE, or just transits to TRANSF_IDLE in case of the end
     of the data transfer. The state roughly corresponds to TP_INTERVAL of
     TPSM in TRAN */
    TRANSF_OUT_WAIT
  } transf_st_e;
  
  typedef enum {
    CMD_RSP_DELAY,      RES_FCREQ_DELAY,
    STAT_FCREQ_DELAY,   FCRDY_DATA_DELAY,
    FCREQ_FCRDY_DELAY,  DATA_STAT_DELAY
  } delay_e;
  
  class uhsii_link_cl extends component_cl;

    local mailbox #(uhsii_pkt)             mbx_xl_tx;
    local mailbox #(uhsii_pkt)             mbx_xl_rx;
    local mailbox #(uhsii_rsp)             mbx_lt_tx;
    local mailbox #(uhsii_req)             mbx_lt_rx;

    local uhsii_tran_cl                    cm_tran;

    local uhsii_pkt                        last_rec_pkt,
                                           prev_rec_pkt;
    local uhsii_req                        dreq;
    local uhsii_rsp                        drsp;
    local transf_st_e                      transf_st;

    local bit                              inside_db,
                                           crc_err_db;

    local int                              db_retry_max,
                                           db_retry_cntr;

    local mailbox #(card_echo_event_cl)    event_echo;
    local process                          th_obj = null;
    
    local bit                              no_delays;

    // pseudo-random behaviour:

    protected int unsigned       wait_units;
    static int unsigned          random_seed;

    // for error generation in card:

    struct {
      bit db_payload;
      bit db_sop;
      bit db_eop;

      bit single_msg;
      bit double_msg;
      bit res_sop;
      bit res_payload;
      bit res_eop;

      bit fcreq_urecov;
      bit fcrdy_urecov;
      bit stat_recov;
      bit stat_urecov;
      bit ebsy_mem;

      bit not_msg;
      bit not_res;
      bit not_data;

      bit trans_id;
      
      bit cmd_nak;
    } error_gen;

    semaphore error_gen_sem;

  `ifdef CARD_COVER
    local uhsii_retry_cover_cl       retry_cov       = null;
    local uhsii_crc_err_inj_cover_cl crc_err_inj_cov = null;
    
    function void set_uhsii_card_covergroups(input uhsii_retry_cover_cl        retry_cov,
                                             input uhsii_crc_err_inj_cover_cl  crc_err_inj_cov);
      this.retry_cov        = retry_cov;
      this.crc_err_inj_cov  = crc_err_inj_cov;
    endfunction : set_uhsii_card_covergroups
  `endif // CARD_COVER

    // -------------------------------------------------------------------- //

    function new (input string               _name,
                  input component_cl         _parent,
                  input mailbox #(uhsii_pkt) _mbx_xl_tx,
                  input mailbox #(uhsii_pkt) _mbx_xl_rx,
                  input mailbox #(uhsii_rsp) _mbx_lt_tx,
                  input mailbox #(uhsii_req) _mbx_lt_rx,
                  input uhsii_tran_cl        _cm_tran,
                  input bit                  _no_delays);
      super.new(_name, _parent);
      this.mbx_xl_tx     = _mbx_xl_tx;
      this.mbx_xl_rx     = _mbx_xl_rx;
      this.mbx_lt_tx     = _mbx_lt_tx;
      this.mbx_lt_rx     = _mbx_lt_rx;
      this.cm_tran       = _cm_tran;
      this.no_delays     = _no_delays;
      this.event_echo    = null;
      this.error_gen_sem = new(1);

      random_seed = random_seed + 26'h3FB6F5D;
      wait_units = random_seed;
    endfunction : new

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    task start;
      fork
        run;
      join_none
    endtask : start
  
    function string get_class_name;
      return "uhsii_link_cl";
    endfunction : get_class_name

    task run;
      th_obj = process::self();
      `DISPLAY_LOGGER_NOTE("run method of UHSII_LINK started");
      // pass start param values from TRAN registers
      pass_lss_params;

      // *** main thread ***
      forever begin
        receive_pkt;
        take_action;
      end
    endtask : run

    function void dispose;
      if (th_obj != null)
        th_obj.kill;
    endfunction : dispose

    // -------------------------------------------------------------------- //

    task pass_lss_params;
      uhsii_rsp rsp = null;

      mbx_lt_tx.get(rsp);
      if (rsp.req != null || rsp.change_params == null)
        `DISPLAY_LOGGER_WARNING("missing initialization TRAN params")
      else begin
        uhsii_pkt pkt = new;
        if (rsp.fsm_rst) begin
          transf_st = TRANSF_IDLE;
          pkt.switch2lidl = `TRUE;
          drsp = null;
        end
        pkt.pkt_type = META_PKT;
        pkt.change_params = rsp.change_params;
        pkt.go2dormant = rsp.go2dormant;
        pkt.go4reset   = rsp.phy_rst;
        mbx_xl_tx.put(pkt);
      end
    endtask : pass_lss_params

    local task receive_pkt;
      prev_rec_pkt = last_rec_pkt;
      mbx_xl_rx.get(last_rec_pkt);    
    endtask : receive_pkt
    
`ifdef CARD_COVER
    bit crc_error_in_last_read_burst = `FALSE;

    function inj_pkt_e decode_msg_inj_pkt(uhsii_pkt _pkt);
      return _pkt.ctg == MSG_CTG_LMSG ? (
            _pkt.idx == LMSG_IDX_FCREQ ? FCREQ_CRC_ERR_INJ :
            _pkt.idx == LMSG_IDX_FCRDY ? FCRDY_CRC_ERR_INJ :
            _pkt.idx == LMSG_IDX_STAT  ? STAT_CRC_ERR_INJ  :
                                         UNKNOWN_CRC_ERR_INJ
          ) :
          _pkt.ctg == MSG_CTG_AMSG ? (
            _pkt.idx == AMSG_IDX_EBSY  ? EBSY_CRC_ERR_INJ :
                                         UNKNOWN_CRC_ERR_INJ
          ) : UNKNOWN_CRC_ERR_INJ;
    endfunction : decode_msg_inj_pkt
`endif // CARD_COVER

    /** Sends two copies of msg pkt. The first copy has repeat_msg flag set,
        and other meta flags unset, both can have errors injected. If needed,
        task waits to obtain the key for error injection operations. */
    local task send_msg_pkt_twice(input uhsii_pkt msg_pkt,
                                  input bit       key_needed);
      uhsii_pkt msg1_pkt     = msg_pkt.copy,
                msg2_pkt     = msg_pkt;
      msg1_pkt.repeat_msg    = `TRUE;
      msg1_pkt.switch2didl   = `FALSE;
      msg1_pkt.init_2lhd_in  = `FALSE;

      if (key_needed)
        error_gen_sem.get(1);

      if ((error_gen.single_msg | error_gen.double_msg) && 
          ( !$urandom_range(11) || (msg_pkt.ctg == MSG_CTG_AMSG &&
                                    msg_pkt.idx == AMSG_IDX_EBSY) )) begin
        inject_msg_error(msg1_pkt, `FALSE, `FALSE);
        inject_msg_error(msg2_pkt, `TRUE,  `FALSE);
      end

      if (error_gen.not_msg && !$urandom_range(5)) begin
        `DISPLAY_LOGGER_NOTE("Errors injected in message: change type")
        case ($urandom_range(4))
          0: begin
            msg1_pkt = null;
            msg2_pkt.change_type = `TRUE;
          end
          1: begin
            msg1_pkt.change_type = `TRUE;
            msg2_pkt = null;
          end
          default: begin
            msg1_pkt.change_type = `TRUE;
            msg2_pkt.change_type = `TRUE;
          end
        endcase
        if (!$urandom_range(3))
          error_gen.not_msg = `FALSE;
      end
      inject_trans_id_error(msg1_pkt, msg2_pkt);
      if (key_needed)
        error_gen_sem.put(1);
        
      if (msg1_pkt != null)
        send_pkt(msg1_pkt);
      if (msg2_pkt != null)
        send_pkt(msg2_pkt);

    `ifdef CARD_COVER
      if (crc_err_inj_cov != null &&
          msg1_pkt != null && ~msg1_pkt.change_type && // both messages exist
          msg2_pkt != null && ~msg2_pkt.change_type && // both have unchanged type
         (msg1_pkt.payload_error | msg2_pkt.payload_error) && // at least one have CRC error
         (msg1_pkt.payload_error | msg1_pkt.sop_error | msg1_pkt.eop_error) && // both have some error
         (msg2_pkt.payload_error | msg2_pkt.sop_error | msg2_pkt.eop_error) ) begin
        crc_err_inj_cov.msg_err_inj_callback(decode_msg_inj_pkt(msg1_pkt));
      end
    `endif // CARD_COVER
    endtask : send_msg_pkt_twice

    local task wait_before_send_pkt(delay_e dmode);
      if (no_delays) return;
      case (dmode)
        RES_FCREQ_DELAY:      wait_units %= 220;           // RES out 2 FCREQ out (read)
        STAT_FCREQ_DELAY:     wait_units %= 190;           // STAT in 2 FCREQ out (read)
        FCRDY_DATA_DELAY:     wait_units %= 280; /*/10*/   // FCRDY in 2 DATA out (read)
        FCREQ_FCRDY_DELAY:    wait_units %= 450;           // FCREQ in 2 FCRDY out (write)
        DATA_STAT_DELAY:      wait_units %= 220; /*/10*/   // DATA in 2 STAT out (write)
        CMD_RSP_DELAY:        wait_units %= 310;           // CMD in 2 RSP out
      endcase

      if (dmode == FCRDY_DATA_DELAY || dmode == DATA_STAT_DELAY) begin
        `DISPLAY_LOGGER_NOTE($sformatf("UHSII PKT delay: %0.2f us", wait_units/100.0))
        #(wait_units * 10ns);
      end
      else begin
        `DISPLAY_LOGGER_NOTE($sformatf("UHSII PKT delay: %0.1f us", wait_units/10.0))
        #(wait_units * 0.1us);
      end
      wait_units = 2541 * wait_units + 7;
    endtask : wait_before_send_pkt

    local task send_pkt(input uhsii_pkt send_pkt);
      mbx_xl_tx.put(send_pkt);
      #3ns;
    endtask : send_pkt

    local task process_req2rsp(input  uhsii_req reqx,
                               output uhsii_rsp rspx);
      time cmd2rsp_delay;

      mbx_lt_rx.put(reqx);
      mbx_lt_tx.get(rspx);
      assert (rspx != null)
      else $fatal(1, "Internal card model error (process_req2rsp)");

      `DISPLAY_LOGGER_MSG($sformatf("TRAN: %s", rspx.to_string))

      if (rspx.fsm_rst | rspx.phy_rst) begin
        uhsii_pkt meta_pkt = new;
        transf_st = TRANSF_IDLE;
        meta_pkt.pkt_type = META_PKT;
        meta_pkt.switch2lidl = `TRUE;
        if (rspx.phy_rst)
          drsp = null;
        send_pkt(meta_pkt);
      end

      if (rspx.change_params != null)
        db_retry_max = rspx.change_params.max_retry_num;

      wait_before_send_pkt(CMD_RSP_DELAY);
    endtask : process_req2rsp

    local task check_wait_send_ebsy(input uhsii_rsp lrsp);
      bit send_ebsy;
      uhsii_pkt ebsy_pkt;

      if (lrsp != null) begin
        lrsp.wait_to_send_ebsy(send_ebsy);
        if (send_ebsy) begin
          ebsy_pkt = new;
          ebsy_pkt.make_ebsy_pkt(last_rec_pkt);
          error_gen_sem.get(1);
          ebsy_pkt.urec_err = error_gen.ebsy_mem;
          error_gen.ebsy_mem = `FALSE;
          error_gen_sem.put(1);
          send_msg_pkt_twice(ebsy_pkt, `FALSE);
        end
      end
    endtask : check_wait_send_ebsy

    local task echo_card_operation(input uhsii_pkt in_pkt,
                                   input uhsii_pkt out_pkt);
      if (this.event_echo != null)
        fork
          begin
            uhsii_echo_event_cl echo_tmp = new (in_pkt, out_pkt);
            if (out_pkt != null)
              wait (out_pkt.sent);
            void'(this.event_echo.try_put(echo_tmp));
          end
        join_none
    endtask : echo_card_operation

    // -------------------------------------------------------------------- //

    local task take_action;
      if (last_rec_pkt.sdb)
        inside_db = `TRUE;

      `DISPLAY_LOGGER_NOTE($sformatf("link FSM state: %s inside_DB=%b pow_cycle=%b crc_err=%b",
        transf_st.name, inside_db, last_rec_pkt.power_cycle, last_rec_pkt.crc_error))

      if (last_rec_pkt.power_cycle)
        request_reset;
      else if (last_rec_pkt.crc_error) begin
        if (inside_db)
          // data pkts with CRC error can't be simply ignored
          accept_pkt;
        else
          `DISPLAY_LOGGER_WARNING("CRC error in received packet")
      end
      else if (last_rec_pkt.pkt_type == UNKN_PKT ||
               last_rec_pkt.decode_error)
          `DISPLAY_LOGGER_WARNING("Malformed packet received")
      else begin
        if (inside_db) begin
          if (last_rec_pkt.pkt_type != DATA_PKT &&
              last_rec_pkt.pkt_type != DATA_PKT_2L);
          else if (last_rec_pkt.dest_id != cm_tran.get_own_node_id)
            `DISPLAY_LOGGER_WARNING("packet shall have been bypassed by DB streaming")
          else;
            accept_pkt;
        end
        else begin
          if (last_rec_pkt.pkt_type == DATA_PKT ||
              last_rec_pkt.pkt_type == DATA_PKT_2L)
            `DISPLAY_LOGGER_WARNING("data packet found outside DB")
          else if (last_rec_pkt.src_id == last_rec_pkt.dest_id &&
                   last_rec_pkt.pkt_type == CCMD_PKT)
            execute_ccmd_broadcast;
          else if (last_rec_pkt.src_id == cm_tran.get_own_node_id)
            `DISPLAY_LOGGER_WARNING("issued pkt not accepted by any other device")
          else if (last_rec_pkt.dest_id != cm_tran.get_own_node_id)
            bypass_pkt;
          else
            accept_pkt;
        end
      end

      if (last_rec_pkt.edb)
        inside_db = `FALSE;
    endtask : take_action

    local task request_reset;
      uhsii_pkt tmp_pkt;
      uhsii_req req = new;      
      req.reset = `TRUE;
      mbx_lt_rx.put(req);

      while (mbx_xl_tx.try_get(tmp_pkt));
      
      pass_lss_params;
      // ^^ not only passes LSS params to XTOR
      // first gets TRAN's res to reset req
      echo_card_operation(last_rec_pkt, null);
    endtask : request_reset

    local task bypass_pkt;
      `DISPLAY_LOGGER_NOTE("pkt bypassed")
      send_pkt(last_rec_pkt); // bypass in LINK
    endtask : bypass_pkt

    // *** standard command execution ***

    local task accept_pkt;
      if (last_rec_pkt.pkt_type == MSG_PKT &&
          last_rec_pkt.compare_to(prev_rec_pkt));
          // ignores doubled link msg pkt
      else if (last_rec_pkt.crc_error && transf_st != TRANSF_IN_ACTIVE)
        `DISPLAY_LOGGER_WARNING("Packet with CRC error received and ignored")
      else
        case (transf_st)
          TRANSF_IDLE:
            accept_pkt_idle;
          TRANSF_IN_WAIT:
            accept_pkt_in_wait;
          TRANSF_IN_ACTIVE:
            accept_pkt_in_active;
          TRANSF_OUT_ACTIVE:
            accept_pkt_out_active;
          TRANSF_OUT_WAIT:
            accept_pkt_out_wait;
          default:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unexpected transf_st: %s", transf_st.name))
        endcase
    endtask : accept_pkt

    local task accept_pkt_idle;
      case (last_rec_pkt.pkt_type)
        CCMD_PKT:
          execute_ccmd_p2p;
        DCMD_PKT:
          execute_dcmd;
        RES_PKT,
        DATA_PKT,
        MSG_PKT:
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unexpected pkt type in TRANSF_IDLE received: %s",
              last_rec_pkt.pkt_type.name))
        default:
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unknown pkt type received: %s",
              last_rec_pkt.pkt_type.name))
      endcase    
    endtask : accept_pkt_idle

    // *** standard data flow control ***

    /** Sends FCRDY upon FCREQ reception. Possibly executes CCMD. */
    local task accept_pkt_in_wait;
      uhsii_pkt fc_pkt;

      case (last_rec_pkt.pkt_type)
        CCMD_PKT:
          execute_ccmd_p2p;
        DCMD_PKT,
        RES_PKT:
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unexpected pkt type in TRANSF_IN_WAIT received: %s",
              last_rec_pkt.pkt_type.name))
        DATA_PKT:
          `DISPLAY_LOGGER_WARNING(
             "DATA pkt received in TRANSF_IN_WAIT without FC handshake completion")
        MSG_PKT:
          if (last_rec_pkt.ctg == MSG_CTG_LMSG)
            case (last_rec_pkt.idx)
              LMSG_IDX_FCREQ:
                if (last_rec_pkt.urec_err)
                  `DISPLAY_LOGGER_WARNING("LMSG_IDX_FCREQ with unrecoverable error received")
                else begin
                  fc_pkt = new;
                  error_gen_sem.get(1);
                  fc_pkt.make_fc_pkt(last_rec_pkt, LMSG_IDX_FCRDY, error_gen.fcrdy_urecov);
                  fc_pkt.init_2lhd_in = dreq.dpm & !error_gen.fcrdy_urecov;
                  error_gen.fcrdy_urecov = `FALSE;
                  error_gen_sem.put(1);
                  wait_before_send_pkt(FCREQ_FCRDY_DELAY);
                  send_msg_pkt_twice(fc_pkt, `FALSE);
                  transf_st = error_gen.fcrdy_urecov ? TRANSF_IN_WAIT : TRANSF_IN_ACTIVE;
                end
              LMSG_IDX_FCRDY:
                `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_FCRDY")
              LMSG_IDX_STAT:
                `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_STAT")
              default:
                `DISPLAY_LOGGER_WARNING($sformatf(
                    "unknown Link MSG %b", last_rec_pkt.idx))
            endcase
        default:
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unknown pkt type received: %s",
              last_rec_pkt.pkt_type.name))
      endcase
    endtask : accept_pkt_in_wait
  
    /** Accepts data burst and sends STAT. CCMD not allowed. */
    local task accept_pkt_in_active;
      bit inject_urec_err = `FALSE;
      uhsii_pkt fc_pkt;
      mem_blk blk;
      string temp;
    
      if (last_rec_pkt.pkt_type != DATA_PKT &&
          last_rec_pkt.pkt_type != DATA_PKT_2L &&
         !last_rec_pkt.crc_error)
        `DISPLAY_LOGGER_WARNING($sformatf(
            "expecting DATA_PKT, found: %s",
            last_rec_pkt.pkt_type.name))
      else if (!inside_db)
        `DISPLAY_LOGGER_WARNING(
            "packet received but ignored, waiting for SDB")
      else begin
        if (last_rec_pkt.crc_error)
          crc_err_db = `TRUE;
        else if (!crc_err_db) begin
          blk = new;
          blk.data = new [dreq.blm ? drsp.blk_len : dreq.tlen];
          for (int i = 0, j = last_rec_pkt.payload_index;
              (i < last_rec_pkt.payload_length) && (i < blk.data.size);
              ++i, ++j)
            blk.data[i] = last_rec_pkt.data[j][7:0];
          drsp.put_next_blk(blk);
        end

        if (last_rec_pkt.edb) begin
          error_gen_sem.get(1);
          if (crc_err_db) begin
            if (++db_retry_cntr > db_retry_max) begin
              crc_err_db = `FALSE;
              inject_urec_err = `TRUE;
              db_retry_cntr = 0;
            end
          end
          else if (error_gen.stat_recov && $urandom_range(3)) begin
            crc_err_db = error_gen.stat_recov;
            if (!$urandom_range(4))
              error_gen.stat_recov = `FALSE;
          end
          
        `ifdef CARD_COVER
          if (retry_cov != null)
            retry_cov.next_burst(crc_err_db | inject_urec_err);
          if ((~crc_err_db & ~inject_urec_err) && crc_err_inj_cov != null)
            crc_err_inj_cov.next_burst_callback(crc_err_db | inject_urec_err);
        `endif // CARD_COVER

          if (!crc_err_db && !inject_urec_err) begin
            inject_urec_err = error_gen.stat_urecov;
            error_gen.stat_urecov = `FALSE;
          end
          error_gen_sem.put(1);

          fc_pkt = new;
          fc_pkt.make_fc_pkt(last_rec_pkt, LMSG_IDX_STAT,
            inject_urec_err, crc_err_db);
          wait_before_send_pkt(DATA_STAT_DELAY);
          send_msg_pkt_twice(fc_pkt, `TRUE);
          drsp.complete_put(crc_err_db | inject_urec_err);
          #3ns;
          transf_st = (inject_urec_err | drsp.has_next_blk) ? TRANSF_IN_WAIT : TRANSF_IDLE;

          `DISPLAY_LOGGER_NOTE($sformatf(
              "DB pkt accepted, %s",
              inject_urec_err ? "UNRECOVERABLE ERROR!" :
              crc_err_db ? "DB RETRY" : "END OF DB"))
          crc_err_db = `FALSE;
  
          if (transf_st == TRANSF_IDLE) begin
            drsp.transf_compl = `TRUE;
            check_wait_send_ebsy(drsp);
            clear_stat_errors;
          end
        end
        else
          `DISPLAY_LOGGER_NOTE("DB pkt accepted, waiting for next")
      end
    endtask : accept_pkt_in_active
  
    /** Sends data burst upon FCRDY reception. Possibly executes CCMD. */
    local task accept_pkt_out_active;
      case (last_rec_pkt.pkt_type)
        CCMD_PKT:
          execute_ccmd_p2p;
        DCMD_PKT,
        RES_PKT,
        DATA_PKT:
          `DISPLAY_LOGGER_WARNING($sformatf(
            "unexpected pkt type in TRANSF_OUT_ACTIVE received: %s",
            last_rec_pkt.pkt_type.name))
        MSG_PKT:
          if (last_rec_pkt.ctg == MSG_CTG_LMSG && !last_rec_pkt.urec_err)
            case (last_rec_pkt.idx)
              LMSG_IDX_FCREQ:
                `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_FCREQ")
              LMSG_IDX_FCRDY:
                send_entire_data_burst;
              LMSG_IDX_STAT:
                `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_STAT")
              default:
                `DISPLAY_LOGGER_WARNING($sformatf(
                    "unknown Link MSG %b", last_rec_pkt.idx))
            endcase
        default:
          `DISPLAY_LOGGER_WARNING($sformatf(
              "unknown pkt type received: %s",
              last_rec_pkt.pkt_type.name))
      endcase
    endtask : accept_pkt_out_active

    local task send_entire_data_burst;
      uhsii_pkt data_pkt;
      mem_blk blk;
      bit [2:0] err_mask = 3'b000;
    `ifdef CARD_COVER
      bit crc_error_injected = `FALSE;
    `endif // CARD_COVER

      error_gen_sem.get(1);
      if (error_gen.trans_id && !$urandom_range(15)) begin
        err_mask = ($urandom % 3'b111) + 1'b1;
        error_gen.trans_id = `FALSE;
      end
      error_gen_sem.put(1);

      wait_before_send_pkt(FCRDY_DATA_DELAY);

      for (int i = 0; drsp.has_next_blk &&
                     (i < drsp.n_fcu || !dreq.blm); ++i) begin
        blk = drsp.get_next_blk;
        data_pkt = new;
        data_pkt.make_data_pkt(~dreq.lsd, last_rec_pkt, blk.data,
                               dreq.blm ? drsp.blk_len : dreq.tlen,
                               dreq.dpm);
        data_pkt.trans_id ^= err_mask;
        if (i == 0) begin
          data_pkt.sdb = `TRUE;
          data_pkt.init_2lhd_out = dreq.dpm;
        end
        #2ns; // necessary for lsd=1 & tlen=0
        if (i + 1 == drsp.n_fcu || !drsp.has_next_blk)
          data_pkt.edb = `TRUE;

        if (err_mask == 3'b000)
          inject_db_error(data_pkt, i);
        send_pkt(data_pkt);
      `ifdef CARD_COVER
        crc_error_injected |= data_pkt.payload_error;
      `endif // CARD_COVER
      end

      transf_st = TRANSF_OUT_WAIT;
    `ifdef CARD_COVER
      if (crc_error_injected && crc_err_inj_cov != null)
        crc_err_inj_cov.data_transf_err_inj_callback(DATA_BURST_CRC_ERR_INJ);
      crc_error_in_last_read_burst = crc_error_injected;
    `endif // CARD_COVER
    endtask : send_entire_data_burst

    /** Waits for STAT and decides whether to transmit next DB. */
    local task accept_pkt_out_wait;
      uhsii_pkt fc_pkt, meta_pkt;

      if (last_rec_pkt.pkt_type != MSG_PKT)
        `DISPLAY_LOGGER_WARNING($sformatf(
            "expecting MSG_PKT, found: %s",
            last_rec_pkt.pkt_type.name))
      else begin
        if (last_rec_pkt.ctg == MSG_CTG_LMSG)
          case (last_rec_pkt.idx)
            LMSG_IDX_FCREQ:
              `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_FCREQ")
            LMSG_IDX_FCRDY:
              `DISPLAY_LOGGER_WARNING("unexpected LMSG_IDX_FCRDY")
            LMSG_IDX_STAT: begin
            `ifdef CARD_COVER
              if (retry_cov != null)
                retry_cov.next_burst(last_rec_pkt.rec_err | last_rec_pkt.urec_err, crc_error_in_last_read_burst);
              if (~last_rec_pkt.rec_err && crc_err_inj_cov != null)
                crc_err_inj_cov.next_burst_callback(last_rec_pkt.rec_err | last_rec_pkt.urec_err);
            `endif // CARD_COVER
              if (last_rec_pkt.urec_err) begin
                `DISPLAY_LOGGER_WARNING("LMSG_IDX_STAT with unrecoverable error received")
                transf_st = TRANSF_OUT_ACTIVE;
              end
              else begin
                meta_pkt = new;
                meta_pkt.pkt_type = META_PKT;
                meta_pkt.switch2lidl = `TRUE;
                send_pkt(meta_pkt);
            
                drsp.complete_get(last_rec_pkt.rec_err);
                if (drsp.has_next_blk) begin
                  error_gen_sem.get(1);
                  fc_pkt = new;
                  fc_pkt.make_fc_pkt(last_rec_pkt, LMSG_IDX_FCREQ, error_gen.fcreq_urecov);
                  error_gen.fcreq_urecov = `FALSE;
                  error_gen_sem.put(1);
                  fc_pkt.switch2didl = `TRUE;
                  wait_before_send_pkt(STAT_FCREQ_DELAY);
                  send_msg_pkt_twice(fc_pkt, `FALSE);
                  transf_st = TRANSF_OUT_ACTIVE;
                end
                else begin
                  // read transfer completed!
                  transf_st = TRANSF_IDLE;
                  drsp.transf_compl = `TRUE;
                  check_wait_send_ebsy(drsp);
                  clear_db_errors;
                end
              end
            end
          default:
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown Link MSG %b", last_rec_pkt.idx))
        endcase
      end
    endtask : accept_pkt_out_wait

    // **** standard command execution details ****
  `ifdef CARD_COVER
    function inj_oper_e decode_ccmd_inj_oper(uhsii_req _req);
      if (_req.lsd) begin
        if (~_req.app && _req.cmd_index == 6'd12)
          return STOP_TRANSF_CRC_ERR_INJ;
        else
          return NORMAL_CCMD_CRC_ERR_INJ;
      end
      else if (_req.rw) begin
        if (_req.addr[11:0] == UHSII_CMD_IOADR_TRANS_ABORT)
          return TRANS_ABORT_CRC_ERR_INJ;
        else if (_req.addr[11:0] == UHSII_CMD_IOADR_GO_DORMANT_STATE)
          return GO_DORMANT_CRC_ERR_INJ;
        else
          return NORMAL_CCMD_CRC_ERR_INJ;
      end
      else
        return NORMAL_CCMD_CRC_ERR_INJ;
    endfunction : decode_ccmd_inj_oper
  `endif // CARD_COVER

    local task execute_ccmd_broadcast;
      uhsii_req req    = null;
      uhsii_rsp rsp    = null;
      uhsii_pkt bc_pkt = null;

      if (last_rec_pkt.np);
      else begin
        `DISPLAY_LOGGER_WARNING("SD commands cannot be broadcast in UHS-II")
        return;
      end
      
      req = new;
      req.cd = `FALSE;
      req.rw = last_rec_pkt.rw;
      req.addr = {20'h00000, last_rec_pkt.ioadr};
      req.pld = new[last_rec_pkt.plen == 3 ? 4 : last_rec_pkt.plen];
      req.bc = `TRUE;
      if (req.pld.size > 0)
        copy_from_ccmd_payload(last_rec_pkt, req);

      process_req2rsp(req, rsp);

      if (~rsp.nak) begin
        bc_pkt = new;
        bc_pkt.make_brc_pkt(last_rec_pkt);
        if (req.pld.size > 0)
          bc_pkt.add_payload(req.pld);
        if (rsp.change_params != null)
          bc_pkt.change_params = rsp.change_params;
        bc_pkt.go2dormant = rsp.go2dormant;
        bc_pkt.go4reset   = rsp.phy_rst;

        inject_res_error(bc_pkt);
        send_pkt(bc_pkt);

      `ifdef CARD_COVER
        if (crc_err_inj_cov != null) begin
          crc_err_inj_cov.ccmd_accepted_callback(decode_ccmd_inj_oper(req), `YES);
          if (bc_pkt.payload_error & ~bc_pkt.change_type)
            crc_err_inj_cov.ccmd_error_inj_callback;
        end
      `endif // CARD_COVER
      end
      echo_card_operation(last_rec_pkt, bc_pkt);
    endtask : execute_ccmd_broadcast

    local task execute_ccmd_p2p;
      uhsii_req req = null;
      uhsii_rsp rsp = null;
      uhsii_pkt res_pkt = new;
      
      req = new;
      req.cd = `FALSE;

      if (last_rec_pkt.np) begin
        req.rw    = last_rec_pkt.rw;
        req.addr  = {20'h00000, last_rec_pkt.ioadr};
        req.pld   = new[last_rec_pkt.plen == 3 ? 4 : last_rec_pkt.plen];
      end
      else begin
        req.lsd       = `TRUE;
        req.app       = last_rec_pkt.app;
        req.cmd_index = last_rec_pkt.cmd_index;
        req.addr      = last_rec_pkt.sd_arg;
      end
      if (req.rw && req.pld.size > 0)
        copy_from_ccmd_payload(last_rec_pkt, req);

      process_req2rsp(req, rsp);

      res_pkt.make_res_pkt(last_rec_pkt, rsp.nak, rsp.ecode);
      if (!rsp.nak) begin
        if (!req.rw && req.pld.size > 0)
          res_pkt.add_payload(req.pld);
        if (rsp.change_params != null)
          res_pkt.change_params = rsp.change_params;
        res_pkt.go2dormant = rsp.go2dormant;
        res_pkt.go4reset   = rsp.phy_rst;
      end

      inject_res_error(res_pkt);
      send_pkt(res_pkt);
    `ifdef CARD_COVER
      if (crc_err_inj_cov != null) begin
        crc_err_inj_cov.ccmd_accepted_callback(decode_ccmd_inj_oper(req), `NO);
        if (res_pkt.payload_error & ~res_pkt.change_type)
          crc_err_inj_cov.ccmd_error_inj_callback;
      end
    `endif // CARD_COVER
      echo_card_operation(last_rec_pkt, res_pkt);

      check_wait_send_ebsy(rsp);
      check_wait_send_ebsy(drsp);
    endtask : execute_ccmd_p2p

    local function void copy_from_ccmd_payload(uhsii_pkt pkt, uhsii_req req);
      int i = -1, j = pkt.payload_index, k,
        pld_dword_num = pkt.payload_length / 4;
      if (pld_dword_num > req.pld.size)
        pld_dword_num = req.pld.size;
      while (++i < pld_dword_num) begin
        req.pld[i] = 32'h00000000;
        for (k = 0; k < 4; ++j, ++k)
          req.pld[i] ^= ({24'h000000, pkt.data[j][7:0]} << (8 * (3 - k)));
      end
    endfunction : copy_from_ccmd_payload

    local task execute_dcmd;
      uhsii_pkt res_pkt = new,
                fc_pkt;
      bit reject_args = `FALSE;
      
      // ** check arguments **
      if (last_rec_pkt.dam == `TRUE) begin
        `DISPLAY_LOGGER_WARNING("Fixed address mode DAM=1 is not supported");
        reject_args = `TRUE;
      end
      else if (last_rec_pkt.tlum == `TRUE) begin
        if (last_rec_pkt.lm == `FALSE) begin
          `DISPLAY_LOGGER_WARNING("TLEN must be specified in byte mode: TLUM=1 LM=0");
          reject_args = `TRUE;
        end
        else if (last_rec_pkt.dm == `TRUE) begin
          `DISPLAY_LOGGER_WARNING("2L-HD is not supported in byte mode: TLUM=1 DM=1");
          reject_args = `TRUE;
        end
        else if (last_rec_pkt.tlen < 1 ||
                 last_rec_pkt.tlen > (last_rec_pkt.np ? 512 : 2048)) begin
          `DISPLAY_LOGGER_WARNING($sformatf(
              "Incorrect TLEN=%0d specified; must be between 1 and %0d inclusively",
              last_rec_pkt.tlen, last_rec_pkt.np ? 512 : 2048));
          reject_args = `TRUE;
        end
      end

      if (reject_args) begin
        res_pkt.make_res_pkt(last_rec_pkt, `TRUE, ECODE_ARG_ERR);
        inject_res_error(res_pkt);
        send_pkt(res_pkt);
        `DISPLAY_LOGGER_INFO("DCMD rejected ...")
        return;
      end

      // ** request **
      dreq        = new;
      dreq.lsd    = ~last_rec_pkt.np;
      dreq.cd     = `TRUE;
      dreq.tlen   = last_rec_pkt.lm ? last_rec_pkt.tlen : -1;
      dreq.blm    = ~ last_rec_pkt.tlum;
      dreq.dpm    = last_rec_pkt.dm;
      if (last_rec_pkt.np) begin
        dreq.rw   = last_rec_pkt.rw;
        dreq.addr = last_rec_pkt.dadr;
      end
      else begin
        dreq.app       = last_rec_pkt.app;
        dreq.cmd_index = last_rec_pkt.cmd_index;
        dreq.addr      = last_rec_pkt.sd_arg;
      end

      process_req2rsp(dreq, drsp);

      // ** response **
      res_pkt.make_res_pkt(last_rec_pkt, drsp.nak, drsp.ecode);
      if (dreq.lsd && dreq.pld.size > 0)
        res_pkt.add_payload(dreq.pld);

      inject_res_error(res_pkt);
      send_pkt(res_pkt);
    `ifdef CARD_COVER
      if (crc_err_inj_cov != null) begin
        crc_err_inj_cov.new_data_transf_callback(
            dreq.rw,
            dreq.cmd_index == 6'd18 || dreq.cmd_index == 6'd25 ||
           (dreq.cmd_index == 6'd53 && dreq.addr[27]),
            dreq.dpm);
        if (res_pkt.payload_error)
          crc_err_inj_cov.data_transf_err_inj_callback(RES_CRC_ERR_INJ);
      end
    `endif // CARD_COVER

      echo_card_operation(last_rec_pkt, res_pkt);

      // ** data transfer **
      if (drsp.start_data_transfer) begin
        if (! dreq.rw) begin
          fc_pkt = new;
          fc_pkt.make_fc_pkt(last_rec_pkt, LMSG_IDX_FCREQ);
          fc_pkt.switch2didl = `TRUE;
          wait_before_send_pkt(RES_FCREQ_DELAY);
          send_msg_pkt_twice(fc_pkt, `TRUE);
        end
        transf_st = dreq.rw ? TRANSF_IN_WAIT : TRANSF_OUT_ACTIVE;
      `ifdef CARD_COVER
        if (retry_cov != null)
          retry_cov.new_transfer(
              dreq.rw,
              dreq.cmd_index == 6'd18 || dreq.cmd_index == 6'd25 ||
             (dreq.cmd_index == 6'd53 && dreq.addr[27]),
             ~dreq.blm, db_retry_max);
      `endif // CARD_COVER
      end
    endtask : execute_dcmd

    // -------------------------------------------------------------------- //

    function void register_event_echo(
        input mailbox #(card_echo_event_cl) event_echo);
      this.event_echo = event_echo;
    endfunction : register_event_echo

    task inject_db_error(input uhsii_pkt pkt, input int i);
      if ((i == 0 && !drsp.has_next_blk) || i == $urandom_range(drsp.n_fcu)) begin
        error_gen_sem.get(1);
        if (error_gen.db_sop && !$urandom_range(3)) begin
          pkt.sop_error = error_gen.db_sop;
          if (!$urandom_range(3))
            error_gen.db_sop = `FALSE;
        end
        if (error_gen.db_eop && !$urandom_range(3)) begin
          pkt.eop_error = error_gen.db_eop;
          if (!$urandom_range(3))
            error_gen.db_eop = `FALSE;
        end
        if (error_gen.db_payload && $urandom_range(4)) begin
          pkt.payload_error = error_gen.db_payload;
          if (!$urandom_range(5))
            error_gen.db_payload = `FALSE;
        end
        if (error_gen.not_data && !$urandom_range(4)) begin
          pkt.change_type = error_gen.not_data;
          if (!$urandom_range(2))
            error_gen.not_data = `FALSE;
        end
        error_gen_sem.put(1);
      end
    endtask : inject_db_error
    
    task clear_stat_errors;
      error_gen_sem.get(1);
      error_gen.stat_urecov  = `FALSE;
      error_gen.stat_recov   = `FALSE;
      error_gen.trans_id     = `FALSE;
      error_gen_sem.put(1);
    endtask : clear_stat_errors
    
    task clear_db_errors;
      error_gen_sem.get(1);
      error_gen.db_sop     = `FALSE;
      error_gen.db_eop     = `FALSE;
      error_gen.db_payload = `FALSE;
      error_gen.not_data   = `FALSE;
      error_gen.trans_id   = `FALSE;
      error_gen_sem.put(1);
    endtask : clear_db_errors

    task inject_res_error(input uhsii_pkt pkt);
      error_gen_sem.get(1);
      pkt.sop_error             = error_gen.res_sop;
      pkt.eop_error             = error_gen.res_eop;
      pkt.payload_error         = error_gen.res_payload;
      pkt.change_type           = error_gen.not_res;

      error_gen.res_sop         = `FALSE;
      error_gen.res_eop         = `FALSE;
      error_gen.res_payload     = `FALSE;
      error_gen.not_res         = `FALSE;
      
      inject_trans_id_error(pkt);

      error_gen_sem.put(1);

      if (pkt.sop_error)
        `DISPLAY_LOGGER_NOTE("Errors injected: SOP")
      if (pkt.eop_error)
        `DISPLAY_LOGGER_NOTE("Errors injected: EOP")
      if (pkt.payload_error)
        `DISPLAY_LOGGER_NOTE("Errors injected: payload")
      if (pkt.change_type)
        `DISPLAY_LOGGER_NOTE("Errors injected: not RES")
    endtask : inject_res_error

    local function bit is_ebsy_pkt(uhsii_pkt pkt);
      return pkt == null ? `FALSE :
            (pkt.pkt_type == MSG_PKT && pkt.ctg == MSG_CTG_AMSG && pkt.idx == AMSG_IDX_EBSY && ~pkt.change_type);
    endfunction : is_ebsy_pkt
    
    task inject_trans_id_error(input uhsii_pkt pkt1, input uhsii_pkt pkt2 = null);
      
      if (error_gen.trans_id && (!$urandom_range(11) || 
                                 ((pkt1 == null || is_ebsy_pkt(pkt1)) &&
                                  (pkt2 == null || is_ebsy_pkt(pkt2)) &&
                                   cm_tran.get_last_sd_cmd_was_dcmd) )) begin
        bit [2:0] err_mask = $urandom % 3'b111 + 1'b1;
        `DISPLAY_LOGGER_NOTE("Errors injected: trans ID")
        if (pkt1 != null)
          pkt1.trans_id ^= err_mask;
        if (pkt2 != null)
          pkt2.trans_id ^= err_mask;
        error_gen.trans_id = `FALSE;
      end
    endtask : inject_trans_id_error

    task inject_msg_error_details(input uhsii_pkt pkt);
      case ($urandom % 10)
        1:       pkt.sop_error        = `TRUE;
        2:       pkt.eop_error        = `TRUE;
        default: pkt.payload_error    = `TRUE;
      endcase
    endtask : inject_msg_error_details

    task inject_msg_error(input uhsii_pkt     pkt,
                          input bit           second,
                          input bit           key_needed);
      if (!second && key_needed)
        error_gen_sem.get(1);
      if (error_gen.double_msg) begin
        inject_msg_error_details(pkt);
        if (second)
          error_gen.double_msg = `FALSE;
      end
      else if (error_gen.single_msg) begin
        if (second || ($urandom % 2 == 1)) begin
          inject_msg_error_details(pkt);
          error_gen.single_msg = `FALSE;
        end
      end
      `DISPLAY_LOGGER_NOTE($sformatf(
          "Errors injected in %s %s: sop=%0b payload=%0b eop=%0b",
          second ? "2nd" : "1st",
          pkt.ctg == MSG_CTG_LMSG ? (
            pkt.idx == LMSG_IDX_FCREQ ? "FCREQ" :
            pkt.idx == LMSG_IDX_FCRDY ? "FCRDY" :
            pkt.idx == LMSG_IDX_STAT  ? "STAT"  : "unknmsg"
          ) :
          pkt.ctg == MSG_CTG_AMSG ? (
            pkt.idx == AMSG_IDX_EBSY  ? "EBSY! " : "unknmsg"
          ) : "unknmsg",
          pkt.sop_error, pkt.payload_error, pkt.eop_error))
      if (second && key_needed)
        error_gen_sem.put(1);
    endtask : inject_msg_error

  endclass : uhsii_link_cl
endpackage : uhsii_link_pkg
