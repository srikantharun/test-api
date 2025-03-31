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
//   SD legacy/UHS-I/eMMC transactor
//
//   File contents  : pakage sd_xtor_pkg
//                    class  sd_xtor_cl
//------------------------------------------------------------------------------

`timescale 1ns / 1ps

`define STRICT_OUTPUT_WINDOW_CMD
`define STRICT_OUTPUT_WINDOW_DAT

`ifdef USE_LOGGERS
  `define DISPLAY_INCOMING(_str) \
    `DISPLAY_LOGGER_MSG($sformatf("<i>incoming</i>  %s", _str))
  `define DISPLAY_OUTGOING(_str) \
    `DISPLAY_LOGGER_MSG($sformatf("<i>outgoing</i>  %s", _str))
`else // USE_LOGGERS
  `define DISPLAY_INCOMING(_str) \
    `DISPLAY_LOGGER_MSG($sformatf("INCOMING PKT:  %s", _str))
  `define DISPLAY_OUTGOING(_str) \
    `DISPLAY_LOGGER_MSG($sformatf("OUTGOING PKT:  %s", _str))
`endif // !USE_LOGGERS

package sd_xtor_pkg;
`include "card_logging.svh"
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import sd_card_pkg::*;
  import sd_tok_pkg::*;
  
  class sd_xtor_cl extends component_cl;
    local virtual sd_4v00_if.CARD sd_bus;

    mailbox #(sd_cmd)      mbx_cmd;
    mailbox #(sd_rsp)      mbx_rsp;
    mailbox #(sd_dat)      mbx_dat_wr;
    mailbox #(sd_dat)      mbx_dat_rd;
    mailbox #(bit)         mbx_intr;
    mailbox #(bit)         mbx_lvs;

    local bit              sdio_mode;
    local bit              emmc_mode;
    local bit              supress_debug;

    local bit              intr_signal_n = `HIGH; // reflects interrupt bit value in SDIO layer
    local bit              intr_output_n = `HIGH; // reflects current DAT1 output value
    
    local realtime lvsi_imp_time;

    int supress_all_checks ;
 	
    local process cmd_bus_th_obj     = null,
                  dat_bus_th_obj     = null,
                  intr_signal_th_obj = null;

    function new (input string               _name,
                  input component_cl         _parent,
                  input virtual              sd_4v00_if.CARD bus,
                  input bit                  emmc_mode,
                  input bit                  sdio_mode);
      super.new(_name, _parent);
      this.sd_bus         = bus;
      this.mbx_cmd        = new (1);
      this.mbx_rsp        = new (1);
      this.mbx_dat_wr     = new (1);
      this.mbx_dat_rd     = new (1);
      this.mbx_lvs        = new (1);
      this.error_gen_sem  = new (1);
      this.emmc_mode      = emmc_mode;
      this.sdio_mode      = sdio_mode;
      this.bus_speed      = emmc_mode ? DEFAULT_EMMC : IDENT_SPEED;
      if (sdio_mode)
        this.mbx_intr     = new (1);
      supress_all_checks  = 0;	
      this.cg_ddr_crc_error = new();
`ifdef DISABLE_ALL_CHECKS 
      supress_all_checks  = 1;	      
`endif      
    endfunction : new

    function void make;
    endfunction : make

    function void link_up;
    endfunction : link_up

    function string get_class_name;
      return "sd_xtor_cl";
    endfunction : get_class_name

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    task start;
      fork
        run;
      join_none
    endtask : start

    task run();
      fork : all_sd_xtor_threads
        cmd_bus_th;
        dat_bus_th;

        if (sdio_mode)
          intr_signal_th;
      join_none
    endtask : run

    // ***** bus speed and timing *****

    local bus_speed_e      bus_speed;

    local const realtime OUTPUT_DELAY_CMD_MAX[13] = { // = t_ODLmax
      14ns,     // Identification
      14ns,     // DS
      14ns,     // HS
      14ns,     // SDR12
      14ns,     // SDR25
      7.5ns,    // SDR50
      0ns,      // SDR104 // not to be used
      13.7ns,   // DDR50
      26.7ns,   // DS (eMMC) // = 1/(26MHz) - t_OSU_min !
      13.7ns,   // HS SDR (eMMC)
      13.7ns,   // HS DDR (eMMC)
      0ns,      // HS200 (eMMC) // not to be used
      0ns       // HS400 (eMMC) // not to be used
    };

    local const realtime OUTPUT_DELAY_DAT_MAX[13]  = { // = t_ODLmax
      14ns,     // Identification
      14ns,     // DS
      14ns,     // HS
      14ns,     // SDR12
      14ns,     // SDR25
      7.5ns,    // SDR50
      0ns,      // SDR104 // not to be used
      7ns,      // DDR50
      26.7ns,   // DS (eMMC) // = 1/(26MHz) - t_OSU_min !
      13.7ns,   // HS SDR (eMMC)
      7ns,      // HS DDR (eMMC)
      0ns,      // HS200 (eMMC) // not to be used
      0ns       // HS400 (eMMC) // not to be used
    };

    // T_ODLY_max for CMD and DAT differ only in DDR50 and eMMC-DDR

    local const realtime OUTPUT_DELAY_CMD_MIN[13] = { // = t_OHmin
      0ns,      // Identification
      0ns,      // DS
      2.5ns,    // HS
      1.5ns,    // SDR12
      1.5ns,    // SDR25
      1.5ns,    // SDR50
      0ns,      // SDR104 // not to be used
      1.5ns,    // DDR50
      8.3ns,    // DS (eMMC)
      2.5ns,    // HS SDR (eMMC)
      2.5ns,    // HS DDR (eMMC)
      0ns,      // HS200 (eMMC) // not to be used
      0ns       // HS400 (eMMC) // not to be used
    };

    local const realtime OUTPUT_DELAY_DAT_MIN[13] = { // = t_OHmin
      0ns,      // Identification
      0ns,      // DS
      2.5ns,    // HS
      1.5ns,    // SDR12
      1.5ns,    // SDR25
      1.5ns,    // SDR50
      0ns,      // SDR104 // not to be used
      1.5ns,    // DDR50
      8.3ns,    // DS (eMMC)
      2.5ns,    // HS SDR (eMMC)
      1.5ns,    // HS DDR (eMMC) // = tODLYmin, 2.5ns for CMD
      0ns,      // HS200 (eMMC) // not to be used
      0ns       // HS400 (eMMC) // not to be used
    };

    local bit uses_dynamic_cmd_fastest_out_delay = `TRUE;
    local bit uses_dynamic_dat_fastest_out_delay = `TRUE;
    local bit uses_dynamic_cmd_fastest_out_window = `TRUE;
    local bit uses_dynamic_dat_fastest_out_window = `TRUE;

    local realtime OUTPUT_DELAY_CMD_FASTEST_CONST = 9.615ns; // = t_OP (UHS-I), = t_PH (eMMC)
    local realtime OUTPUT_DELAY_DAT_FASTEST_CONST = 9.615ns; // = t_OP (UHS-I), = t_PH (eMMC)
    local realtime OUTPUT_WINDOW_CMD_FASTEST_CONST = 2.885ns; // = t_ODW (UHS-I), = t_VW (eMMC)
    local realtime OUTPUT_WINDOW_DAT_FASTEST_CONST = 2.885ns; // = t_ODW (UHS-I), = t_VW (eMMC)
    local realtime OUTPUT_DELAY_FASTEST_DYNAMIC;      // updated at every clk posedge to 2*UI
    local realtime OUTPUT_WINDOW_FASTEST_DYNAMIC;     // updated at every clk posedge to a*UI; SD:a=0.6, eMMC:a=0.585
    local realtime OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR; // updated at every clk posedge to UI/2 - 2*0.4ns

    local const realtime TIME_RQ = 400ps;

    // for setting output timings in the fastest modes (SDR104, HS200, HS400):

    function void set_fastest_speed_out_delay(input int cmd_delay_in_ps,
                                              input int dat_delay_in_ps);
      OUTPUT_DELAY_CMD_FASTEST_CONST = cmd_delay_in_ps * 1ps;
      OUTPUT_DELAY_DAT_FASTEST_CONST = dat_delay_in_ps * 1ps;
      uses_dynamic_cmd_fastest_out_delay = (cmd_delay_in_ps < 0);
      uses_dynamic_dat_fastest_out_delay = (dat_delay_in_ps < 0);
      `DISPLAY_LOGGER_NOTE($sformatf(
          "ODLY set in SD XTOR to %s (cmd) and %s (dat)",
          uses_dynamic_cmd_fastest_out_delay ? "dynamic" : $sformatf("%t", OUTPUT_DELAY_CMD_FASTEST_CONST),
          uses_dynamic_dat_fastest_out_delay ? "dynamic" : $sformatf("%t", OUTPUT_DELAY_DAT_FASTEST_CONST) ))
    endfunction : set_fastest_speed_out_delay

    function void set_fastest_speed_out_window(input int cmd_window_in_ps,
                                               input int dat_window_in_ps);
      OUTPUT_WINDOW_CMD_FASTEST_CONST = cmd_window_in_ps * 1ps;
      OUTPUT_WINDOW_DAT_FASTEST_CONST = dat_window_in_ps * 1ps;
      uses_dynamic_cmd_fastest_out_window = (cmd_window_in_ps < 0);
      uses_dynamic_dat_fastest_out_window = (dat_window_in_ps < 0);
      `DISPLAY_LOGGER_NOTE($sformatf(
          "OW set in SD XTOR to %s (cmd) and %s (dat)",
          uses_dynamic_cmd_fastest_out_window ? "dynamic" : $sformatf("%t", OUTPUT_WINDOW_CMD_FASTEST_CONST),
          uses_dynamic_dat_fastest_out_window ? "dynamic" : $sformatf("%t", OUTPUT_WINDOW_DAT_FASTEST_CONST) ))
    endfunction : set_fastest_speed_out_window

    // output delay/window macros:
    local realtime last_clk_posedge  = 0.0;
    local realtime tmp_period_last   = 1s,
                   tmp_period_prev   = 1s;

    `define OUT_DELAY_CMD_MAX        (uses_fastest(this.bus_speed) ? ( \
                                        uses_dynamic_cmd_fastest_out_delay ? \
                                          OUTPUT_DELAY_FASTEST_DYNAMIC : \
                                          OUTPUT_DELAY_CMD_FASTEST_CONST \
                                        ) : \
                                        OUTPUT_DELAY_CMD_MAX[this.bus_speed] \
                                     )
    `define OUT_DELAY_DAT_MAX        (uses_fastest(this.bus_speed) ? (( \
                                        uses_dynamic_dat_fastest_out_delay ? \
                                          OUTPUT_DELAY_FASTEST_DYNAMIC : \
                                          OUTPUT_DELAY_DAT_FASTEST_CONST) + ( \
                                        bus_speed == HS400_EMMC ? TIME_RQ : 0ps)) : \
                                      OUTPUT_DELAY_DAT_MAX[this.bus_speed])

    `define OUT_DELAY_CMD_MIN        (OUTPUT_DELAY_CMD_MIN[this.bus_speed])
    `define OUT_DELAY_DAT_MIN        (OUTPUT_DELAY_DAT_MIN[this.bus_speed])

    local function void reset_dynamic_delays();
      last_clk_posedge = 0.0;
      tmp_period_last  = 1s;
      tmp_period_prev  = 1s;
    endfunction : reset_dynamic_delays

    // ***** destructor *****

    function void dispose;
      if (cmd_bus_th_obj != null)       cmd_bus_th_obj.kill;
      if (dat_bus_th_obj != null)       dat_bus_th_obj.kill;
      if (intr_signal_th_obj != null)   intr_signal_th_obj.kill;

      sd_bus.cmd_o <=                         `HIMP;
      sd_bus.dat_o <=                     { 8{`HIMP} };
      sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX     `HIMP;
      sd_bus.dat_o <= #`OUT_DELAY_DAT_MAX { 8{`HIMP} };
    endfunction : dispose

    // ***** for error generation in card *****

    struct {
      bit cmd_crc;
      bit cmd_end_bit;
      bit dat_crc;
      bit dat_end_bit;
      bit cmd_crc_acmd;
      bit cmd_end_bit_acmd;
    } error_gen;

    semaphore error_gen_sem;

    // ==================================================================== //

    enum {
      CMD_IDLE,             // waiting for start bit of new CMD
      CMD_BUSY,             // idle but not ready to accept a new command
      CMD_NEW,              // new CMD transmission bit
      CMD_REC,              // receiving the entire CMD

      RSP_WAIT,             // wait for RSP to send, go to IDLE if no RSP
      RSP_LONG,             // transmitting 136-bit RSP
      RSP_SHORT,            // transmitting 48-bit RSP

      CMD_VOLT_SWITCH,      // voltage switch CMD=0 (not ready)
      CMD_VOLT_SWITCH_END,  // voltage switch CMD=1 (last cycle)

      CMD_BOOT_WAIT,        // host drives CMD=0 for N cycles, N=2..74;
      CMD_BOOT_CONF,        // host drives CMD=0 for N cycles, N > 74

      CMD_ERROR             // incorrect state
    } cmd_bus_st;

    enum {
      DAT_IDLE,             // waiting for DAT to return to 1 or Z (idle "not confirmed")
      DAT_IDLE_CONF,        // waiting for start bit of new data ("confirmed" idle state)
      SEND_WAIT,            // waiting for new read data to send
      SEND_START,
      SEND_DATA,
      SEND_CRC,
      SEND_END,
      REC_DATA,
      REC_CRC,
      REC_CANCELLED,
      SEND_FEEDBACK,
      SEND_BUSY,            // driving DAT0 LOW (card not ready)
      SEND_INTR,            // driving DAT1 LOW (card signals interrupt)
      DAT_VOLT_SWITCH,      // voltage switch DATs=0 (not ready)
      DAT_VOLT_SWITCH_END,  // voltage switch DATs=1 (last cycle)
      DAT_ERROR             // incorrect state
    } dat_bus_st;

    // ==================================================================== //

    local int       cmd_bit_cntr;

    sd_cmd         cmd_rx = null;
    sd_rsp         rsp_tx = null,
                   rsp_null;

    bit [7:1]      cmd_rx_crc;
    bit [7:1]      rsp_tx_crc;

    int wr_dat_blklen; // write data blklen to be expected by xtor; 0 = no write transfer expected
    int dat_bus_width; // number of lines to be used for data transfers (DAT0...DAT7)
    int busy_sig_count;

    local task cmd_bus_th;
      cmd_bus_th_obj = process::self();
      #2ns;

      forever begin
      `ifdef STRICT_OUTPUT_WINDOW_CMD
        if (!uses_fastest(this.bus_speed) && cmd_bus_st != CMD_VOLT_SWITCH &&
                                             cmd_bus_st != CMD_VOLT_SWITCH_END)
          sd_bus.cmd_o <= #`OUT_DELAY_CMD_MIN `HIMP;
      `endif // STRICT_OUTPUT_WINDOW_CMD

        if (sd_bus.rst_n === `LOW) begin
          sd_bus.cmd_o <= `HIMP;
          sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIMP;
          cmd_rx = new;
          cmd_rx.power_cycle = `TRUE;
          mbx_cmd.put(cmd_rx);
          mbx_rsp.get(rsp_tx);
          #30ns;
          cmd_bus_st = CMD_IDLE;
          dat_bus_width = 1;
          fork
              low_voltage_init();
          join_any
            
        end
        else
        case (cmd_bus_st)
          CMD_BUSY,
          CMD_IDLE: begin
            sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIMP;
            if (cmd_bus_st == CMD_BUSY) begin
              if (--cmd_bit_cntr == 0)
                cmd_bus_st = CMD_IDLE;
            end
            else if (sd_bus.cmd_d === `FALSE) // cmd S-bit
              cmd_bus_st = CMD_NEW;
          end

          // -------------------------------------------------------------- //

          CMD_NEW:
            if (sd_bus.cmd_d === `HIGH) begin // cmd T-bit
              cmd_rx = new;
              cmd_bit_cntr = (48 - 2);
              cmd_bus_st = CMD_REC;
            end
            else if (emmc_mode) begin
              cmd_bus_st = CMD_BOOT_WAIT;
              cmd_bit_cntr = 72;
            end
            else
              cmd_bus_st = CMD_ERROR;

          // -------------------------------------------------------------- //

          CMD_REC:
            if (--cmd_bit_cntr >= 40)      // command index
              cmd_rx.index[cmd_bit_cntr-40] = sd_bus.cmd_d;
            else if (cmd_bit_cntr >= 8)    // command argument
              cmd_rx.arg[cmd_bit_cntr-8]    = sd_bus.cmd_d;
            else if (cmd_bit_cntr > 0)     // CRC
              cmd_rx_crc[cmd_bit_cntr]      = sd_bus.cmd_d;
            else begin                     // E-bit
              cmd_rx.crc_err = (!sd_bus.cmd_d || (cmd_rx_crc[7:1] != calc_crc7(
                  {2'b01, cmd_rx.index, cmd_rx.arg}, 40)));
              `DISPLAY_INCOMING(cmd_rx.to_string)
              mbx_cmd.put(cmd_rx);
              mbx_rsp.peek(rsp_tx);

              assert (rsp_tx != null && rsp_tx.rsp_kind != EMPTY_RSP)
              else $fatal(1, "Internal implementation error");

              if (rsp_tx.rsp_kind == NONE_RSP) begin
                cmd_bus_st = CMD_BUSY;
                cmd_bit_cntr = 8;
                mbx_rsp.get(rsp_null);
                wr_dat_blklen = 0;
              end
              else begin
                `DISPLAY_OUTGOING(rsp_tx.to_string)
                if (bus_speed==IDENT_SPEED || bus_speed==DEFAULT_SPEED )
                  cmd_bit_cntr = 0;
                else 
                  cmd_bit_cntr = 1;
                cmd_bus_st = RSP_WAIT;
                rsp_tx.randomize_delay(this.bus_speed); // N_CR timing
                `DISPLAY_LOGGER_NOTE($sformatf("RSP delay: %0d cycle(s)", rsp_tx.delay_cycles))
                if (rsp_tx.wr_dat_blklen >= 0)
                  wr_dat_blklen = rsp_tx.wr_dat_blklen;
              end
            end

          // -------------------------------------------------------------- //

          RSP_WAIT: begin
          `ifdef STRICT_OUTPUT_WINDOW_CMD
            if (++cmd_bit_cntr >= 3)
          `else
            if (++cmd_bit_cntr == 3)
          `endif // STRICT_OUTPUT_WINDOW_CMD
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIGH; // P bit
            if (cmd_bit_cntr < rsp_tx.delay_cycles);
            else if (rsp_tx.contents.size == 4) begin
              cmd_bit_cntr = 136;
              cmd_bus_st = RSP_LONG;
            end
            else begin
              cmd_bit_cntr = 48;
              rsp_tx_crc = (rsp_tx.rsp_kind == R3 || rsp_tx.rsp_kind == R4) ?
                            7'b1111111 :
                            calc_crc7(
                           {2'b00, rsp_tx.index, rsp_tx.contents[0]}, 40);
              cmd_bus_st = RSP_SHORT;

              if (rsp_tx.rsp_kind != R3 || rsp_tx.rsp_kind != R4) begin
                bit spoil_crc = `FALSE;
                error_gen_sem.get(1);
                if (cmd_rx.index == 6'd12 || cmd_rx.index == 6'd23) begin
                  spoil_crc = error_gen.cmd_crc_acmd;
                  error_gen.cmd_crc_acmd = `FALSE;
                end
                else if (cmd_rx.index != 6'd19 && cmd_rx.index != 6'd21) begin
                  spoil_crc = error_gen.cmd_crc;
                  error_gen.cmd_crc = `FALSE;
                end
                error_gen_sem.put(1);
                if (spoil_crc) begin
                  rsp_tx_crc ^= ($urandom % 6'd63) + 1'b1;
                  `DISPLAY_LOGGER_NOTE("error injected: CMD CRC")
                end
              end
            end
          end

          // -------------------------------------------------------------- //

          RSP_LONG: begin
            if (--cmd_bit_cntr >= 134) begin
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `LOW;  // S/T-bit
            end
            else if (cmd_bit_cntr >= 128) begin
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIGH; // reserved
            end
            else if (cmd_bit_cntr > 0) begin
              // register data
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX
                              rsp_tx.contents[3-cmd_bit_cntr/32]
                                             [cmd_bit_cntr % 32];
            end
            else if (cmd_bit_cntr == 0) begin
              error_gen_sem.get(1);
              if (error_gen.cmd_end_bit) begin
                sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `LOW;
                `DISPLAY_LOGGER_NOTE("error injected: CMD end bit")
              end
              else
                sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIGH; // E-bit
              error_gen.cmd_end_bit = `FALSE;
              mbx_rsp.get(rsp_null);
              error_gen_sem.put(1);
            end
            else begin // cmd_bit_cntr == -1
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIMP;
              cmd_bus_st = CMD_BUSY;
              cmd_bit_cntr = 8;
            end
          end

          // -------------------------------------------------------------- //

          RSP_SHORT: begin
            if (--cmd_bit_cntr >= 46) begin
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `LOW; // S/T-bit
            end
            else if (cmd_bit_cntr >= 40)
              // command index
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX
                                rsp_tx.index[cmd_bit_cntr-40];
            else if (cmd_bit_cntr >= 8)
              // register data
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX
                              rsp_tx.contents[0][cmd_bit_cntr-8];
            else if (cmd_bit_cntr > 0)
              // CRC
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX
                              rsp_tx_crc[cmd_bit_cntr];
            else if (cmd_bit_cntr == 0) begin
              bit spoil_end_bit = `FALSE;
              error_gen_sem.get(1);
              if (cmd_rx.index == 6'd12 || cmd_rx.index == 6'd23) begin
                spoil_end_bit = error_gen.cmd_end_bit_acmd;
                error_gen.cmd_end_bit_acmd = `FALSE;
              end
              else if (cmd_rx.index != 6'd19 && cmd_rx.index != 6'd21) begin
                spoil_end_bit = error_gen.cmd_end_bit;
                error_gen.cmd_end_bit = `FALSE;
              end
              error_gen_sem.put(1);
              if (spoil_end_bit) begin
                sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `LOW;
                `DISPLAY_LOGGER_NOTE("error injection: CMD end bit")
              end
              else
                sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIGH; // E-bit
              mbx_rsp.get(rsp_null);
              if (rsp_tx.switch2volt18) begin
                #0.5ns;
                cmd_bus_st = CMD_VOLT_SWITCH;
                dat_bus_st = DAT_VOLT_SWITCH;
                fork
                  do_voltage_switch;
                join_none
              end
            end
            else begin // cmd_bit_cntr == -1
              sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIMP;
              cmd_bus_st = CMD_BUSY;
              cmd_bit_cntr = 8;
            end
          end

          // -------------------------------------------------------------- //

          CMD_VOLT_SWITCH:
            sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `LOW;

          // -------------------------------------------------------------- //

          CMD_VOLT_SWITCH_END: begin
            sd_bus.cmd_o <= #`OUT_DELAY_CMD_MAX `HIGH;
            if (sd_bus.cmd_d === `HIGH)
            cmd_bus_st = CMD_IDLE;
          end

          // -------------------------------------------------------------- //

          CMD_BOOT_WAIT:
            if (sd_bus.cmd_d !== `LOW)
              cmd_bus_st = CMD_IDLE;
            else if (--cmd_bit_cntr <= 0) begin
              cmd_rx = new;
              cmd_rx.init_boot = `TRUE;
              `DISPLAY_INCOMING(cmd_rx.to_string)
              mbx_cmd.put(cmd_rx);
              mbx_rsp.get(rsp_tx);
              cmd_bus_st = CMD_BOOT_CONF;
            end

          // -------------------------------------------------------------- //

          CMD_BOOT_CONF:
            if (sd_bus.cmd_d !== `LOW) begin
              cmd_rx = new;
              cmd_rx.stop_boot = `TRUE;
              `DISPLAY_INCOMING(cmd_rx.to_string)
              mbx_cmd.put(cmd_rx);
              mbx_rsp.get(rsp_tx);
              cmd_bus_st = CMD_IDLE;
            end

          // -------------------------------------------------------------- //

          default: begin
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown SD XTOR cmd_bus_st: %s", cmd_bus_st))
            cmd_bus_st = CMD_BUSY;
            cmd_bit_cntr = 1;
          end
        endcase

      `ifdef STRICT_OUTPUT_WINDOW_CMD
        if (uses_fastest(this.bus_speed) && cmd_bus_st != CMD_VOLT_SWITCH &&
                                            cmd_bus_st != CMD_VOLT_SWITCH_END)
          sd_bus.cmd_o <= #(`OUT_DELAY_CMD_MAX + (uses_dynamic_cmd_fastest_out_window ?
              OUTPUT_WINDOW_FASTEST_DYNAMIC : OUTPUT_WINDOW_CMD_FASTEST_CONST)) `HIMP;
      `endif // STRICT_OUTPUT_WINDOW_CMD

        if (bus_speed==IDENT_SPEED || bus_speed==DEFAULT_SPEED )
          @(negedge sd_bus.rst_n, negedge sd_bus.clk_d); //ident/default speed
        else 
          @(negedge sd_bus.rst_n, posedge sd_bus.clk_d); // no DDR here           

        if (sd_bus.rst_n === `LOW)
          reset_dynamic_delays;
        else if (uses_fastest(this.bus_speed)) begin
          // measure the actual clock period
          if (last_clk_posedge != 0.0) begin
            tmp_period_prev =  tmp_period_last;
            tmp_period_last = ($realtime - last_clk_posedge);
            if (tmp_period_prev >= tmp_period_last) begin // to exclude cases when clock is stopped
              OUTPUT_DELAY_FASTEST_DYNAMIC       = 2 * tmp_period_last - 1ps;
              OUTPUT_WINDOW_FASTEST_DYNAMIC      = (emmc_mode ? 0.585 : 0.6) * tmp_period_last + 1ps;
              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR  = tmp_period_last / 2 - 2 * TIME_RQ + 1ps;
            end
          end
          last_clk_posedge = $realtime;
        end
      end
    endtask : cmd_bus_th

task low_voltage_init();

    @(posedge sd_bus.rst_n);

    @(posedge sd_bus.clk_d); //t3
    lvsi_imp_time = $realtime;
    if ((sd_bus.dat_d[0] != 0) || (sd_bus.dat_d[0] != 0) ||
        (sd_bus.dat_d[0] != 0) || (sd_bus.dat_d[0] != 0) || (sd_bus.cmd_d !=0)) begin
            `DISPLAY_LOGGER_NOTE("At least one DAT line or CMD line high. HVS Host. LVSI aborted")
            return;
    end
        
    @(negedge sd_bus.clk_d); //t4
    lvsi_imp_time = $realtime - lvsi_imp_time;
    $display("LVSI High clock pulse time: %t", lvsi_imp_time);
    
    if (lvsi_imp_time > 30us) begin
        assert_max_pulse_time: assert(0);
        mbx_lvs.put(1'b0);
    end
        
    if (lvsi_imp_time < 10us) begin
        `DISPLAY_LOGGER_NOTE("Clock high pulse shorter than 10us. Can be HVS Host. LVSI aborted")
        mbx_lvs.put(1'b0);
        return;
    end
    
    if ((lvsi_imp_time > 10us) && (sd_bus.cmd_d == 0) &&  (sd_bus.dat_d[0] == 0) 
                                                      &&  (sd_bus.dat_d[1] == 0)
                                                      &&  (sd_bus.dat_d[2] == 0)
                                                      &&  (sd_bus.dat_d[3] == 0)) begin
         `DISPLAY_LOGGER_NOTE("Recognized LVS Host")
          fork
              begin
                  #($urandom_range(5000,1)*1us);
                  sd_bus.dat_o[2] = 1'b1;
              end
              
              begin
                  @(posedge sd_bus.clk_d);
                  `DISPLAY_LOGGER_NOTE("Host drives clk during LVSI Execution!");
                  mbx_lvs.put(1'b0);
                  assert_no_clk_during_lvsi_exec: assert(0);
              end
                
          join_any
          disable fork;
          
             
          fork
              begin
                  @(posedge sd_bus.cmd_d);
              end
              
              begin
                  @(posedge sd_bus.clk_d);
                  `DISPLAY_LOGGER_NOTE( "Host drives clk before CMD line during LVSI (t6 -> t7)")
                  mbx_lvs.put(1'b0);
                  assert_no_clk_before_cmd_lvsi: assert(0);
              end
                
          join_any
          disable fork;
          
          for ( int ji = 0; ji < ($urandom_range(72,3)); ji++) begin
              @(posedge sd_bus.clk_d)
              sd_bus.dat_o[2] = 1'b1;
              if ((sd_bus.dat_d[0] != 1) || (sd_bus.dat_d[1] != 1) ||
                  (sd_bus.dat_d[3] != 1) || (sd_bus.cmd_d != 1)) begin
                 `DISPLAY_LOGGER_NOTE("CMD or DAT line not high before LVSI end") 
                 mbx_lvs.put(1'b0);
                 assert_drive_dat_and_cmd_lvsi: assert (0);
                  end                
          end
          mbx_lvs.put(1'b1);
          `DISPLAY_LOGGER_NOTE("LVSI completed")
          
       end
                                                      
    else if (sd_bus.cmd_d != 0) begin
            `DISPLAY_LOGGER_NOTE("High on CMD line (LVSI Execution phase")
            mbx_lvs.put(1'b0);
    end
    else if ((sd_bus.dat_d[0] != 0) || (sd_bus.dat_d[1] != 0) || (sd_bus.dat_d[2] != 0)||(sd_bus.dat_d[3] != 0)) begin
            `DISPLAY_LOGGER_NOTE("At least one DAT line high (LVSI Execution phase")
            mbx_lvs.put(1'b0);
    end

endtask : low_voltage_init
    // ==================================================================== //

    local int      dat_bit_cntr;

    sd_dat         dat_rx = null,
                   dat_tx = null,
                   dat_null;

    bit [7:0]      dat_tx_temp[$],
                   dat_rx_temp[$];
    bit [16:0]     dat_crc_temp[16];
    bit            dat_parity; // 0 in SDR, toggles in DDR
    bit            ddr_crc_parity;
    bit            crc_err_both;

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ //

    task inject_data_crc_error;
      error_gen_sem.get(1);
      if (error_gen.dat_crc && !$urandom_range(11)) begin
        dat_tx.crc_err |= `TRUE;
        error_gen.dat_crc = `FALSE;
        `DISPLAY_LOGGER_NOTE("error injection: DAT CRC")
      end
      error_gen_sem.put(1);
    endtask : inject_data_crc_error

    // -------------------------------------------------------------------- //

    task inject_data_end_bit_error(output bit inj_err);
      error_gen_sem.get(1);
      if (error_gen.dat_end_bit && !$urandom_range(11)) begin
        inj_err = `TRUE;
        error_gen.dat_end_bit = `FALSE;
        `DISPLAY_LOGGER_NOTE("error injection: DAT end bit")
      end
      error_gen_sem.put(1);
    endtask : inject_data_end_bit_error

    // -------------------------------------------------------------------- //

    task check_next_dat_tx_present;
      #0.3ns;
      if (mbx_dat_rd.try_peek(dat_tx)) begin
        if (dat_tx != null && dat_tx.data.size > 0) begin
          dat_bit_cntr = (dat_bus_st == SEND_END ? 0 : uses_ddr(this.bus_speed) ? 1 : 2);
          dat_tx.randomize_delay(this.bus_speed); // N_AC timing
          `DISPLAY_LOGGER_NOTE($sformatf("DAT delay: %0d cycle(s)", dat_tx.delay_cycles))
          dat_bus_st = SEND_WAIT;
          inject_data_crc_error;
          `DISPLAY_OUTGOING(dat_tx.to_string)
          if (uses_ddr(this.bus_speed))
            dat_parity = `TRUE;
        end
        else if (dat_tx.token) begin
          dat_bit_cntr = 0;
          dat_tx.randomize_delay(this.bus_speed); // N_CRC timing
          dat_bit_cntr -= (dat_tx.delay_cycles - 2);
          `DISPLAY_LOGGER_NOTE($sformatf("CRC delay: %0d cycle(s)", dat_tx.delay_cycles))
          dat_bus_st = SEND_FEEDBACK;
          inject_data_crc_error;
          `DISPLAY_OUTGOING(dat_tx.to_string)
          if (dat_tx.wr_dat_end)
            wr_dat_blklen = 0;
          // while sending CRC token, dat_parity toggles for HS400
          // stays HIGH for other DDR modes:
          if (uses_ddr(this.bus_speed))
            dat_parity = `TRUE;
          // in case of minimal timing we must start DS preamble here:
          if (this.bus_speed == HS400_EMMC && dat_bit_cntr == 0)
            sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) `LOW;
        end
        else begin
          `DISPLAY_OUTGOING(dat_tx.to_string)
          mbx_dat_rd.get(dat_null);
          if (dat_tx.busy) begin
            dat_bit_cntr = ((dat_bus_st == DAT_IDLE_CONF ||
                             dat_bus_st == DAT_IDLE) ? -1 : 0);
            dat_bus_st = SEND_BUSY;
          end
          if (dat_tx.wr_dat_end)
            wr_dat_blklen = 0;
          if (dat_tx.change_speed) begin
            if (uses_fastest(dat_tx.new_speed) && !uses_fastest(this.bus_speed))
              reset_dynamic_delays;
            this.bus_speed = dat_tx.new_speed;
            `ifdef USE_LOGGERS
              `DISPLAY_LOGGER_INFO($sformatf("Bus speed changed to: <b>%s</b> (completed)", bus_speed.name))
            `else // USE_LOGGERS
              `DISPLAY_LOGGER_INFO($sformatf("Bus speed changed to: %s (completed)", bus_speed.name))
            `endif // USE_LOGGERS
          end
          if (dat_tx.new_width != LERR) begin
            this.dat_bus_width = dat_tx.new_width;
            `ifdef USE_LOGGERS
              `DISPLAY_LOGGER_INFO($sformatf("Bus width changed to: <b>L%0d</b> (completed)", dat_bus_width))
            `else // USE_LOGGERS
              `DISPLAY_LOGGER_INFO($sformatf("Bus width changed to: L%0d (completed)", dat_bus_width))
            `endif // USE_LOGGERS
          end
          dat_tx = null;
        end
      end
      else begin
        dat_bus_st = (dat_bus_st == DAT_IDLE_CONF ? DAT_IDLE_CONF : DAT_IDLE);
        if (dat_bus_st == DAT_IDLE)
          dat_bit_cntr = 1;
      end
    endtask : check_next_dat_tx_present

    // -------------------------------------------------------------------- //

    task signal_interrupt(bit supress = `LOW, bit delay_correction = `FALSE);
      realtime delay = `OUT_DELAY_DAT_MAX;
      this.supress_debug = supress;
      if (delay_correction)
        delay -= 0.3ns;

      if (~sdio_mode);
      else if (~intr_output_n & (supress | intr_signal_n)) begin
        // interrupt ended or temporarily not to be signalled
        sd_bus.dat_o[1] <= #delay `HIGH;
        intr_output_n = `HIGH;
      end
      else if (~intr_signal_n & intr_output_n & ~supress) begin
        // interrupt status started
        sd_bus.dat_o[1] <= #delay `LOW;
        intr_output_n = `LOW;
      end
      else if (~intr_output_n)
        // interrupt currently to be signalled
        sd_bus.dat_o[1] <= #delay `LOW;
      else
        // no interrupt to be signalled
        sd_bus.dat_o[1] <= #delay `HIMP;
    endtask : signal_interrupt

    // -------------------------------------------------------------------- //

    local function bit is_interrupt(int lines);
      return (sdio_mode && ~intr_signal_n && (lines == 1));
    endfunction : is_interrupt

    // -------------------------------------------------------------------- //

    local task dat_bus_th;
      dat_bus_th_obj = process::self();
      #3ns;
      sd_bus.ds_o <= emmc_mode ? `HIMP : `UNKN;

      forever begin
      `ifdef STRICT_OUTPUT_WINDOW_DAT
        if (!uses_fastest(this.bus_speed) && dat_bus_st != DAT_VOLT_SWITCH &&
                                             dat_bus_st != DAT_VOLT_SWITCH_END &&
                                             dat_bus_st != SEND_BUSY)
          sd_bus.dat_o <= #`OUT_DELAY_DAT_MIN {8{`HIMP}};
      `endif // STRICT_OUTPUT_WINDOW_DAT

        if (sd_bus.rst_n === `LOW) begin
          sd_bus.dat_o <= {8{`HIMP}};
          sd_bus.dat_o <= #`OUT_DELAY_DAT_MAX {8{`HIMP}};
          dat_bus_st = DAT_IDLE;
          dat_bit_cntr = 1;
        end
        else
        case (dat_bus_st)
          DAT_IDLE,
          DAT_IDLE_CONF: begin
            bit delay_correction = `FALSE;
            sd_bus.dat_o <= #`OUT_DELAY_DAT_MAX {8{`HIMP}};
            if (dat_parity && bus_speed == HS400_EMMC)
              sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) `HIMP;
            dat_parity = `FALSE;

            if (dat_bus_st == DAT_IDLE) begin
              if ((sd_bus.dat_d[0] === `HIGH || sd_bus.dat_d[0] === `HIMP) &&
                  (sd_bus.dat_d[1] === `HIGH || sd_bus.dat_d[1] === `HIMP || sdio_mode) && // might be LOW due to INTR
                  (sd_bus.dat_d[2] === `HIGH || sd_bus.dat_d[2] === `HIMP) &&
                  (sd_bus.dat_d[3] === `HIGH || sd_bus.dat_d[3] === `HIMP) &&
                  (sd_bus.dat_d[4] === `HIGH || sd_bus.dat_d[4] === `HIMP) &&
                  (sd_bus.dat_d[5] === `HIGH || sd_bus.dat_d[5] === `HIMP) &&
                  (sd_bus.dat_d[6] === `HIGH || sd_bus.dat_d[6] === `HIMP) &&
                  (sd_bus.dat_d[7] === `HIGH || sd_bus.dat_d[7] === `HIMP) &&
                   dat_bit_cntr-- == 0)
                dat_bus_st = DAT_IDLE_CONF;
            end
            else if (wr_dat_blklen > 0 && sd_bus.dat_d[0] === `LOW) begin // S-bit
              int dat_lines_in_use = (sd_bus.dat_d[7:0] === {8{`LOW}} ? 8 :
                                      sd_bus.dat_d[3:0] === {4{`LOW}} ? 4 : 1);
              if (supress_all_checks==0) begin
	              a_incorrect_write_data_width: assert (dat_bus_width === dat_lines_in_use) 
		      else `DISPLAY_LOGGER_ERROR($sformatf({"Actual write data width is inconsistent with current card settings; ", "expected %0d found %0d"}, dat_bus_width, dat_lines_in_use));
	      end
              dat_bit_cntr = 8;
              dat_bus_st = REC_DATA;
              dat_rx_temp = uses_ddr(this.bus_speed) ? '{8'h00, 8'h00} : '{8'h00};
              for (int i = 0; i < dat_bus_width * (uses_ddr(this.bus_speed) ? 2 : 1); ++i)
                dat_crc_temp[i] = 17'b00000000000000000;
            end
            else begin
              check_next_dat_tx_present; // can change dat_bus_st to be used in next cycle
              delay_correction = `TRUE;
            end

            signal_interrupt(dat_bus_width > 1 &&
                ((dat_bus_st != DAT_IDLE && dat_bus_st != DAT_IDLE_CONF) || wr_dat_blklen > 0),
                  delay_correction);
          end

          // -------------------------------------------------------------- //

          SEND_WAIT: begin
            if (dat_tx.data.size < (uses_ddr(this.bus_speed) ? 2 : 1)) begin
              dat_bus_st = DAT_IDLE;
              dat_bit_cntr = 1;
              a_incorrect_read_data_blk_length: assert (0) else
              `DISPLAY_LOGGER_ERROR("Internal card model error: incorrect read data block length")
            end
            else begin
              a_incorrect_read_data_width:
              assert (dat_bus_width === dat_tx.lines) else `DISPLAY_LOGGER_ERROR(
                  "Internal card model error: incorrect read data width")
              if (dat_tx.lines == 1)
                signal_interrupt;
              for (int i = 0; i < dat_tx.lines; ++i)
                sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIGH; // P-bit
              for (int i = is_interrupt(dat_tx.lines) ? 2 : dat_tx.lines; i < 8; ++i)
                sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIMP;
            `ifdef STRICT_OUTPUT_WINDOW_DAT
              if (uses_fastest(this.bus_speed))
                sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                    bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                    uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                           OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
            `endif // STRICT_OUTPUT_WINDOW_DAT
            end
            #0.3ns;
            if (mbx_dat_rd.num() == 0)
              dat_bus_st = SEND_END; // transfer cancelled
            else if (++dat_bit_cntr < dat_tx.delay_cycles);
            else begin
              dat_bus_st = SEND_START;
              if (bus_speed == HS400_EMMC)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) `LOW; // preamble
            end
          end

          // -------------------------------------------------------------- //

          SEND_START: begin
            if (uses_ddr(this.bus_speed)) begin
              if (bus_speed == HS400_EMMC)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) dat_parity;
              dat_parity = ~dat_parity;
            end
            case (dat_tx.lines)
              1, 4, 8: begin
                if (~uses_ddr(this.bus_speed) || ~dat_parity || this.bus_speed inside {DDR50, HS400_EMMC}) begin
                  for (int i = 0; i < dat_tx.lines; ++i)
                    sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `LOW; // S-bit
                  for (int i = is_interrupt(dat_tx.lines) ? 2 : dat_tx.lines; i < 8; ++i)
                    sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIMP;
                  for (int i = 0; i < dat_tx.lines * (uses_ddr(this.bus_speed) ? 2 : 1); ++i)
                    dat_crc_temp[i] = 17'b00000000000000000;
                  if (dat_tx.lines == 1)
                    signal_interrupt;
                `ifdef STRICT_OUTPUT_WINDOW_DAT
                  if (uses_fastest(this.bus_speed))
                    sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                        bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                        uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                               OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
                `endif // STRICT_OUTPUT_WINDOW_DAT
                end
                if (~uses_ddr(this.bus_speed) | dat_parity) begin
                  #0.3ns;
                  if (mbx_dat_rd.num() == 0)
                    dat_bus_st = SEND_END; // transfer cancelled
                  else begin
                    dat_bus_st = SEND_DATA;
                    dat_bit_cntr = 8;
                    dat_tx_temp = dat_tx.data;
                  end
                end
              end

              default: begin // incorrect
                dat_bus_st = DAT_IDLE;
                dat_bit_cntr = 1;
              end
            endcase
          end

          // -------------------------------------------------------------- //

          SEND_DATA: begin
            if (uses_ddr(this.bus_speed)) begin
              if (bus_speed == HS400_EMMC)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) dat_parity;
              dat_parity = ~dat_parity;
            end
            for (int i = dat_tx.lines - 1; i >= 0; --i) begin
              --dat_bit_cntr;
              sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX
                                 dat_tx_temp[dat_parity ? 1 : 0][dat_bit_cntr];
              dat_crc_temp[i+(dat_parity ? dat_tx.lines : 0)] <<= 1;
              if (dat_tx_temp[dat_parity ? 1 : 0][dat_bit_cntr] ^
                 dat_crc_temp[i+(dat_parity ? dat_tx.lines : 0)][16])
                 dat_crc_temp[i+(dat_parity ? dat_tx.lines : 0)] ^= crc16_gen_polynom;
            end
            if (dat_tx.lines == 1)
              signal_interrupt;
          `ifdef STRICT_OUTPUT_WINDOW_DAT
            if (uses_fastest(this.bus_speed)) begin
              if (dat_tx.tuning_block &&
                   (dat_tx.lines == 8 ?  dat_tx_temp[0] === {8{`LOW}}       :
                    dat_tx.lines == 4 ? (dat_bit_cntr == 4 ?
                                         dat_tx_temp[0][7:4] === {4{`LOW}}  :
                                         dat_tx_temp[0][3:0] === {4{`LOW}}) :
                                         `LOW ));
              // ^^ necessary in order that tuning block can be detected by host
              else
                sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                    bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                    uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                           OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
            end
          `endif // STRICT_OUTPUT_WINDOW_DAT

            if (uses_ddr(this.bus_speed) & ~dat_parity)
              // we need repeat line counting for next half cycle:
              dat_bit_cntr += dat_tx.lines;
            else begin
              #0.3ns;
              if (mbx_dat_rd.num() == 0) // transfer cancelled
                dat_bus_st = SEND_END;
              else if (dat_bit_cntr == 0) begin
                dat_tx_temp.delete(0);
                if (uses_ddr(this.bus_speed))
                  dat_tx_temp.delete(0);
                if (dat_tx_temp.size > (uses_ddr(this.bus_speed) ? 1 : 0))
                  dat_bit_cntr = 8;
                else begin
                  dat_bit_cntr = 16;
                  dat_bus_st = SEND_CRC;
                  if (dat_tx.crc_err) begin
                    // intentional error injection:
                    int err_index = $urandom % (dat_tx.lines * (uses_ddr(this.bus_speed) ? 2 : 1));
                    dat_crc_temp [err_index] ^= ($urandom % 16'hFFFF) + 1'b1;
                         
	                if (uses_ddr(this.bus_speed)) begin
		                crc_err_both = ($urandom_range(1));
		                if (crc_err_both) begin
		                  if (err_index < dat_tx.lines)
			                dat_crc_temp [err_index + dat_tx.lines] ^= ($urandom % 16'hFFFF) + 1'b1;  
		                  else
			                dat_crc_temp [err_index - dat_tx.lines] ^= ($urandom % 16'hFFFF) + 1'b1;   
		             end
		                		                
                      if (err_index > dat_tx.lines)
		                  ddr_crc_parity = 1'b1;
                      else
		                  ddr_crc_parity = 1'b0;
                      
                      cg_ddr_crc_error.sample();
	                end
                  end
                end
              end
            end
          end

          // -------------------------------------------------------------- //

          SEND_CRC: begin
            if (uses_ddr(this.bus_speed)) begin
              if (bus_speed == HS400_EMMC)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) dat_parity;
              dat_parity = ~dat_parity;
            end
            if (!dat_parity)
              --dat_bit_cntr;
            for (int i = 0; i < dat_tx.lines; ++i) begin
              sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX
                              dat_crc_temp[i+(dat_parity ? dat_tx.lines : 0)]
                                          [dat_bit_cntr];
            if (dat_tx.lines == 1)
              signal_interrupt;
          `ifdef STRICT_OUTPUT_WINDOW_DAT
            if (uses_fastest(this.bus_speed))
              sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                  bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                  uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                         OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
          `endif // STRICT_OUTPUT_WINDOW_DAT
            end

            if (~uses_ddr(this.bus_speed) | dat_parity) begin
              #0.3ns;
              if (dat_bit_cntr == 0 || mbx_dat_rd.num() == 0)
                // transfer ^^ finished or cancelled ^^
                dat_bus_st = SEND_END;
            end
          end

          // -------------------------------------------------------------- //

          SEND_END: begin
            if (uses_ddr(this.bus_speed)) begin
              if (bus_speed == HS400_EMMC)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) dat_parity;
              dat_parity = ~dat_parity;
            end
            if (~uses_ddr(this.bus_speed) || ~dat_parity /*|| this.bus_speed == HS400_EMMC*/) begin
              bit inj_err = `FALSE;
              inject_data_end_bit_error(inj_err);
              if (inj_err) begin
                bit [7:0] end_bit = (dat_tx.lines == 1 ? 8'd0 : $random % ((1 << dat_tx.lines) - 1));
                for (int i = 0; i < dat_tx.lines; ++i)
                  sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX end_bit[i];
              end
              else
                for (int i = 0; i < dat_tx.lines; ++i)
                  sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIGH; // E-bit

              if (dat_tx.lines == 1)
                signal_interrupt;
              for (int i = is_interrupt(dat_tx.lines) ? 2 : dat_tx.lines; i < 8; ++i)
                sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIMP;

            `ifdef STRICT_OUTPUT_WINDOW_DAT
              if (uses_fastest(this.bus_speed))
                sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                    bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                    uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                           OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
            `endif // STRICT_OUTPUT_WINDOW_DAT
            end
            if (!uses_ddr(this.bus_speed) || dat_parity) begin
              // remove what has just been sent
              void'(mbx_dat_rd.try_get(dat_null));
              dat_tx = null;
              check_next_dat_tx_present; // can change dat_bus_st to be used in next cycle
              if (dat_bus_st == SEND_WAIT && sdio_mode && ~intr_signal_n && dat_tx.lines > 1) begin
                dat_bit_cntr = 0;
                dat_bus_st = SEND_INTR;
              end
            end
          end

          // -------------------------------------------------------------- //

          REC_DATA,
          REC_CRC:
          begin
            if (dat_bus_st == REC_CRC && ~dat_parity)
              --dat_bit_cntr;
            if (dat_bit_cntr >= 0)
              for (int i = dat_bus_width - 1; i >= 0; --i) begin
                if (dat_bus_st == REC_DATA) begin
                  --dat_bit_cntr;
                  if (uses_ddr(this.bus_speed))
                    dat_rx_temp
                    [$-(dat_parity ? 0 : 1)][dat_bit_cntr] = sd_bus.dat_d[i];
                  else
                    dat_rx_temp[$][dat_bit_cntr] = sd_bus.dat_d[i];
                end
                dat_crc_temp[i+(dat_parity ? dat_bus_width : 0)] <<= 1;
                if (sd_bus.dat_d[i] ^
                    dat_crc_temp[i+(dat_parity ? dat_bus_width : 0)][16])
                  dat_crc_temp[i+(dat_parity ? dat_bus_width : 0)] ^= crc16_gen_polynom;
              end
            if (uses_ddr(this.bus_speed) && dat_bit_cntr >= 0)
              dat_parity = ~dat_parity;
            if (dat_bus_width == 1)
              signal_interrupt;

            if (dat_parity) begin
              if (dat_bus_st == REC_DATA)
                dat_bit_cntr += dat_bus_width;
            end
            else begin
              if (dat_bit_cntr == (uses_ddr(this.bus_speed) ? -3 : -2))
                check_next_dat_tx_present;
              else if (mbx_dat_rd.try_peek(dat_tx)) begin
                if (dat_tx.wr_dat_end & ~dat_tx.token) begin
                  // transfer cancelled
                  dat_bus_st = REC_CANCELLED;
                  wr_dat_blklen = 0;
                  dat_bit_cntr = 2;
                  mbx_dat_rd.get(dat_null);
                  dat_tx = null;
                end
              end
              else if (dat_bit_cntr == 0) begin
                if (dat_bus_st == REC_CRC) begin
                  dat_rx = new (`FALSE, `TRUE, dat_bus_width);
                  dat_rx.crc_err = `FALSE;
                  for (int i = 0; i < dat_rx.lines * (uses_ddr(this.bus_speed) ? 2 : 1) &&
                                  !dat_rx.crc_err; ++i)
                    dat_rx.crc_err |= (dat_crc_temp[i][15:0] != 16'h0000);
                  dat_rx.data = dat_rx_temp;
                  `DISPLAY_INCOMING(dat_rx.to_string)
                  mbx_dat_wr.put(dat_rx);
                end
                else begin
                  if (wr_dat_blklen - dat_rx_temp.size > (uses_ddr(this.bus_speed) ? 1 : 0)) begin
                    dat_rx_temp.push_back(8'h00);
                    if (uses_ddr(this.bus_speed))
                      dat_rx_temp.push_back(8'h00);
                    dat_bit_cntr = 8;
                  end
                  else begin
                    dat_bus_st = REC_CRC;
                    dat_bit_cntr = 16;
                  end
                end
              end
            end
          end

          // -------------------------------------------------------------- //

          REC_CANCELLED: begin
            if (dat_bus_width == 1)
              signal_interrupt;
            if (--dat_bit_cntr == 0)
              check_next_dat_tx_present;
          end

          // -------------------------------------------------------------- //

          SEND_FEEDBACK: begin
            // dat_parity toggles in HS400 but ...
	    if (bus_speed == DEFAULT_SPEED)
	      busy_sig_count = 6;
	    else
	      busy_sig_count = 5;
	    
            if (bus_speed == HS400_EMMC) begin
              if (dat_bit_cntr >= 0)
                sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) dat_parity;
              dat_parity = ~dat_parity;
            end
            if (~dat_parity | ~uses_fastest(this.bus_speed))
            // just stays HIGH in DDR modes different than HS400
              dat_bit_cntr++;
            if (dat_bit_cntr < busy_sig_count) begin
              if (this.bus_speed != HS400_EMMC || dat_bit_cntr == 1 || ~dat_parity)
              // in HS400 only start bit last through the entire cycle ^^
	      if (bus_speed == DEFAULT_SPEED) begin 
                  case (dat_bit_cntr)
                    2:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX `LOW; // S-bit
                    3, 5:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX dat_tx.crc_err;
                    4:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX ~dat_tx.crc_err;
                  endcase
              end
              else begin
		   case (dat_bit_cntr)
                    1:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX `LOW; // S-bit
                    2, 4:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX dat_tx.crc_err;
                    3:
                      sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX ~dat_tx.crc_err;
                  endcase
              end
                  

              if (dat_bus_width == 1 || wr_dat_blklen == 0)
                signal_interrupt;
              else if (sdio_mode & (~intr_signal_n | ~intr_output_n))
                case (dat_bit_cntr)
                  1: begin
                    sd_bus.dat_o[1] <= #`OUT_DELAY_DAT_MAX `LOW;
                    intr_output_n = `LOW;
                  end
                  2:
                    sd_bus.dat_o[1] <= #`OUT_DELAY_DAT_MAX `HIGH;
                  3: begin
                    sd_bus.dat_o[1] <= #`OUT_DELAY_DAT_MAX `HIMP;
                    intr_output_n = `HIGH;
                  end
                endcase

              #0.3ns;
              if (!mbx_dat_rd.try_peek(dat_tx)) begin
                // transfer cancelled manner #1
                // if we are here, mbx_dat_rd is empty: mbx_dat_rd.num() == 0
                dat_bus_st = SEND_BUSY;
                dat_bit_cntr = 0;
              end
              else if (~dat_tx.token & dat_tx.wr_dat_end) begin
                // transfer cancelled manner #2
                dat_bus_st = SEND_BUSY;
                dat_bit_cntr = 0;
                if (dat_tx.wr_dat_end)
                  wr_dat_blklen = 0;
                void'(mbx_dat_rd.try_get(dat_null));
                dat_tx = null;
              end
            end
            else begin
              if (this.bus_speed != HS400_EMMC || ~dat_parity) begin
                bit inj_err = `FALSE;
                inject_data_end_bit_error(inj_err);
                sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX inj_err ? `LOW : `HIGH; // E-bit
              end

              if (dat_bus_width == 1 || wr_dat_blklen == 0)
                signal_interrupt;
              if (bus_speed != HS400_EMMC || dat_parity) begin
                void'(mbx_dat_rd.try_get(dat_null));
                dat_bus_st   = dat_tx.busy ? SEND_BUSY : DAT_IDLE;
                dat_bit_cntr = dat_tx.busy ? 0 : 1;
                dat_tx = null;
              end

              if (dat_bus_st == DAT_IDLE) begin
                #0.3ns;
                if (mbx_dat_rd.try_peek(dat_tx) && dat_tx != null &&
                    (dat_tx.busy | dat_tx.wr_dat_end) && dat_tx.data.size == 0) begin
                  `DISPLAY_OUTGOING(dat_tx.to_string)
                  dat_bus_st = SEND_BUSY;
                  dat_bit_cntr = 0;
                  if (dat_tx.wr_dat_end)
                    wr_dat_blklen = 0;
                  mbx_dat_rd.get(dat_null);
                  dat_tx = null;
                end
              end
            end
          `ifdef STRICT_OUTPUT_WINDOW_DAT
            if (uses_fastest(this.bus_speed))
              sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                  bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                  uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                         OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
          `endif // STRICT_OUTPUT_WINDOW_DAT
          end

          // -------------------------------------------------------------- //

          SEND_BUSY: begin
            if (dat_parity && bus_speed == HS400_EMMC)
              sd_bus.ds_o <= #(`OUT_DELAY_DAT_MAX - TIME_RQ) `HIMP;
            if (++dat_bit_cntr > 2 && mbx_dat_rd.try_peek(dat_tx) && dat_tx != null) begin
              if ((dat_tx.busy | dat_tx.wr_dat_end) && dat_tx.data.size == 0) begin
                `DISPLAY_OUTGOING(dat_tx.to_string)
                if (dat_tx.wr_dat_end)
                  wr_dat_blklen = 0;
                mbx_dat_rd.get(dat_null);
                dat_tx = null;
              end
              else begin
                dat_bus_st = DAT_IDLE;
                dat_bit_cntr = 1;
              end
            end
            if (dat_bus_width == 1 || wr_dat_blklen == 0)
              signal_interrupt;
            if (dat_bit_cntr == 1 || dat_bus_st == DAT_IDLE) begin
              if (dat_bus_st == SEND_BUSY) begin
                sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX `LOW;  // S/L-bit
                if (dat_parity)
                  dat_parity = ~dat_parity;
              end
              else
                sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX `HIGH; // E-bit
            end
          end

          // -------------------------------------------------------------- //

          SEND_INTR: begin
            case (++dat_bit_cntr)
              1, 2:
                for (int i = 0; i < dat_tx.lines; ++i)
                  sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIGH;
              3: begin
                sd_bus.dat_o[0] <= #`OUT_DELAY_DAT_MAX `HIGH;
                sd_bus.dat_o[1] <= #`OUT_DELAY_DAT_MAX `LOW; // intr!
                for (int i = 2; i < dat_tx.lines; ++i)
                  sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIGH;
              end
              4: begin
                for (int i = 0; i < dat_tx.lines; ++i)
                  sd_bus.dat_o[i] <= #`OUT_DELAY_DAT_MAX `HIGH;
                dat_bus_st = SEND_WAIT;
              end
            endcase
          `ifdef STRICT_OUTPUT_WINDOW_DAT
            if (uses_fastest(this.bus_speed))
              sd_bus.dat_o <= #(`OUT_DELAY_DAT_MAX + (
                  bus_speed == HS400_EMMC ?              OUTPUT_WINDOW_FASTEST_DYNAMIC_DDR :
                  uses_dynamic_dat_fastest_out_window ?  OUTPUT_WINDOW_FASTEST_DYNAMIC     :
                                                         OUTPUT_WINDOW_DAT_FASTEST_CONST)) {8{`HIMP}};
          `endif // STRICT_OUTPUT_WINDOW_DAT
          end

          // -------------------------------------------------------------- //

          DAT_VOLT_SWITCH:
            sd_bus.dat_o[3:0] <= #`OUT_DELAY_DAT_MAX {4{`LOW}};

          // -------------------------------------------------------------- //

          DAT_VOLT_SWITCH_END: begin
            sd_bus.dat_o[3:0] <= #`OUT_DELAY_DAT_MAX {4{`HIGH}};
            dat_bus_st = DAT_IDLE;
            dat_bit_cntr = 1;
          end

          // -------------------------------------------------------------- //

          default: begin
            `DISPLAY_LOGGER_WARNING($sformatf(
                "unknown SD XTOR dat_bus_st: %s", dat_bus_st))
            dat_bus_st = DAT_IDLE;
            dat_bit_cntr = 1;
          end
        endcase

        
        if (bus_speed==IDENT_SPEED || bus_speed==DEFAULT_SPEED )
          @(negedge sd_bus.rst_n, negedge sd_bus.clk_d); //ident/default speed
        else begin
          // ddr/sdr clock selection:
          if (dat_parity)
            @(negedge sd_bus.rst_n, negedge sd_bus.clk_d);
          else
            @(negedge sd_bus.rst_n, posedge sd_bus.clk_d);
        end
      end
    endtask : dat_bus_th

    // ==================================================================== //

    local task intr_signal_th;
      intr_signal_th_obj = process::self();
      forever
        if (sd_bus.rst_n === `LOW) begin
          while (mbx_intr.try_get(intr_signal_n));
          intr_signal_n = `HIGH;
          intr_output_n = `HIGH;
          wait (sd_bus.rst_n === `HIGH);
        end
        else
          fork
            fork
              mbx_intr.get(intr_signal_n);
              wait (sd_bus.rst_n === `LOW);
            join_any
            disable fork;
          join
    endtask : intr_signal_th

    // ==================================================================== //

    task do_voltage_switch;
      automatic bit clk_stopped = `FALSE;
      fork
        while (!clk_stopped) begin
          fork : wait_for_clk_stopped
            begin
              #100ns;
              @(sd_bus.clk_d);
            end
            begin
              #10us;
              clk_stopped = `TRUE;
            end
          join_any
          disable fork;
        end
      join

      repeat (11) @(posedge sd_bus.clk_d);
      case (bus_speed)
        DEFAULT_SPEED: bus_speed = SDR12;
        HIGH_SPEED:    bus_speed = SDR25;
      endcase
      `DISPLAY_LOGGER_INFO($sformatf(
          "Bus speed changed to: %s", bus_speed.name))

      repeat (33) @(posedge sd_bus.clk_d);
      #9ns cmd_bus_st = CMD_VOLT_SWITCH_END;

      repeat (22) @(posedge sd_bus.clk_d);
      #9ns dat_bus_st = DAT_VOLT_SWITCH_END;
    endtask : do_voltage_switch

    covergroup cg_ddr_crc_error;
	cp_crc_parity : coverpoint ({ddr_crc_parity, crc_err_both}) {
		bins bin_error_even = {{1'b1, 1'b0}};
		bins bin_error_odd = {{1'b0, 1'b0}};
	}
	cp_crc_err_both : coverpoint (crc_err_both) {
		bins bin_error_both = {1'b1};
	}
    endgroup : cg_ddr_crc_error
    
  endclass : sd_xtor_cl
endpackage : sd_xtor_pkg
