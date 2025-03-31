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
//   UHS-II packet object
//   
//   File contents  : package uhsii_pkt_pkg
//                    class   uhsii_pkt_cl                                   
//------------------------------------------------------------------------------

`include "sv_macros.svh"

//`define PRINT_ALL_RAW_BYTES
`define META_INFO_DISPLAY

package uhsii_pkt_pkg;

  import tb_pkg::*;
  import uhsii_params_pkg::*;

  /** UHSII pkt direction. */
  typedef enum bit [1:0] {UNKN_DIR, INCOMING, OUTGOING} pkt_dir_e;

  /** UHSII pkt type. */

  typedef enum bit [2:0] {
    UNKN_PKT,
    CCMD_PKT,
    DCMD_PKT,
    RES_PKT,
    DATA_PKT,
    DATA_PKT_2L,
    MSG_PKT,
    META_PKT // meta info for XTOR only
  } pkt_type_e;

  typedef struct packed {
    pkt_dir_e            pkt_dir;
    bit                  sdb, edb;
    bit                  decode_error;
    bit                  crc_error;
    pkt_type_e           pkt_type;
    bit                  np;
    bit                  broadcast;
    bit [2:0]            trans_id;
    // CCMD
    bit                  rw;
    bit [1:0]            plen;
    bit [11:0]           ioadr;
    // DCMD
    bit                  dm, lm, tlum, dam; // TMODE
    bit [31:0]           dadr, tlen;
    // RES
    bit                  nak;
    bit [2:0]            ecode;
    bit [14:0]           cmd_echo;
    // payload
    int                  payload_index;
    int                  payload_length;
    int                  pads;
    bit [31:0]           first_pld_dword;
    // MSG
    bit [2:0]            ctg;
    bit [3:0]            idx;
    bit                  rec_err;
    bit                  urec_err;
    // 2L-HD only:
    bit                  init_2lhd_in;
    bit                  init_2lhd_out;
    // non-native only:
    bit                  app;
    bit [5:0]            cmd_index;
    bit [31:0]           sd_arg;
  } uhsii_pkt_struct ;

  class lss_params_cl;
    const int           n_lss_dir;
    const int           n_lss_syn;
    const int           n_data_gap;
    const bit [1:0]     range;
    const bit           lpm;
    const int           n_fcu;
    const int           max_blklen;
    const bit [1:0]     max_retry_num;

    /** Constructor with defaults. */
    function new(input int           _n_lss_dir        = 8,
                 input int           _n_lss_syn        = 16,
                 input int           _n_data_gap       = 2,
                 input bit [1:0]     _range            = 0,
                 input bit           _lpm              = 0,
                 input int           _n_fcu            = 16,
                 input int           _max_blklen       = 512,
                 input bit [1:0]     _max_retry_num    = 3);
      n_lss_dir         = _n_lss_dir;
      n_lss_syn         = _n_lss_syn;
      n_data_gap        = _n_data_gap;
      range             = _range;
      lpm               = _lpm;
      n_fcu             = _n_fcu;
      max_blklen        = _max_blklen;
      max_retry_num     = _max_retry_num;
    endfunction : new

    function string to_string();
      if (this == null)
        return "NULL";
      $swrite(to_string,
        "N_LSS_DIR=%d N_LSS_SYN=%d N_DATA_GAP=%d RANGE=%b LPM=%b",
        this.n_lss_dir, this.n_lss_syn, this.n_data_gap,
        this.range,     this.lpm );
      $swrite(to_string,
        "%s N_FCU=%d MAX_BLKLEN=%d", to_string, this.n_fcu, this.max_blklen);
    endfunction : to_string
  endclass : lss_params_cl

// =========================  UHSII PKT CLASS  =========================== //

  class uhsii_pkt;

    // - - - -  CRC calc  - - - - - - - - - - - - - - - - - - - - - - - - - //

    static const bit [16:0] crc_gen_polynom = 17'b10001000000100001;

    // - - - - scrambling - - - - - - - - - - - - - - - - - - - - - - - - - //

    // x^16 + x^5 + x^4 + x^3 + 1
    static const bit [16:0] scramble_polynom = 17'b10000000000111001;
    static       bit [16:0] lsfr_temp;
    static bit       [7:0]  scramble_pattern[$];
    /* last element in scramble_pattern is always invalid:
       it is not a real scramble patter but conserved LSFR state */

    static function void ensure_scramble_pattern_length(int length);
      if (length > scramble_pattern.size-1) begin
        if (scramble_pattern.size >= 2) begin
          // load previous calc onto lsfr: last -> [7:0], penultimate -> [15:8]
          lsfr_temp[7:0]  = revert(scramble_pattern.pop_back());
          lsfr_temp[15:8] = revert(scramble_pattern[$]);
        end
        else begin
          lsfr_temp = 17'h0FFFF;
          scramble_pattern = {};
          scramble_pattern.push_back(8'hFF);
        end

        while (length > scramble_pattern.size) begin
          repeat (8) begin
            lsfr_temp <<= 1;
            if (lsfr_temp[16])
              lsfr_temp ^= scramble_polynom;
          end
          scramble_pattern.push_back(revert(lsfr_temp[15:8]));
        end
        scramble_pattern.push_back(revert(lsfr_temp[7:0]));
      end
    endfunction : ensure_scramble_pattern_length

    // for debug purposes only
    static function void display_scramble_pattern();
      $display("display_scramble_pattern");
      for (int i = 0; i < scramble_pattern.size; ++i)
        $display("%h", scramble_pattern[i]);
    endfunction : display_scramble_pattern

    // = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = //

    // *** low-level pkt fields ***

    bit [8:0]  data[];        // may contain PAD, never cointains CRC
    bit [15:0] crc_act,       // actual CRC: can contain errors
               crc_exp;       // expected CRC: always correct
  
    bit       crc_act_exists; // whether crc_actual contains accessible data
    bit       crc_exp_exists; // whether crc_expected contains accessible data

    bit       crc_error;      // CRC is incorrect?

    uhsii_pkt odd_data_pkt;   // handle to a corresponding odd data pkt
                              // in 2L-HD; if non-null, this pkt is 2L-HD
                              // even data pkt

    pkt_dir_e pkt_dir = UNKN_DIR;

    bit        sdb, edb;    // start/end of data burst flags

    // *** higher-level packet fields ***

    bit decode_error;
    bit sent;
  
    // header:
    pkt_type_e         pkt_type;
    bit                np;
    bit [3:0]          dest_id;
    bit [3:0]          src_id;
    bit [2:0]          trans_id;

    // CCMD

    bit                rw;
    bit [1:0]          plen;
    bit [11:0]         ioadr;

    // DCMD

    bit                dm, lm, tlum, dam; // TMODE
    bit [31:0]         dadr, tlen;

    // RES

    bit                nak;
    bit [2:0]          ecode;
    bit [14:0]         cmd_echo;

    // payload -- (fields not changed while 2L-HD split!)

    int payload_index;  // index of first byte of payload within data array
    int payload_length; // payload length in bytes
    int pads = 0;       // number of dected PADs, appended to data in DATA_PKT

    // MSG
    bit [2:0] ctg;
    bit [3:0] idx;
    bit rec_err;
    bit urec_err;

    // non-native only:
    bit                app;
    bit [5:0]          cmd_index;
    int                sd_arg;

    // meta data (directives for/from xtor):

    bit                go4reset;      // full reset command received
    bit                go2dormant;    // go to dormant command received
    bit                switch2didl;
    bit                switch2lidl;
    bit                power_cycle;   // power cycle or reset from pin
    bit                repeat_msg;    // set for the first one of two msg copies to tell
                                      // XTOR to start sending the next copy immediately

    // 2L-HD only:
    bit                init_2lhd_in;
    bit                init_2lhd_out;

    // error injection:
    bit                sop_error;
    bit                eop_error;
    bit                payload_error;
    bit                change_type;
    
  
    lss_params_cl change_params;  // new param set to be used by xtor

    function new;
      data              = new[0];
      crc_act_exists    = `FALSE;
      crc_exp_exists    = `FALSE;
      crc_error         = `FALSE;
  
      pkt_dir           =  UNKN_DIR;
      sdb               =  `FALSE;
      edb               =  `FALSE;
  
      pkt_type          =  UNKN_PKT;
      decode_error      =  `FALSE;
      payload_index     =  -1;
      payload_length    =  0;

      odd_data_pkt      = null;
      change_params     = null;
    endfunction : new

    // *** raw data access ***

    function void add_rec_data(ref bit [8:0] rec_bytes[$],
                               input bit is_scrambled = `TRUE);
      if (rec_bytes.size >= 3) begin
        data = new [rec_bytes.size - 2];
        for (int i = 0; i < data.size; ++i)
          data[i] = rec_bytes[i];
      end
      if (rec_bytes.size >= 2) begin
        crc_act[15:8]  = rec_bytes[$-1];
        crc_act[7:0]   = rec_bytes[$];
        crc_act_exists = `TRUE;
      end
      rec_bytes = {};
      pkt_dir        =  INCOMING;
      if (is_scrambled) this.scramble;
    endfunction : add_rec_data

    function string to_string;
      int act_len;
      if (this == null)
        return "NULL";
      act_len = this.data.size - this.pads;

    `ifdef USE_LOGGERS
      $swrite(to_string,
        "<i>%s</i> %s pkt <b>%s</b>\t%s\tlen=%d trans=%h src_id=%h dest_id=%h",
        pkt_dir.name, np ? "NP" : "SD", pkt_type.name,
        decode_error ? "ERROR!" :
        (sdb & edb) ? "S+EDB" : sdb ? "SDB" : edb ? "EDB" :
        pkt_type == MSG_PKT ? (
          ctg == MSG_CTG_LMSG ? (
            idx == LMSG_IDX_FCREQ ? "FCREQ" :
            idx == LMSG_IDX_FCRDY ? "FCRDY" :
            idx == LMSG_IDX_STAT  ? "STAT"  : ""
          ) :
          ctg == MSG_CTG_AMSG ? (
            idx == AMSG_IDX_EBSY  ? "EBSY! " : ""
          ) : ""
        ) :
        pkt_type == CCMD_PKT ?
          $sformatf("%s io=%3h plen=%2b", rw ? "wr" : "rd", ioadr, plen) : "",
        act_len, trans_id, src_id, dest_id );
    `else // USE_LOGGERS
      $swrite(to_string,
        "%s %s pkt %s\t%s\tlen=%d trans=%h src_id=%h dest_id=%h",
        pkt_dir.name, np ? "NP" : "SD", pkt_type.name,
        decode_error ? "ERROR!" :
        (sdb & edb) ? "S+EDB" : sdb ? "SDB" : edb ? "EDB" :
        pkt_type == MSG_PKT ? (
          ctg == MSG_CTG_LMSG ? (
            idx == LMSG_IDX_FCREQ ? "FCREQ" :
            idx == LMSG_IDX_FCRDY ? "FCRDY" :
            idx == LMSG_IDX_STAT  ? "STAT"  : ""
          ) :
          ctg == MSG_CTG_AMSG ? (
            idx == AMSG_IDX_EBSY  ? "EBSY! " : ""
          ) : ""
        ) :
        pkt_type == CCMD_PKT ?
          $sformatf("%s io=%3h plen=%2b", rw ? "wr" : "rd", ioadr, plen) : "",
        act_len, trans_id, src_id, dest_id );
    `endif // !USE_LOGGERS

      if (this.power_cycle)
        $swrite(to_string, "%s [power cycle req]", to_string);
      if (this.crc_act_exists)
        $swrite(to_string, "%s  CRC act = %h", to_string, this.crc_act);
      if (this.crc_exp_exists)
        $swrite(to_string, "%s  CRC exp = %h", to_string, this.crc_exp);

      if (act_len > 0) begin
        $swrite(to_string, "%s   %s", to_string, "\traw bytes:");
      `ifdef PRINT_ALL_RAW_BYTES
        for (int i = 0; i < act_len; ++i)
          $swrite(to_string, "%s %h", to_string, data[i][7:0]);
      `else // PRINT_ALL_RAW_BYTES
        for (int i = 0; i < 20 && i < act_len; ++i)
          $swrite(to_string, "%s %h", to_string, data[i][7:0]);
        if (act_len > 20)
          $swrite(to_string, "%s ...", to_string);
      `endif // ! PRINT_ALL_RAW_BYTES
      end
      else
        $swrite(to_string, "%s   %s", to_string, "[no data]");

      if (!decode_error) begin
        if (!np && (pkt_type == CCMD_PKT || pkt_type == DCMD_PKT))
          $swrite(to_string, "%s %sCMD%d arg=%h",
            to_string, app ? "A" : " ", cmd_index, sd_arg);

        if (pkt_type == MSG_PKT && ctg == MSG_CTG_LMSG)
          $swrite(to_string, "%s %s", to_string,
            this.urec_err ? "unrecoverable error" :
            this.rec_err  ? "recoverable error" : "");
        if (pkt_type == MSG_PKT && ctg == MSG_CTG_AMSG && idx == AMSG_IDX_EBSY)
          $swrite(to_string, "%s %s", to_string,
            this.urec_err ? "memory error" : "");
        else if (pkt_type == DCMD_PKT)
          if (this.lm)
            $swrite(to_string, "%s tlen=%d", to_string, tlen);
          else
            $swrite(to_string, "%s %s", to_string, "(no tlen)");
      end
    `ifdef META_INFO_DISPLAY
      $swrite(to_string,
        "%s go2dorm=%b switch2didl=%b switch2lidl=%b power_cycle=%b repeat_msg=%b go4reset=%b",
        to_string,
        go2dormant, switch2didl, switch2lidl, power_cycle, repeat_msg, go4reset);
    `endif // META_INFO_DISPLAY
      if (this.odd_data_pkt != null)
        $swrite(to_string, "%s   additional odd data pkt:\n%s",
          to_string, this.odd_data_pkt.to_string);
    endfunction : to_string

    /** Scrambles/descrambles data included in the data field (except PAD). */
    function void scramble;
      if (this.data.size > 0 && this.crc_act_exists) begin
        ensure_scramble_pattern_length(this.data.size + 2);
        for (int i = 0; i < this.data.size; ++i)
          if (this.data[i][8] == 1'b0) // if it's not PAD
            this.data[i][7:0] ^= scramble_pattern[i];
        crc_act[15:8] ^= scramble_pattern[this.data.size];
        crc_act[7:0]  ^= scramble_pattern[this.data.size + 1];        
      end
    endfunction : scramble

    /** Compares crc_act with crc_exp. Invokes calc_crc first. */
    function void check_crc;
      this.calc_crc;
      this.crc_error = (this.crc_act != this.crc_exp);
      if (this.odd_data_pkt != null) begin
        this.odd_data_pkt.check_crc;
        this.crc_error |= this.odd_data_pkt.crc_error;
      end
    endfunction : check_crc

    /** Invokes calc_crc, then copies calculated CRC from crc_exp to crc_act. */
    function void add_crc;
      this.calc_crc;
      this.crc_act = this.crc_exp;
      this.crc_act_exists = `TRUE;
      if (this.odd_data_pkt != null)
        this.odd_data_pkt.add_crc;
    endfunction : add_crc

    /** XORs act_crc and mask (introduces intentional errors to CRC). */
    function void spoil_crc(bit [15:0] mask);
      if (!this.crc_act_exists) this.calc_crc;
      this.crc_act = this.crc_act ^ mask;
    endfunction : spoil_crc

    /** Calculates CRC for data field and saves it into crc_exp. */
    function void calc_crc;
      automatic bit [16:0] crc_temp = 17'h00000;
      automatic bit [7:0]  data_temp;
      automatic int data_len = this.data.size; 

      if (this.data.size == 0) begin
        assert (0) else $error("data not present. CRC not calculated.");
        return;
      end

      for (int i = 0; i < data_len; ++i) begin
        data_temp = data[i][7:0];
        repeat (8) begin
          crc_temp <<= 1;        
          if (data_temp[7] ^ crc_temp[16])
            crc_temp ^= crc_gen_polynom;
          data_temp <<= 1;
        end
      end

      crc_exp = crc_temp[15:0];
      crc_exp_exists = `TRUE;
    endfunction : calc_crc

    function void put_send_data(ref bit [8:0] send_bytes[$],
                                input bit is_scrambled = `TRUE);
      int i = data.size - 1;
      if (is_scrambled) this.scramble;

      send_bytes = {};
      send_bytes.push_front(this.crc_act[7:0]);
      send_bytes.push_front(this.crc_act[15:8]);
      while (i >= 0)
        send_bytes.push_front(data[i--]);
    endfunction : put_send_data

    // *** packet decoding ***

    function void decode_pkt;
      decode_pkt_header;
      case (pkt_type)
        CCMD_PKT:
          decode_ccmd_pkt;
        DCMD_PKT:
          decode_dcmd_pkt;
        RES_PKT:
          decode_res_pkt;
        DATA_PKT:
          decode_data_pkt;
        MSG_PKT:
          decode_msg_pkt;
        default:
          assert (0) else $error("unknown packet type");
      endcase

      if (this.pkt_type != UNKN_PKT)
        this.payload_length = this.data.size - this.payload_index - this.pads;
    endfunction : decode_pkt

    function void decode_pkt_header;
      this.np = data[0][7];
      if (data.size >= 2) begin
        decode_pkt_type;
        if (this.pkt_type != UNKN_PKT) begin
          this.trans_id      = data[1][2:0];
          this.dest_id       = data[0][3:0];
          this.src_id        = data[1][7:4];
          this.payload_index = 2;        
        end
      end
    endfunction : decode_pkt_header

    function void decode_pkt_type;
      case (data[0][6:4])
        PKT_TYPE_CCMD:   pkt_type = CCMD_PKT;
        PKT_TYPE_DCMD:   pkt_type = DCMD_PKT;
        PKT_TYPE_RES:    pkt_type = RES_PKT;
        PKT_TYPE_DATA:   pkt_type = DATA_PKT;
        PKT_TYPE_MSG:    pkt_type = MSG_PKT;      
        default:         pkt_type = UNKN_PKT;
      endcase
    endfunction : decode_pkt_type

    function void decode_ccmd_pkt;
      if (data.size >= 4 && np) begin
        rw             = data[2][7];
        plen           = data[2][5:4];
        ioadr[11:8]    = data[2][3:0];
        ioadr[7:0]     = data[3][7:0];
        payload_index  = 4;
      end
      else if (data.size >= 8 && !np) begin
        decode_sd_args;
        payload_index = 8;
      end
      else
        decode_error = `TRUE;
    endfunction : decode_ccmd_pkt

    function void decode_dcmd_pkt;
      if (data.size >= 8) begin
        dm          = data[2][6];
        lm          = data[2][5];
        tlum        = data[2][4];
        dam         = data[2][3];

        if (np) begin
          rw     =  data[2][7];
          dadr   = {data[4][7:0], data[5][7:0], data[6][7:0],  data[7][7:0]};
        end
        else
          decode_sd_args;

        if (data.size >= 12)
          tlen = {data[8][7:0], data[9][7:0], data[10][7:0], data[11][7:0]};
        this.payload_index = (data.size >= 12) ? 12 : 8;
      end
      else
        decode_error = `TRUE;
    endfunction : decode_dcmd_pkt

    function void decode_sd_args;
      app        =  data[3][6];
      cmd_index  =  data[3][5:0];
      sd_arg     = {data[4][7:0], data[5][7:0], data[6][7:0],  data[7][7:0]};
    endfunction : decode_sd_args

    function void decode_res_pkt;
      nak = data[2][7];
      if (nak)
        ecode = data[2][6:4];
      else
        cmd_echo = {data[3][6:0], data[4][7:0]};
    endfunction : decode_res_pkt

    function void decode_data_pkt;
      if (data.size > 2) begin
        payload_index = 2;
        if (this.odd_data_pkt != null)
          combine_from_2lanes;
        for (int i = data.size - 1; data[i][8] == 1'b1; ++pads, --i);
      end
    endfunction : decode_data_pkt

    function void decode_msg_pkt;
      if (data.size >= 4) begin
        ctg = data[2][7:5];
        idx = data[2][3:0];
        urec_err = data[3][7];
        if (ctg == MSG_CTG_LMSG && idx == LMSG_IDX_STAT)
          rec_err = data[3][0];
        this.payload_index = 4;
      end
      else
        decode_error = `TRUE;
    endfunction : decode_msg_pkt

    // -------------------------------------------------------------------- //

    // *** packet encoding ***

    function void encode_pkt;
      pkt_dir = OUTGOING;
      case (pkt_type)
        CCMD_PKT:
          encode_ccmd_pkt;
        DCMD_PKT:
          encode_dcmd_pkt;
        RES_PKT:
          encode_res_pkt;
        DATA_PKT,
        DATA_PKT_2L:
          encode_data_pkt;
        MSG_PKT:
          encode_msg_pkt;
        META_PKT:
          ;  // do nothing
        default:
          assert (0) else $error("unknown packet type");
      endcase
    endfunction : encode_pkt

    /** Ensures additional space in the data array: lb and le are the numbers
        of bytes inserted at the beginning and at the end of the array,
        respectively. Bytes inserted at the beginning have value of 9'h000;
        bytes inserted at the end of the array have value of PAD according
        to the UHS II standard. */
    function void ensure_data_array_space(int lb, le = 0);
      bit [8:0] temp[];
      this.payload_index  = lb;
      if (this.data.size == 0) begin
        this.payload_length = 0;
        this.data = new [lb + le];
      end
      else begin
        this.payload_length = this.data.size;
        temp = new [lb + this.data.size + le];
        for (int i = this.data.size - 1; i >= 0; --i)
          temp[i + lb] = this.data[i];
        for (int i = lb - 1; i >= 0; --i)
          temp[i] = 9'h000;
        for (int i = data.size + lb; i < temp.size; ++i)
          temp[i] = {LSS_PAD_M, LSS_PAD};
        this.data = temp;
      end
    endfunction : ensure_data_array_space

    function void encode_pkt_header;
      data[0][7]   = np;
      data[0][3:0] = dest_id;
      data[1][2:0] = trans_id;
      data[1][7:4] = src_id;
      if (this.change_type)
        randcase
          (1 * (data[0][6:4] != PKT_TYPE_CCMD)): data[0][6:4] = PKT_TYPE_CCMD;
          (1 * (data[0][6:4] != PKT_TYPE_RES)):  data[0][6:4] = PKT_TYPE_RES;
          (1 * (data[0][6:4] != PKT_TYPE_DATA)): data[0][6:4] = PKT_TYPE_DATA;
          (1 * (data[0][6:4] != PKT_TYPE_MSG)):  data[0][6:4] = PKT_TYPE_MSG;
        endcase
    endfunction : encode_pkt_header

    function void encode_ccmd_pkt;
      ensure_data_array_space(np ? 4 : 8);
      data[0][6:4] = PKT_TYPE_CCMD;
      encode_pkt_header;
      if (np) begin
        data[2][7]   = rw;
        data[2][5:4] = plen;
        data[2][3:0] = ioadr[11:8];
        data[3][7:0] = ioadr[7:0];
      end
      else
        encode_sd_args;
    endfunction : encode_ccmd_pkt

    function void encode_dcmd_pkt;
      ensure_data_array_space(lm ? 12 : 8);
      data[0][6:4] = PKT_TYPE_DCMD;
      encode_pkt_header;

      data[2][6] = dm;
      data[2][5] = lm;
      data[2][4] = tlum;
      data[2][3] = dam;
      if (np) begin
        data[2][7] = rw;
        data[4][7:0] = dadr[31:24];
        data[5][7:0] = dadr[23:16];
        data[6][7:0] = dadr[15:8];
        data[7][7:0] = dadr[7:0];
      end
      else
        encode_sd_args;

      if (lm) begin
        data[8][7:0]  = tlen[31:24];
        data[9][7:0]  = tlen[23:16];
        data[10][7:0] = tlen[15:8];
        data[11][7:0] = tlen[7:0];
      end
    endfunction : encode_dcmd_pkt

    function void encode_sd_args;
      data[3][6]    = app;
      data[3][5:0]  = cmd_index;
      data[4]       = sd_arg[31:24];
      data[5]       = sd_arg[23:16];
      data[6]       = sd_arg[15:8];
      data[7]       = sd_arg[7:0];  
    endfunction : encode_sd_args

    function void encode_res_pkt;
      ensure_data_array_space(4);
      data[0][6:4] = PKT_TYPE_RES;
      encode_pkt_header;
      data[2][7] = nak;
      if (nak) 
        data[2][6:4] = ecode;
      else begin
        data[2][6:0] = cmd_echo[14:8];
        data[3][7:0] = cmd_echo[7:0];
      end
    endfunction : encode_res_pkt

    function void encode_data_pkt;
      data[0][6:4] = PKT_TYPE_DATA;
      encode_pkt_header;
  
      if (this.pkt_type == DATA_PKT_2L)
        split_into_2lanes;
    endfunction : encode_data_pkt

    function void encode_msg_pkt;
      ensure_data_array_space(4);
      data[0][6:4] = PKT_TYPE_MSG;
      encode_pkt_header;
      // this is always native protocol!?
      data[2][7:5] = ctg;
      data[2][3:0] = idx;
      data[3][7:0] = {urec_err, 6'd0, idx == LMSG_IDX_STAT ? rec_err : 1'b0};
    endfunction : encode_msg_pkt

    // ==================================================================== //

    function void combine_from_2lanes;
      bit [8:0] data_temp[] = new [this.data.size +
                                   this.odd_data_pkt.data.size - 2],
                data_even[] = this.data,
                data_odd[]  = this.odd_data_pkt.data;
      int i = 2, j = 2;
      if (this.pkt_type == DATA_PKT) begin
        this.pkt_type = DATA_PKT_2L;
        this.odd_data_pkt.pkt_type = DATA_PKT_2L;
      end

      if (data_even.size >= 2) begin
        // header is common
        data_temp[0] = data_even[0];
        data_temp[1] = data_even[1];
      end
      for (`EMPTY_STMNT; j < data_even.size && j < data_odd.size; i+=2, ++j) begin
        data_temp[i]   = data_even[j];
        data_temp[i+1] = data_odd[j];
      end
      for (`EMPTY_STMNT; i < data_temp.size && j < data_even.size; ++i, ++j)
        data_temp[i] = data_even[j];
      for (`EMPTY_STMNT; i < data_temp.size && j < data_odd.size; ++i, ++j)
        data_temp[i] = data_odd[j];

      this.data = data_temp;
    endfunction : combine_from_2lanes

    /** Splits pkt data into odd and even part to be sent on different lanes.
        Used for preparation of a data pkt in 2L-HD. */
    function void split_into_2lanes;
      int new_length = (this.data.size - 2) / 2 + 2;
      bit [8:0] data_temp[] = this.data,
                data_even[] = new[new_length],
                data_odd[]  = new[new_length];
      this.odd_data_pkt = new this;

      if (data_temp.size >= 2) begin
        // header is common
        data_even[0] = data_temp[0];
        data_even[1] = data_temp[1];
        data_odd[0]  = data_temp[0];
        data_odd[1]  = data_temp[1];
      end

      for (int i = 2, j = 0; i < data_temp.size-1; i+=2, ++j) begin
        data_even[2+j] = data_temp[i];
        data_odd[2+j]  = data_temp[i+1];
      end

      this.data                   = data_even;
      this.odd_data_pkt.data      = data_odd;
      this.odd_data_pkt.pkt_dir   = OUTGOING;
    endfunction : split_into_2lanes

    function bit compare_to(input uhsii_pkt pkt);
      if (this == null)
        return `FALSE;
      if (pkt == null)
        return `FALSE;
      if (this.pkt_type != pkt.pkt_type)
        return `FALSE;
      if (this.np != pkt.np)
        return `FALSE;
      if (this.src_id != pkt.src_id)
        return `FALSE;
      if (this.dest_id != pkt.dest_id)
        return `FALSE;
      if (this.trans_id != pkt.trans_id)
        return `FALSE;
    
      case (this.pkt_type)
        MSG_PKT: begin
          if (this.ctg != pkt.ctg)
            return `FALSE;
          if (this.idx != pkt.idx)
            return `FALSE;
          if (this.urec_err != pkt.urec_err)
            return `FALSE;
          if (this.rec_err != pkt.rec_err)
            return `FALSE;
          return `TRUE;
        end

        default : return `FALSE;
      endcase
    endfunction : compare_to

    function void add_payload(int unsigned req_pld[]);
      this.data = new[req_pld.size * 4];
      for (int i = 0; i < this.data.size; ++i)
        this.data[i] = ((req_pld[i/4] >> ((3 - i%4) * 8)) & 32'h000000FF);
    endfunction : add_payload

    function void make_brc_pkt(input uhsii_pkt orig_pkt);
      this.np         = orig_pkt.np;
      this.src_id     = orig_pkt.src_id;
      this.dest_id    = orig_pkt.dest_id;
      this.trans_id   = orig_pkt.trans_id;
      this.pkt_type   = orig_pkt.pkt_type;

      // orig_pkt should be always CCMD
      this.rw         = orig_pkt.rw;
      this.plen       = orig_pkt.plen;
      this.ioadr      = orig_pkt.ioadr;    
    endfunction : make_brc_pkt

    function void make_res_pkt(input uhsii_pkt cmd_pkt,
                               input bit nak,
                               input bit [2:0] ecode);
      this.np         = cmd_pkt.np;
      this.src_id     = cmd_pkt.dest_id;
      this.dest_id    = cmd_pkt.src_id;
      this.trans_id   = cmd_pkt.trans_id;
      this.pkt_type   = RES_PKT;
      this.nak        = nak;

      if (nak)
        this.ecode    = ecode;
      else if (np)
        case (cmd_pkt.pkt_type)
          CCMD_PKT: this.cmd_echo = {1'b0, cmd_pkt.plen, cmd_pkt.ioadr};
          DCMD_PKT: this.cmd_echo = {cmd_pkt.dm,  cmd_pkt.lm, cmd_pkt.tlum,
                                     cmd_pkt.dam, 11'h000};
          default:  assert (0) else $error("expecting CCMD_PKT or DCMD_PKT");
        endcase
      else
        this.cmd_echo =
          {cmd_pkt.pkt_type == DCMD_PKT ?
            {cmd_pkt.dm,  cmd_pkt.lm, cmd_pkt.tlum, cmd_pkt.dam} :
            4'b0000,
          4'b0000,
          cmd_pkt.app,
          cmd_pkt.cmd_index};
    endfunction : make_res_pkt

    function void make_fc_pkt(input uhsii_pkt   last_pkt,
                              input bit [3:0]   idx,
                              input bit         ure = `FALSE,
                              input bit         re  = `FALSE);
      this.np         = `TRUE;
      this.pkt_type   = MSG_PKT;

      this.dest_id    = last_pkt.src_id;
      this.src_id     = last_pkt.dest_id;
      this.trans_id   = last_pkt.trans_id;

      this.ctg        = MSG_CTG_LMSG;
      this.idx        = idx;
      this.urec_err   = ure;  // unrecoverable error
      this.rec_err    = re;   // recoverable error
    endfunction

    function void make_ebsy_pkt(input uhsii_pkt   last_pkt,
                                input bit         me = `FALSE);
      make_fc_pkt(last_pkt, AMSG_IDX_EBSY, me);
      this.ctg = MSG_CTG_AMSG;
    endfunction : make_ebsy_pkt

    function void make_data_pkt(input bit            np,
                                input uhsii_pkt      fcrdy_pkt,
                                input byte unsigned  data[],
                                input int            length,
                                input bit            _2lhd);
      this.pads = (_2lhd ?
          ((length % 4 == 0) ? 0 : (4 - length % 4)) :
           (length % 2) ); // ... and for a few PADs if needed

      this.np              = np;
      this.src_id          = fcrdy_pkt.dest_id;
      this.dest_id         = fcrdy_pkt.src_id;
      this.trans_id        = fcrdy_pkt.trans_id;
      this.pkt_type        = _2lhd ? DATA_PKT_2L : DATA_PKT;

      this.payload_index   = 2;
      this.payload_length  = length;
      this.data            = new [2 + length + this.pads];

      for (int i = 0, j = 2; i < length && i < data.size; ++i, ++j)
        this.data[j] = {1'b0, data[i]};
      for (int k = 0, j = this.data.size-1; k < this.pads; ++k, --j)
        this.data[j] = {LSS_PAD_M, LSS_PAD};
    endfunction

    function uhsii_pkt copy;
      if (this == null)
        copy = null;
      else begin
        copy = new this;
        copy.data = new [this.data.size];
        foreach (copy.data[i])
          copy.data[i] = this.data[i];
      end
    endfunction : copy

    // -------------------------------------------------------------------- //

    // to be used in the packet checker:

    function void put_into_struct(ref uhsii_pkt_struct pkt);
      pkt.pkt_dir                   =  this.pkt_dir;
      pkt.sdb                       =  this.sdb;
      pkt.edb                       =  this.edb;
      pkt.decode_error              =  this.decode_error;
      pkt.crc_error                 =  this.crc_error;
      pkt.pkt_type                  =  this.pkt_type;
      pkt.np                        =  this.np;
      pkt.trans_id                  =  this.trans_id;
      pkt.broadcast                 = (this.src_id == this.dest_id);
      pkt.rw                        =  this.rw;
      pkt.plen                      =  this.plen;
      pkt.ioadr                     =  this.ioadr;
      pkt.dm                        =  this.dm;
      pkt.lm                        =  this.lm;
      pkt.tlum                      =  this.tlum;
      pkt.dam                       =  this.dam;
      pkt.dadr                      =  this.dadr;
      pkt.tlen                      =  this.tlen;
      pkt.nak                       =  this.nak;
      pkt.ecode                     =  this.ecode;
      pkt.payload_index             =  this.payload_index;
      pkt.payload_length            =  this.payload_length;
      pkt.pads                      =  this.pads;
      pkt.ctg                       =  this.ctg;
      pkt.idx                       =  this.idx;
      pkt.cmd_echo                  =  this.cmd_echo;
      pkt.urec_err                  =  this.urec_err;
      pkt.rec_err                   =  this.rec_err;
      pkt.app                       =  this.app;
      pkt.cmd_index                 =  this.cmd_index;
      pkt.sd_arg                    =  this.sd_arg;
      pkt.first_pld_dword           =  32'h00000000;

      if (pkt.payload_length >= 4) begin
        pkt.first_pld_dword[31:24]  = this.data[4];
        pkt.first_pld_dword[23:16]  = this.data[5];
        pkt.first_pld_dword[16:8]   = this.data[6];
        pkt.first_pld_dword[7:0]    = this.data[7];
      end

      pkt.init_2lhd_in              =  this.init_2lhd_in;
      pkt.init_2lhd_out             =  this.init_2lhd_out;
    endfunction
  
    // for debugging only:

    static function string struct_to_string(const ref uhsii_pkt_struct pkt);
      string returned = " ";

      $swrite(returned, "%s pkt_dir=%s", returned, pkt.pkt_dir.name);
      $swrite(returned, "%s pkt_type=%s", returned, pkt.pkt_type.name);
      $swrite(returned, "%s np=%b", returned, pkt.np);
      $swrite(returned, "%s bc=%b", returned, pkt.broadcast);
      $swrite(returned, "%s trans_id=%b", returned, pkt.trans_id);

      $swrite(returned, "%s sdb=%b", returned, pkt.sdb);
      $swrite(returned, "%s edb=%b", returned, pkt.edb);
      $swrite(returned, "%s dec_err=%b", returned, pkt.decode_error);
      $swrite(returned, "%s crc_err=%b", returned, pkt.crc_error);

      $swrite(returned, "%s rw=%b", returned, pkt.rw);
      $swrite(returned, "%s plen=%b", returned, pkt.plen);
      $swrite(returned, "%s ioadr=%h", returned, pkt.ioadr);

      $swrite(returned, "%s dm=%b", returned, pkt.dm);
      $swrite(returned, "%s lm=%b", returned, pkt.lm);
      $swrite(returned, "%s tlum=%b", returned, pkt.tlum);
      $swrite(returned, "%s dam=%b", returned, pkt.dam);

      $swrite(returned, "%s dadr=%h", returned, pkt.dadr);
      $swrite(returned, "%s tlen=%h", returned, pkt.tlen);

      $swrite(returned, "%s nak=%b", returned, pkt.nak);
      $swrite(returned, "%s ecode=%b", returned, pkt.ecode);

      $swrite(returned, "%s cmd_echo=%h", returned, pkt.cmd_echo);

      $swrite(returned, "%s pld_idx=%d", returned, pkt.payload_index);
      $swrite(returned, "%s pld_len=%d", returned, pkt.payload_length);
      $swrite(returned, "%s pads=%d", returned, pkt.pads);
      $swrite(returned, "%s first_pld_dword=%h", returned, pkt.first_pld_dword);

      $swrite(returned, "%s ctg=%b", returned, pkt.ctg);
      $swrite(returned, "%s idx=%b", returned, pkt.idx);
      $swrite(returned, "%s rec_err=%b", returned, pkt.rec_err);
      $swrite(returned, "%s urec_err=%b", returned, pkt.urec_err);

      $swrite(returned, "%s init2lhd_IN=%b", returned, pkt.init_2lhd_in);
      $swrite(returned, "%s init2lhd_OUT=%b", returned, pkt.init_2lhd_out);

      $swrite(returned, "%s app=%b", returned, pkt.app);
      $swrite(returned, "%s SDcmd=%d", returned, pkt.cmd_index);
      $swrite(returned, "%s SDarg=%h", returned, pkt.sd_arg);
    
      return returned;
    endfunction : struct_to_string

  endclass : uhsii_pkt
endpackage : uhsii_pkt_pkg

