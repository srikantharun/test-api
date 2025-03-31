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
//   legacy SD card & UHS-II SD-TRAN model
//
//   File contents   : package sd_card_pkg
//                     class   sd_card_cl
//                     class   legacy_config_cl
//                     class   sd_transf_cl
//------------------------------------------------------------------------------

`timescale 1 ns / 100 ps

//`define DATA_INTEGRITY_CHECK_DEBUG_WRITE
//`define DATA_INTEGRITY_CHECK_DEBUG_READ

`include "sv_macros.svh"
`include "card_logging.svh"
package sd_card_pkg;
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import card_echo_event_pkg::*;
  import sd_mem_pkg::*;
  import sd_tok_pkg::*;
  import datagen_pkg::*;

`include "sd_card_params.svh"
`ifdef CARD_COVER
`include "legacy_card_cover.sv"
`endif // CARD_COVER

  typedef bit [7:0] byte_array[];

  typedef enum {
    SDSC,         // SD standard capacity card
    SDHC,         // SD high capacity card
    SDXC,         // SD extra capacity card
    EMMC_BYTE,    // eMMC card with byte access
    EMMC_SECTOR   // eMMC card with sector access
  } capacity_e;

  typedef enum {
    READ_OPER,
    WRITE_OPER,
    ERASE_OPER
  } oper_e;

  // ----- CRC CALCULATION -----

  const static bit [16:0] crc7_gen_polynom  = 8'b10001001;
  const static bit [16:0] crc16_gen_polynom = 17'b10001000000100001;

  function static bit [6:0] calc_crc7(input bit[127:0] bits, input int len);
    automatic bit [7:0] crc_temp = 8'b00000000;
    for (int i = len-1; i >= 0; --i) begin
      crc_temp <<= 1;
      if (bits[i] ^ crc_temp[7])
        crc_temp ^= crc7_gen_polynom;
    end
    return crc_temp[6:0];
  endfunction : calc_crc7

  function static bit get_ccs(capacity_e card_capacity);
    return (card_capacity inside {SDHC, SDXC, EMMC_SECTOR});
  endfunction : get_ccs

  // ----- SD CARD CONFIG CLASS -----

  class legacy_config_cl;
    const capacity_e      card_cap;
    const bit [23:0]      voltage_window;
    const bit             no_dat_delays;
    const bit             no_cmd_delays;

    function new(input capacity_e  card_cap,
                 input bit [23:0]  voltage_window,
                 input bit         no_dat_delays  = `FALSE,
                 input bit         no_cmd_delays  = `FALSE);
      this.card_cap        =  card_cap;
      this.voltage_window  =  voltage_window;
      this.no_dat_delays   =  no_dat_delays;
      this.no_cmd_delays   =  no_cmd_delays;
    endfunction : new

    static const bit [23:0] default_ocr_sd_leg = 24'b111111111000000000000000;
    static const bit [23:0] default_ocr_emmc   = 24'b111111111000000010000000;
    static const bit [23:0] default_ocr_sdio   = 24'b111111111111111110000000;

    static function bit [23:0] random_ocr_sd_leg;
      do begin
        random_ocr_sd_leg =  $urandom_range(1 << 24);
        random_ocr_sd_leg &= default_ocr_sd_leg;
      end
      while (random_ocr_sd_leg[23:8] == 0);
    endfunction : random_ocr_sd_leg

    static function bit [23:0] random_ocr_emmc;
      do begin
        random_ocr_emmc =  $urandom_range(1 << 24);
        random_ocr_emmc &= default_ocr_emmc;
      end
      while (random_ocr_emmc[23:8] == 0);
    endfunction : random_ocr_emmc

    static function bit [23:0] random_ocr_sdio;
      do begin
        random_ocr_sdio =  $urandom_range(1 << 24);
        random_ocr_sdio &= default_ocr_emmc;
      end
      while (random_ocr_sdio[23:8] == 0);
    endfunction : random_ocr_sdio
  endclass : legacy_config_cl

  // ----- SD DATA TRANSFER CLASS ----- //

  class sd_transf_cl;
    protected int unsigned          start_addr;      // set with CMDs: 17, 18, 24, 25, 32, 53
    protected int unsigned          curr_addr;       // incremented during transfer
    protected int unsigned          end_addr;        // set with 33 or derived from CMD23
    protected int unsigned          max_addr;        // lowest addr unsupported by card

    protected int unsigned          blknum;          // set with CMD23, 0 = unlimited
    protected int unsigned          blklen;          // set with CMD16,

    local capacity_e                card_cap;
    local sd_mem_cl                 memory;
    local mem_blk                   blk_temp;
    local mailbox
              #(card_echo_event_cl) event_echo;
    protected datagen_cl            datagen;
              bit                   datagen_mode;
              time                  started;

    protected oper_e                oper;            // operation type

    bit                             allow_misalign;  // misalign allowed
    bit                             is_misaligned;   // boundary crossed

    bit                             out_of_range;    // end of user data reached
    bit                             erase_start,     // CMD32 has been received
                                    erase_end;       // CMD33 has been received

    local bit                       training;        // proprietary "training" mode

    function new(input int unsigned     addr,
                 input capacity_e       card_cap,
                 input sd_mem_cl        memory,
                 input int unsigned     block_length,
                 input int unsigned     block_count,
                 input oper_e           oper,
                 input bit              misalign,
                 input bit              uhsii_based,
                 input datagen_cl       datagen = null);

      this.start_addr     = addr;
      this.curr_addr      = addr;
      this.card_cap       = card_cap;
      this.memory         = memory;
      this.blk_temp       = null;

      // it's not consistent with spec, but we need to test different block lengths in UHSII SD-Tran
      this.blklen         = (get_ccs(this.card_cap) && !uhsii_based) ? 512 : block_length;
      this.blknum         = block_count;
      this.end_addr       = start_addr + blknum * (get_ccs(this.card_cap) ? 1 : blklen);
      this.max_addr       = 0;
      this.datagen        =  datagen;
      this.datagen_mode   = (datagen != null && datagen.is_active);
      this.started        = $time;

      this.oper           = oper;
      this.allow_misalign = misalign;
      this.is_misaligned  = `FALSE;
      this.erase_start    = `FALSE;
      this.erase_end      = `FALSE;

      this.training       = `FALSE;
    endfunction : new

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    // ----- ----- -----

    virtual function string to_string;
      return $sformatf(
          "%s data transf start_addr=%h curr_addr=%h end_addr=%h blklen=%0d blknum=%0d",
              this.oper.name, this.start_addr, this.curr_addr, this.end_addr,
              this.blklen, this.blknum);
    endfunction : to_string

    // ----- ----- -----

    virtual function bit has_next_blk;
      return (this.blknum == 0 ||
              this.end_addr < this.start_addr ||
              this.end_addr > this.curr_addr);
    endfunction : has_next_blk

    local function int unsigned get_start_blk_addr;
      return get_ccs(this.card_cap) ? start_addr : (start_addr >> 9);
    endfunction : get_start_blk_addr

    local function int unsigned get_curr_blk_addr;
      return get_ccs(this.card_cap) ? curr_addr : (curr_addr >> 9);
    endfunction : get_curr_blk_addr

    local function int unsigned get_end_blk_addr;
      return get_ccs(this.card_cap) ? end_addr : (end_addr >> 9);
    endfunction : get_end_blk_addr

    function void set_end_blk_addr(input int unsigned addr);
      end_addr = addr;
    endfunction : set_end_blk_addr

    local function void prepare_blk_temp_for_write(const ref bit [7:0] data[]);
      bit [7:0] old_data[];
      if (blk_temp.data.size == 512);
      else if (blk_temp.data.size == 0)
        blk_temp.data = new [512];
      else if (blk_temp.data.size < (curr_addr[8:0] + data.size)) begin
        old_data = blk_temp.data;
        blk_temp.data = new [512];
        for (int j = 0; j < old_data.size && j < curr_addr[8:0]; ++j)
          blk_temp.data[j] = old_data[j];
      end
    endfunction : prepare_blk_temp_for_write

    // ----- ----- -----

    local function void incr_mem_addr(bit rw, const ref bit [7:0] data[]);
      if ((curr_addr[8:0] == 9'h1FF) && rw) // puts curr blk
        memory.put_mem_blk(blk_temp, get_curr_blk_addr);
      if (++curr_addr == max_addr)
        out_of_range = `TRUE;
      else if (curr_addr[8:0] == 9'h000) begin
        if (allow_misalign) begin
          blk_temp = memory.get_mem_blk(get_curr_blk_addr()); // gets next blk
          if (rw)
            prepare_blk_temp_for_write(data);
        end
        else
          is_misaligned = `TRUE;
      end
    endfunction : incr_mem_addr

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    virtual function byte_array read_curr_blk();
      int i = 0;
      bit [7:0] data[];
      data_echo_event_cl echo_tmp;

      if (! this.datagen_mode)
        blk_temp = memory.get_mem_blk(get_curr_blk_addr());

      `DISPLAY_LOGGER_MSG($sformatf("data read starting from addr=%h", curr_addr))

      if (! get_ccs(this.card_cap)) begin
        data = new [blklen];
        while (i < data.size && !out_of_range && !is_misaligned) begin
          if (datagen_mode)
            data[i++] = datagen.get8;
          else
            data[i++] = blk_temp.data[curr_addr[8:0]];
          incr_mem_addr(`FALSE, data);
        end
        if (i == data.size)
          is_misaligned = `FALSE;
      end
      else begin // SDHC / SDXC -> no blk boundary crossing
        if (datagen_mode) begin
          data = new [blklen];
          for (int i = 0; i < data.size; ++i)
            data[i] = datagen.get8;
        end
        else if (blk_temp.data.size == blklen)
          data = blk_temp.data;
        else begin
          data = new[blklen];
          for (int i = 0; i < blk_temp.data.size && i < data.size; ++i)
            data[i] = blk_temp.data[i];
        end
        if (++curr_addr == max_addr && has_next_blk)
          out_of_range = `TRUE;
      end

      if (datagen != null && !datagen_mode)
        foreach(data[i])
          datagen.calc_user_crc(data[i]);

      return data;
    endfunction : read_curr_blk

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    virtual task write_curr_blk(const ref bit [7:0] data[]);
      int i = 0;

      if (data.size == blklen)
        `DISPLAY_LOGGER_MSG($sformatf(
            "%0d byte(s) to be written starting from addr=%h", data.size, curr_addr))
      else
        `DISPLAY_LOGGER_WARNING($sformatf(
          "incorrect length of write data block: is %d, should be %d", data.size, blklen))

      if (this.datagen_mode) begin
        if (! get_ccs(this.card_cap))
          while (i++ < data.size && !out_of_range && !is_misaligned)
            incr_mem_addr(`TRUE, data);
        else if (++curr_addr == max_addr && has_next_blk)
          out_of_range = `TRUE;
        return;
      end

      blk_temp = memory.get_mem_blk(get_curr_blk_addr());
      prepare_blk_temp_for_write(data);
      if (! get_ccs(this.card_cap)) begin
        while (i < data.size && !out_of_range && !is_misaligned) begin
          blk_temp.data[curr_addr[8:0]] = data[i++];
          incr_mem_addr(`TRUE, data);
        end
        if (i == data.size)
          is_misaligned = `FALSE;
        if (curr_addr[8:0] > 0)
          memory.put_mem_blk(blk_temp, get_curr_blk_addr);
      end
      else begin // SDHC / SDXC -> no blk boundary crossing
        i = data.size - 1;
        while (data[i] == 0 && i >= 0) --i;
        if (i == -1)
          memory.remove_mem_blk(get_curr_blk_addr);
          // remove blk if it contains zeros only
        else begin
          blk_temp.data = new [++i];
          while (--i >= 0)
            blk_temp.data[i] = data[i];
          memory.put_mem_blk(blk_temp, get_curr_blk_addr);
        end
        if (++curr_addr == max_addr && has_next_blk)
          out_of_range = `TRUE;
      end
    endtask : write_curr_blk

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    function void perform_erase;
      for (int unsigned i = this.get_start_blk_addr;
                        i < this.get_end_blk_addr + 1; ++i)
                        // ^^ ......... inclusive .........^^
        memory.remove_mem_blk(i);
        `DISPLAY_LOGGER_MSG($sformatf("%d block(s) erased",
            (1 + this.get_curr_blk_addr
               - this.get_start_blk_addr)))
    endfunction

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    virtual function bit check_rsp_aligned;
      return `FALSE;
    endfunction : check_rsp_aligned

    // ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- ----- -----

    function int unsigned get_blklen;
      return this.blklen;
    endfunction : get_blklen

    function void set_blklen(input int unsigned blklen);
      this.blklen = blklen;
      this.allow_misalign = `TRUE;
    endfunction : set_blklen

    function int unsigned get_blkcnt;
      return this.blknum;
    endfunction : get_blkcnt

    function void set_training;
      this.training = `TRUE;
    endfunction : set_training

    function bit is_training;
      return this.training;
    endfunction : is_training

  endclass : sd_transf_cl

  // *************************************************************************
  // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ SD CARD CLASS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  // *************************************************************************

  class sd_card_cl extends component_cl;
    static bit delay_1st_read_block = `TRUE;

    const static bit [31:0] TRAINING_PATTERN_ADDR_4B = 32'hFFFFFF00;
    const static bit [31:0] TRAINING_PATTERN_ADDR_8B = 32'hFFFFFF01;

    // ***** fields *****

    // mailboxes for transactions:
    protected mailbox #(sd_cmd)  mbx_cmd;
    protected mailbox #(sd_rsp)  mbx_rsp;
    protected mailbox #(sd_dat)  mbx_dat_rd;
    protected mailbox #(sd_dat)  mbx_dat_wr;
    protected mailbox #(bit)     mbx_lvs;
    protected bit                lvs;

    // internal options:
    protected const bit          uhsii_based;
    protected legacy_config_cl   card_config;

    // temp:
    protected bit                io_mode_support = `FALSE;

    // pseudo-random behaviour:
    protected int unsigned       wait_units;
    static int unsigned          random_seed;

    // SD card registers:
    protected bit [31:0]         ocr_reg;
    protected bit [127:0]        cid_reg;
    protected bit [127:0]        csd_reg;
    protected bit [15:0]         rca_reg;
    protected bit [15:0]         dsr_reg;
    protected bit [63:0]         scr_reg;

    protected bit [511:0]        ssr_reg;
    protected bit [31:0]         csr_reg;

    // memory

    protected sd_mem_cl          data_mem;

    protected datagen_cl         datagen;
    protected mailbox #(card_echo_event_cl)
                                 event_echo;

    // internal state:
    protected sd_cmd             last_cmd;
    protected sd_rsp             last_rsp;
    protected sd_dat             last_dat;
    protected sd_dat             ignore_dat;
    protected sd_meta            last_meta;

    protected card_st_e          card_st;
    protected sd_transf_cl       data_transf;
    protected bus_speed_e        bus_speed;

    protected bit                go_for_acmd;
    protected bit                illegal_cmd;
    protected bit                volt18_switched;
    protected int unsigned       block_length = 512;
    protected int unsigned       block_count  = 0;

    protected bus_width_e        bus_width;

    protected semaphore          voltage_init;

    protected process            data_th_obj,
                                 rcv_th_obj,
                                 prg_th_obj,
                                 main_th_obj,
                                 select_th_obj,
                                 volt_init_th_obj,
                                 bus_speed_th_obj,
                                 misc_th_obj;

    // ***** for error generation in card *****

    struct {
      bit cmd_tout;
      bit cmd_index;
      bit dat_tout;
      bit response;
      bit cmd_tout_acmd;
      bit cmd_index_acmd;
      bit response_acmd;
    } error_gen;

    semaphore error_gen_sem;

  `ifdef CARD_COVER
    local sd_err_flag_cover_cl err_flag_cov = null;

    function void set_legacy_card_covergroups(sd_err_flag_cover_cl err_flag_cov);
      this.err_flag_cov = err_flag_cov;
    endfunction : set_legacy_card_covergroups
  `endif // CARD_COVER

    bit enforce_none_rsp;

    static const int ENFORCE_N_CR = 0; // if 0 -> N_CR = random between 2..64

    static const int ENFORCE_N_AC = 0; // if 0 -> N_AC = random between 2..999

    // -----------------------------------------------------------------------
    //                   card register setup methods
    // -----------------------------------------------------------------------

    virtual function bit [127:0] generate_cid;
      // MID:
      generate_cid[127:120]   = $urandom % 256;
      // OID:
      generate_cid[119:112]   = 8'h4D; // M
      generate_cid[111:104]   = 8'h52; // R
      // PNM:
      generate_cid[103:96]    = 8'h45; // E
      generate_cid[95:88]     = 8'h56; // V
      generate_cid[87:80]     = 8'h41; // A
      generate_cid[79:72]     = 8'h53; // S
      generate_cid[71:64]     = 8'h44; // D
      // PRV:
      generate_cid[63:56]     = 8'b0001_0000;
      // PSN:
      generate_cid[47:16]     = $urandom;
      // reserved:
      generate_cid[23:20]     = 4'h0;
      // MDT:
      generate_cid[15:8]      = {4'd8, 4'd0}; // Aug 2013
      // CRC:
      generate_cid[7:1]       = calc_crc7(generate_cid[127:8], 120);
      generate_cid[0]         = `HIGH;
    endfunction : generate_cid

    // -------------------------------------------------------------------- //

    virtual function bit [127:0] generate_csd(bit v2 = `TRUE);
      // CSD_STRUCT:
      generate_csd[127:126]   = {`LOW, v2};
      // reserved:
      generate_csd[125:120]   = 6'b000000;
      // TAAC:
      generate_csd[119:112]   = v2 ? 8'h0E : {1'b0, 4'h2, 3'h0}; /* 1.2ns*/
      // NSAC:
      generate_csd[111:104]   = v2 ? 8'h00 : 8'h09;
      // TRAN_SPEED:
      generate_csd[103:96]    = 8'h32;
      // CCC:
      generate_csd[95:84]     = {2'b01, v2 | io_mode_support,  9'b110110101};
      // READ_BL_LEN:
      generate_csd[83:80]     = v2 ? 4'd9 : 4'd11; // ?
      // READ_BL_PARTIAL:
      generate_csd[79]        = ~v2;
      // XXX_BLK_MISALIGN:
      generate_csd[WRITE_BLK_MISALIGN_CSD_BIT]  = ~v2;
      generate_csd[READ_BLK_MISALIGN_CSD_BIT]   = ~v2;
      // DSR_IMPL:
      generate_csd[76]        = `FALSE;

      if (v2) begin
        // reserved
        generate_csd[75:70]   = 6'd0;
        // C_SIZE:
        generate_csd[69:48]   = 22'h010000;
      end
      else begin
        // reserved:
        generate_csd[75:74]   = 2'b00;
        // C_SIZE:
        generate_csd[73:62]   = 12'h100;
        // VDD_R_CURR_MIN:
        generate_csd[61:59]   = 3'h0;
        // VDD_R_CURR_MAX:
        generate_csd[58:56]   = 3'h7;
        // VDD_W_CURR_MIN:
        generate_csd[55:53]   = 3'h0;
        // VDD_W_CURR_MAX:
        generate_csd[52:50]   = 3'h7;
        // C_SIZE_MULT:
        generate_csd[49:47]   = 3'h0;
      end

      // ERASE_BLK_EN:
      generate_csd[46]        = `HIGH;
      // SECTOR_SIZE:
      generate_csd[45:39]     = v2 ? 7'h7F : 7'h00;
      // WP_GRP_SIZE:
      generate_csd[38:32]     = v2 ? 7'h00 : 7'h7F;
      // WP_GRP_ENABLE:
      generate_csd[31]        = `LOW;
      // reserved:
      generate_csd[30:29]     = 2'b00;

      // R2W_FACTOR:
      generate_csd[28:26]     = v2 ? 3'b010 : 3'b000;
      // WRITE_BL_LEN
      generate_csd[25:22]     = 4'h9;
      // WRITE_BL_PARTIAL:
      generate_csd[21]        = ~v2;
      // reserved:
      generate_csd[20:16]     = 5'b00000;
      // FILE_FORMAT_GRP:
      generate_csd[15]        = `LOW;
      // COPY:
      generate_csd[14]        = `LOW;

      // PERM_WRITE_PROTECT:
      generate_csd[13]        = `LOW;
      // TMP_WRITE_PROTECT:
      generate_csd[12]        = `LOW;
      //FILE_FORMAT:
      generate_csd[11:10]     = 2'b00;
      // reserved
      generate_csd[9:8]       = 2'b00;

      generate_csd[7:1]       = calc_crc7(generate_csd[127:8], 120);
      generate_csd[0]         = `HIGH;
    endfunction : generate_csd

    // -------------------------------------------------------------------- //

    function bit [63:0] generate_scr(capacity_e card_cap);
      // SCR_STRUCTURE:
      generate_scr[63:60] = 4'h0;
      // SD_SPEC:
      generate_scr[59:56] = 4'h3;
      // DATA_STAT_AFTER_ERASE:
      generate_scr[55]    = 1'b0;
      // SD_SECURITY:
      generate_scr[54:52] = (card_cap == SDSC ? 8'h2 :
                             card_cap == SDHC ? 8'h3 :
                             card_cap == SDXC ? 8'h4 :
                                                8'h0);
      // SD_BUS_WIDTHS:
      generate_scr[51:48] = 4'b0101;
      // SD_SPEC3:
      generate_scr[47]    = 1'b1;
      // EX_SECURITY:
      generate_scr[46:43] = 4'b0000;
      // Reserved:
      generate_scr[42:34] = 9'h000;
      // CMD_SUPPORT:
      generate_scr[33:32] = 2'b10;
      // reserved:
      generate_scr[31:0]  = 32'h00000000;
    endfunction : generate_scr

    // ==================================================================== //

    //-------------------------------------------------------------------------
    //                        SD CARD MODEL CONSTRUCTOR
    //-------------------------------------------------------------------------
    function new(input string             _name,
                 input component_cl       _parent,
                 input mailbox #(sd_cmd)  mbx_cmd,
                 input mailbox #(sd_rsp)  mbx_rsp,
                 input mailbox #(sd_dat)  mbx_dat_rd,
                 input mailbox #(sd_dat)  mbx_dat_wr,
                 input mailbox #(bit)     mbx_lvs,
                 input legacy_config_cl   card_config,
                 input sd_mem_cl          data_mem,
                 input bit                uhsii_based,
                 input bit                use_datagen);
      super.new(_name, _parent);

      this.mbx_cmd       = mbx_cmd;
      this.mbx_rsp       = mbx_rsp;
      this.mbx_dat_rd    = mbx_dat_rd;
      this.mbx_dat_wr    = mbx_dat_wr;
      this.mbx_lvs       = mbx_lvs;
      this.data_mem      = data_mem;
      this.uhsii_based   = uhsii_based;

      if (data_mem == null)
        this.data_mem    = new("memory", this);

      if (card_config == null)
        this.card_config = new(SDSC, legacy_config_cl::random_ocr_sd_leg());
      else
        this.card_config = card_config;

      this.voltage_init  = new (0);

      this.event_echo    = null;
      if (use_datagen)
      this.datagen       = new ("datagen", this);
      else
        this.datagen     = null;
      this.error_gen_sem = new (1);

      random_seed = random_seed + 26'h3FB6F5D;
      wait_units = random_seed;

      put_training_pattern_into_memory_4b;
      put_training_pattern_into_memory_8b;
    endfunction : new

    `INIT_LOGGING_SUBCOMPS_BEGIN
    `INIT_LOGGING_SUBCOMPS_END

    `CARD_LOGGING_UTILS

    //-------------------------------------------------------------------------
    //                              main thread task
    //-------------------------------------------------------------------------
    task start;
      fork
        run;
      join_none
    endtask : start

    virtual function string get_class_name;
      return "sd_card_cl";
    endfunction : get_class_name

    virtual function void dispose;
      int z = 0;
      if (data_th_obj != null) begin
        data_th_obj.kill;
        ++z;
      end
      if (rcv_th_obj != null) begin
        rcv_th_obj.kill;
        ++z;
      end
      if (prg_th_obj != null) begin
        prg_th_obj.kill;
        ++z;
      end
      if (main_th_obj != null) begin
        main_th_obj.kill;
        ++z;
      end
      if (select_th_obj != null) begin
        select_th_obj.kill;
        ++z;
      end
      if (volt_init_th_obj != null) begin
        volt_init_th_obj.kill;
        ++z;
      end
      if (bus_speed_th_obj != null) begin
        bus_speed_th_obj.kill;
        ++z;
      end
      if (misc_th_obj != null) begin
        misc_th_obj.kill;
        ++z;
      end

      `DISPLAY_LOGGER_NOTE($sformatf("card disposed ... %0d thread(s) killed", z))
    endfunction : dispose

    protected virtual task set_register_values;
      this.cid_reg       = generate_cid;
      this.csd_reg       = generate_csd(get_ccs(this.card_config.card_cap));
      this.scr_reg       = generate_scr(this.card_config.card_cap);
    endtask : set_register_values

    task run;
      process thread;

      select_th_obj      = null;
      volt_init_th_obj   = null;
      bus_speed_th_obj   = null;
      misc_th_obj        = null;

      `DISPLAY_LOGGER_NOTE($sformatf(
          "run method of %s card started seed=%h CID=%h",
          this.card_config.card_cap.name, random_seed, cid_reg));
      set_register_values;
      internal_reset;
      pass_bus_info_to_xtor; // reduntant with passing emmc_mode flag to xtor?

      fork : all_sd_card_threads
        begin
          #1ns;
          data_th_obj = process::self();
          forever
            data_th;
        end

        begin
          #2ns;
          rcv_th_obj = process::self();
          forever
            rcv_th;
        end

        begin
          #3ns;
          prg_th_obj = process::self();
          forever
            prg_th;
        end

        begin
          main_th_obj = process::self();
          forever
            execute_cmd;
        end
      join_none
    endtask : run

    function string to_string;
      if (this == null)
        return "null";
      else
        return $sformatf("sd_card random_seed=%h", random_seed);
    endfunction : to_string

    // -----------------------------------------------------------------------
    //            tasks for reporting events to the scoreboard
    // -----------------------------------------------------------------------

    local task echo_card_operation(sd_cmd last_cmd, sd_rsp last_rsp, card_st_e prev_state);
      sd_echo_event_cl echo_tmp;

      if (this.event_echo != null && ~last_cmd.power_cycle) begin
        echo_tmp = new(last_cmd, last_rsp, prev_state, this.uhsii_based);
        void'(this.event_echo.try_put(echo_tmp));
      end
    endtask : echo_card_operation

    // -------------------------------------------------------------------- //

    protected task echo_data_read(int blklen);
      data_echo_event_cl echo_tmp;
      if (this.event_echo != null) begin
        echo_tmp = new (`FALSE, blklen);
        echo_tmp.datagen_mode = this.data_transf.datagen_mode;
        echo_tmp.data_checksum = echo_tmp.datagen_mode ?
          this.datagen.check_crc :
          this.datagen.get_user_crc;
        void'(this.event_echo.try_put(echo_tmp));
      end
    endtask : echo_data_read

    // ---------------------------------------------------------------------- //

    protected task echo_data_write(ref bit [7:0] data[],
                                       bit       crc_err);
      data_echo_event_cl echo_tmp;
      //int err_cntr = 0, err_rep_limit = 10;
      string msg_tmp[$] = '{};

      if (this.event_echo != null) begin
        echo_tmp = new (`TRUE, data.size);
        echo_tmp.crc_err = crc_err;
        echo_tmp.datagen_mode = (datagen != null && datagen.is_active);
        if (echo_tmp.datagen_mode) begin
          echo_tmp.first_error = -1;
          for (int i = 0; i < data.size; ++i) begin
            bit [7:0] tmp = datagen.get8;
          `ifdef DATA_INTEGRITY_CHECK_DEBUG_WRITE
            if (i < 16)
              `DISPLAY_LOGGER_NOTE($sformatf(
                "i=%0d\t received: %2h expected: %2h", i, data[i], tmp))
          `endif // !DATA_INTEGRITY_CHECK_DEBUG_WRITE
            if (data[i] != tmp) begin
              if (echo_tmp.first_error == -1)
                echo_tmp.first_error = i;
              if (msg_tmp.size < 10)
                msg_tmp.push_back($sformatf(
                    "error at position %0d \t data expected: %0h received %0h",
                    i, tmp, data[i]));
            end
            this.datagen.calc_user_crc(data[i]);
          end
          echo_tmp.data_correct = (echo_tmp.first_error == -1);
          echo_tmp.data_checksum = this.datagen.get_user_crc;
          `ifndef C_ENV
            `ifdef UVM
            if (~crc_err)
            `else
            if (~crc_err && test_cases_pkg::card_data_integrity_check())
            `endif
          `else
            if (~crc_err)
          `endif
            report_data_integrity_check(echo_tmp, data, msg_tmp);
        end
        else begin
          foreach (data[i])
            this.datagen.calc_user_crc(data[i]);
          echo_tmp.data_checksum = this.datagen.get_user_crc;
        end
        void'(this.event_echo.try_put(echo_tmp));
      end
    endtask : echo_data_write

    //  - -  - -  - -  - -  - -  - -  - -  - -  - -  - -  - -  - -  - -  - -  //

    task report_data_integrity_check(data_echo_event_cl echo_tmp, ref bit [7:0] data[], string msg_tmp[$]);
      string this_msg = $sformatf(
          "Data integrity check for write transfer started around %t block no %0d %s -- received block data (hex):",
          this.data_transf.started, this.datagen.get_block_no - 1,
          echo_tmp.data_correct ? "passed" : "failed");

      for (int i = 0; i < data.size && i < 16; ++i)
        this_msg = $sformatf("%s %2h", this_msg, data[i]);
      if (data.size > 16)
         this_msg = $sformatf("%s ...", this_msg);
      if (echo_tmp.data_correct)
        `DISPLAY_LOGGER_GREEN(this_msg)
      else begin
        write_data_integrity_error:
        assert (0) else begin
        `DISPLAY_LOGGER_ERROR(this_msg)
        end
      end
      foreach (msg_tmp[i])
        `DISPLAY_LOGGER_NOTE(msg_tmp[i])
    endtask : report_data_integrity_check

    // ====================================================================== //

    //--------------------------------------------------------------------------
    //             "GENERIC" TASK FOR EXECUTION OF SD COMMANDS
    //--------------------------------------------------------------------------

    task execute_cmd();
      card_st_e prev_state;
      mbx_cmd.get(last_cmd);
      assert (last_cmd != null) else $fatal(1, "You found an unexpected state");
      last_rsp = new (NONE_RSP); // "predefined": no response
      prev_state = card_st;

      if (last_cmd.cancel_transf) begin
        // TLEN exhausted in SD-Tran
        data_transf = null;
        cancel_ongoing_read_blocks;
      end
      else if (last_cmd.power_cycle) begin
        // reset requested
        `DISPLAY_LOGGER_INFO($sformatf("RESET in SD%s", this.uhsii_based ? "-TRAN" : " card"))
        cancel_ongoing_read_blocks;
        internal_reset;
        echo_card_operation(last_cmd, last_rsp, prev_state); // reports power cycle to scoreboard
        pass_bus_info_to_xtor;
      end
      else if (last_cmd.init_boot)
        init_boot_procedure;
      else if (last_cmd.stop_boot)
        stop_boot_procedure;
      else if (last_cmd.crc_err)
        csr_reg[COM_CRC_ERROR_CSR_BIT] = `TRUE;
      else begin
        illegal_cmd = `FALSE;

        erase_seq_reset_check;
        irq_st_compl;

        if (uhsii_based & enforce_none_rsp) begin
          illegal_cmd = `TRUE;
          enforce_none_rsp = `FALSE;
          if (~last_cmd.app && last_cmd.index inside {6'd32, 6'd33, 6'd38})
            this.data_transf = null;
        end
        else if (!last_cmd.app && !go_for_acmd)
          case (last_cmd.index)
            6'b000000:   execute_cmd0;
            6'b000001:   execute_cmd1;
            6'b000010:   execute_cmd2;
            6'b000011:   execute_cmd3;
            6'b000100:   execute_cmd4;
            6'b000101:   execute_cmd5;
            6'b000110:   execute_cmd6;
            6'b000111:   execute_cmd7;
            6'b001000:   execute_cmd8;
            6'b001001:   execute_cmd9;
            6'b001010:   execute_cmd10;
            6'b001011:   execute_cmd11;
            6'b001100:   execute_cmd12;
            6'b001101:   execute_cmd13;
            6'b001110:   execute_cmd14;
            6'b001111:   execute_cmd15;
            6'b010000:   execute_cmd16;
            6'b010001:   execute_cmd17;
            6'b010010:   execute_cmd18;
            6'b010011:   execute_cmd19;
            6'b010100:   execute_cmd20;
            6'b010101:   execute_cmd21;
            6'b010110:   execute_cmd22;
            6'b010111:   execute_cmd23;
            6'b011000:   execute_cmd24;
            6'b011001:   execute_cmd25;
            6'b011010:   execute_cmd26;
            6'b011011:   execute_cmd27;
            6'b011100:   execute_cmd28;
            6'b011101:   execute_cmd29;
            6'b011110:   execute_cmd30;
            6'b011111:   execute_cmd31;
            6'b100000:   execute_cmd32;
            6'b100001:   execute_cmd33;
            6'b100010:   execute_cmd34;
            6'b100011:   execute_cmd35;
            6'b100100:   execute_cmd36;
            6'b100101:   execute_cmd37;
            6'b100110:   execute_cmd38;
            6'b100111:   execute_cmd39;
            6'b101000:   execute_cmd40;
            6'b101001:   execute_cmd41;
            6'b101010:   execute_cmd42;
            6'b101011:   execute_cmd43;
            6'b101100:   execute_cmd44;
            6'b101101:   execute_cmd45;
            6'b101110:   execute_cmd46;
            6'b101111:   execute_cmd47;
            6'b110000:   execute_cmd48;
            6'b110001:   execute_cmd49;
            6'b110010:   execute_cmd50;
            6'b110011:   execute_cmd51;
            6'b110100:   execute_cmd52;
            6'b110101:   execute_cmd53;
            6'b110110:   execute_cmd54;
            6'b110111:   execute_cmd55;
            6'b111000:   execute_cmd56;
            6'b111001:   execute_cmd57;
            6'b111010:   execute_cmd58;
            6'b111011:   execute_cmd59;
            6'b111100:   execute_cmd60;
            6'b111101:   execute_cmd61;
            6'b111110:   execute_cmd62;
            6'b111111:   execute_cmd63;
            default:
              unknown_cmd:
              assert (0) else begin
              `DISPLAY_LOGGER_ERROR("unknown command")
              end
          endcase
        else
          case (last_cmd.index)
            6'b000000:   execute_acmd0;
            6'b000001:   execute_acmd1;
            6'b000010:   execute_acmd2;
            6'b000011:   execute_acmd3;
            6'b000100:   execute_acmd4;
            6'b000101:   execute_acmd5;
            6'b000110:   execute_acmd6;
            6'b000111:   execute_acmd7;
            6'b001000:   execute_acmd8;
            6'b001001:   execute_acmd9;
            6'b001010:   execute_acmd10;
            6'b001011:   execute_acmd11;
            6'b001100:   execute_acmd12;
            6'b001101:   execute_acmd13;
            6'b001110:   execute_acmd14;
            6'b001111:   execute_acmd15;
            6'b010000:   execute_acmd16;
            6'b010001:   execute_acmd17;
            6'b010010:   execute_acmd18;
            6'b010011:   execute_acmd19;
            6'b010100:   execute_acmd20;
            6'b010101:   execute_acmd21;
            6'b010110:   execute_acmd22;
            6'b010111:   execute_acmd23;
            6'b011000:   execute_acmd24;
            6'b011001:   execute_acmd25;
            6'b011010:   execute_acmd26;
            6'b011011:   execute_acmd27;
            6'b011100:   execute_acmd28;
            6'b011101:   execute_acmd29;
            6'b011110:   execute_acmd30;
            6'b011111:   execute_acmd31;
            6'b100000:   execute_acmd32;
            6'b100001:   execute_acmd33;
            6'b100010:   execute_acmd34;
            6'b100011:   execute_acmd35;
            6'b100100:   execute_acmd36;
            6'b100101:   execute_acmd37;
            6'b100110:   execute_acmd38;
            6'b100111:   execute_acmd39;
            6'b101000:   execute_acmd40;
            6'b101001:   execute_acmd41;
            6'b101010:   execute_acmd42;
            6'b101011:   execute_acmd43;
            6'b101100:   execute_acmd44;
            6'b101101:   execute_acmd45;
            6'b101110:   execute_acmd46;
            6'b101111:   execute_acmd47;
            6'b110000:   execute_acmd48;
            6'b110001:   execute_acmd49;
            6'b110010:   execute_acmd50;
            6'b110011:   execute_acmd51;
            6'b110100:   execute_acmd52;
            6'b110101:   execute_acmd53;
            6'b110110:   execute_acmd54;
            6'b110111:   execute_acmd55;
            6'b111000:   execute_acmd56;
            6'b111001:   execute_acmd57;
            6'b111010:   execute_acmd58;
            6'b111011:   execute_acmd59;
            6'b111100:   execute_acmd60;
            6'b111101:   execute_acmd61;
            6'b111110:   execute_acmd62;
            6'b111111:   execute_acmd63;
            default:
              unknown_acmd:
              assert (0) else begin
              `DISPLAY_LOGGER_ERROR("unknown command")
              end
          endcase

        assert (last_rsp != null) else $fatal(1, "Internal Card Model implementation error");

        if (card_st < INA_ST)
          csr_reg[12:9] = card_st[3:0];
        check_and_set_illegal_command_bit_status();
        go_for_acmd = csr_reg[APP_CMD_CSR_BIT];

        if (last_rsp.rsp_kind != NONE_RSP &&
            //!(last_cmd != null && !go_for_acmd &&
            // (last_cmd.index == 19 || last_cmd.index == 21)) ) begin
            !(last_cmd != null && !go_for_acmd ) ) begin
          bit clear_rsp = `FALSE;
          error_gen_sem.get(1);
          if (!go_for_acmd && (last_cmd.index == 12 ||
                               last_cmd.index == 23)) begin
            clear_rsp = error_gen.cmd_tout_acmd;
            error_gen.cmd_tout_acmd = `FALSE;
          end
          else begin
            clear_rsp = error_gen.cmd_tout;
            error_gen.cmd_tout = `FALSE;
          end
          error_gen_sem.put(1);
          if (clear_rsp) begin
            last_rsp = new (NONE_RSP);
            last_rsp.delay_cycles = 1;
            `DISPLAY_LOGGER_INFO("CMD timeout error injection -> no RSP")
          end
        end

        if (last_rsp.rsp_kind != NONE_RSP) begin
          csr_reg[COM_CRC_ERROR_CSR_BIT] = `FALSE;
          if (last_rsp.rsp_kind == R1)
            clear_csr_bits_on_read;
          else if (last_rsp.rsp_kind == R5)
            clear_sdio_flags_on_read;
          inject_response_errors(prev_state);

          if (!uhsii_based && last_rsp.delay_cycles == 0) begin
            if (ENFORCE_N_CR != 0)
              last_rsp.delay_cycles = ENFORCE_N_CR;
            else if (card_config.no_cmd_delays)
              last_rsp.delay_cycles = $urandom_range(4,2);
            // otherwise delay_cycles remains 0, then it will be randomized
          end
        end
        else if (uhsii_based && !illegal_cmd)
          // RES witout payload to be sent in UHS:
          last_rsp = new (EMPTY_RSP);
        reset_block_count;

        echo_card_operation(last_cmd, last_rsp, prev_state);
      end
    `ifdef CARD_COVER
      case (last_rsp.rsp_kind)
        R1:      this.err_flag_cov.r1_issued(uhsii_based, last_rsp.contents[0]);
        R5:      this.err_flag_cov.r5_issued(uhsii_based, last_rsp.contents[0][15:8],
                                                          last_rsp.contents[0][7:0]);
      endcase
    `endif // CARD_COVER
      mbx_rsp.put(last_rsp);
    endtask : execute_cmd

    // ==================================================================== //

    protected virtual function void change_state(card_st_e new_st);
    `ifdef USE_LOGGERS
      `DISPLAY_LOGGER_INFO($sformatf(
          "SD card state changed from <i>%s</i> to <b>%s</b>",
          card_st.name, new_st.name))
    `else // USE_LOGGERS
      `DISPLAY_LOGGER_INFO($sformatf(
          "SD card state changed from %s to %s",
          card_st.name, new_st.name))
    `endif // !USE_LOGGERS
      card_st = new_st;
    endfunction : change_state

    protected virtual function void go_to_previous_state(sd_rsp_e rsp_kind, card_st_e prev_st);
      card_st = prev_st;
      `ifdef USE_LOGGERS
        `DISPLAY_LOGGER_INFO($sformatf(
            "Going back to <b>%s</b> due to errors injected in <i>%s</i>",
            card_st.name, rsp_kind.name))
      `else // USE_LOGGERS
        `DISPLAY_LOGGER_INFO($sformatf(
            "Going back to %s due to errors injected in %s",
            card_st.name, rsp_kind.name))
      `endif // !USE_LOGGERS
    endfunction : go_to_previous_state

    // -------------------------------------------------------------------- //

    protected virtual function void operation_compl;
      if (card_st == DATA_ST || card_st == PRG_ST) begin
        change_state(TRAN_ST);
        csr_reg[12:9] = card_st[3:0];
      end
      else if (card_st == DIS_ST) begin
        change_state(STBY_ST);
        csr_reg[12:9] = card_st[3:0];
      end
      else if (card_st == BTST_ST) begin
        change_state(IDLE_ST);
        csr_reg[12:9] = card_st[3:0];
      end
    endfunction : operation_compl

    // -------------------------------------------------------------------- //

    protected virtual task internal_reset(bit volt_back = `TRUE);
      change_state(IDLE_ST);
      if (this.uhsii_based || volt_back) begin
        voltage_init    =  new (1);
        volt18_switched = `FALSE;
        ocr_reg         = {8'h00, this.card_config.voltage_window};
      end
      csr_reg           = 32'h00000000;

      data_transf = null;

      if (!uhsii_based)
        rca_reg         = 16'h0000;

      if (select_th_obj != null) begin
        select_th_obj.kill;
        `DISPLAY_LOGGER_NOTE("select_thread killed")
      end
      if (volt_init_th_obj != null) begin
        volt_init_th_obj.kill;
        `DISPLAY_LOGGER_NOTE("volt_init_th_obj killed")
      end
      if (bus_speed_th_obj != null) begin
        bus_speed_th_obj.kill;
        `DISPLAY_LOGGER_NOTE("bus_speed_th_obj killed")
      end
      if (misc_th_obj != null) begin
        misc_th_obj.kill;
        `DISPLAY_LOGGER_NOTE("misc_th_obj.kill killed")
      end
      // this is the 2nd time just to be more sure...

      repeat (2) begin
        int z = 0;
        #1ns;
        while (mbx_dat_rd.try_get(ignore_dat)) ++z;
        `DISPLAY_LOGGER_NOTE($sformatf("read block queue purged: %0d", z))
      end
      reset_bus_if;
    endtask : internal_reset

    // -------------------------------------------------------------------- //

    local function void erase_seq_reset_check;
      if (card_st == TRAN_ST && data_transf != null &&
         (data_transf.erase_start || data_transf.erase_end)) begin
        if (last_cmd.index == 6'd32 ||
            last_cmd.index == 6'd33 ||
            last_cmd.index == 6'd38 ||
            last_cmd.index == 6'd13);
        else begin
          csr_reg[ERASE_RESET_CSR_BIT] = `TRUE;
          data_transf = null;
          `DISPLAY_LOGGER_MSG("Erase sequence reset")
        end
      end
    endfunction : erase_seq_reset_check

    // -------------------------------------------------------------------- //

    virtual function void irq_st_compl();
    endfunction : irq_st_compl

    // -------------------------------------------------------------------- //

    virtual protected function void check_and_set_illegal_command_bit_status;
      csr_reg[ILLEGAL_COMMAND_CSR_BIT] = illegal_cmd;
    endfunction : check_and_set_illegal_command_bit_status

    // -------------------------------------------------------------------- //

    local function void reset_block_count;
      if ((card_st == TRAN_ST || card_st == RCV_ST || card_st == DATA_ST) &&
          block_count > 0 && last_cmd.index != 6'd23)
        block_count = 0;
    endfunction : reset_block_count

    // -------------------------------------------------------------------- //

    protected task cancel_ongoing_read_blocks;
      if (card_st == DATA_ST || card_st == BTST_ST) begin
        int z = 0;
        while (mbx_dat_rd.try_get(ignore_dat)) ++z;
        `DISPLAY_LOGGER_NOTE($sformatf("cancel_ongoing_read_blocks: %0d", z))
      end
    endtask : cancel_ongoing_read_blocks

    protected task cancel_ongoing_write_blocks(bit card_busy = `FALSE);
      if (!uhsii_based && card_st == RCV_ST) begin
        if (last_cmd != null && !last_cmd.app && last_cmd.index == 6'd12) begin
          // CMD12 cancels transmission of CRC token if it's taking place
          if (mbx_dat_rd.try_get(ignore_dat))
            `DISPLAY_LOGGER_NOTE("cancel_ongoing_write_blocks: token cancelled")
          else
            `DISPLAY_LOGGER_NOTE("cancel_ongoing_write_blocks: no token found")
        end
        else
          `DISPLAY_LOGGER_NOTE(
              "cancel_ongoing_write_blocks: transfer ended by other means than CMD12")
        last_meta = new;
        last_meta.wr_dat_end = `TRUE;
        last_meta.busy = card_busy;
        mbx_dat_rd.put(last_meta);
      end
    endtask : cancel_ongoing_write_blocks

    // -------------------------------------------------------------------- //

    local function void clear_csr_bits_on_read;
      csr_reg[OUT_OF_RANGE_CSR_BIT]        = `FALSE;
      csr_reg[ADDRESS_ERROR_CSR_BIT]       = `FALSE;
      csr_reg[BLOCK_LEN_ERROR_CSR_BIT]     = `FALSE;
      csr_reg[ERASE_SEQ_ERROR_CSR_BIT]     = `FALSE;
      csr_reg[ERASE_PARAM_CSR_BIT]         = `FALSE;
      csr_reg[WP_VIOLATION_CSR_BIT]        = `FALSE;
      csr_reg[CARD_IS_LOCKED_CSR_BIT]      = `FALSE;
      csr_reg[LOCK_UNLOCK_FAILED_CSR_BIT]  = `FALSE;
      csr_reg[CARD_ECC_FAILED_CSR_BIT]     = `FALSE;
      csr_reg[CC_ERROR_CSR_BIT]            = `FALSE;
      csr_reg[ERROR_CSR_BIT]               = `FALSE;
      csr_reg[CSD_OVERWRITE_CSR_BIT]       = `FALSE;
      csr_reg[WP_ERASE_SKIP_CSR_BIT]       = `FALSE;
      csr_reg[ERASE_RESET_CSR_BIT]         = `FALSE;
      csr_reg[APP_CMD_CSR_BIT]             = `FALSE;
    endfunction : clear_csr_bits_on_read

    // -------------------------------------------------------------------- //

    protected virtual function void clear_sdio_flags_on_read;
      // implementation to be provided in class sdio_card_cl
    endfunction : clear_sdio_flags_on_read

    // -------------------------------------------------------------------- //

    protected virtual task init_boot_procedure;
      no_card_support_for_boot_start:
      assert (0) else begin
      `DISPLAY_LOGGER_ERROR("SD Card does not support boot procedure")
      end
    endtask : init_boot_procedure

    protected virtual task stop_boot_procedure;
      no_card_support_for_boot_stop:
      assert (0) else begin
      `DISPLAY_LOGGER_ERROR("SD Card does not support boot procedure")
      end
    endtask : stop_boot_procedure

    // -------------------------------------------------------------------- //

    local function bit correct_block_length;
      return ! (block_length > 2048); // max blklen should be 512
    endfunction

    // -------------------------------------------------------------------- //

    protected task send_card_busy(bit busy);
      last_meta = new;
      last_meta.busy = busy;
      mbx_dat_rd.put(last_meta);
      csr_reg[READY_FOR_DATA_CSR_BIT] = ~busy;
    endtask : send_card_busy

    // -------------------------------------------------------------------- //

    local task inject_response_errors(card_st_e prev_st);
      bit inject_cmd_index_error = `FALSE,
          inject_general_response_error = `FALSE;
      error_gen_sem.get(1);
      if (!go_for_acmd && (last_cmd.index == 12 ||
                           last_cmd.index == 23)) begin
        inject_cmd_index_error = error_gen.cmd_index_acmd;
        error_gen.cmd_index_acmd = `FALSE;
        inject_general_response_error = error_gen.response_acmd;
        error_gen.response_acmd = `FALSE;
      end
//      else if (!go_for_acmd && (last_cmd.index == 19 ||
//                                last_cmd.index == 21)) ;
//        // no error injection for tuning!
      else begin
        if (error_gen.cmd_index && (last_rsp.rsp_kind == R1 ||
                                    last_rsp.rsp_kind == R5 ||
                                    last_rsp.rsp_kind == R6 ||
                                    last_rsp.rsp_kind == R7)) begin
          inject_cmd_index_error = `TRUE;
          error_gen.cmd_index = `FALSE;
        end
        else if (error_gen.response && (last_rsp.rsp_kind == R1 ||
                                        last_rsp.rsp_kind == R5)) begin
          inject_general_response_error = `TRUE;
          error_gen.response = `FALSE;
        end
      end
      error_gen_sem.put(1);
      if (inject_cmd_index_error) begin
        last_rsp.index ^= ($urandom % 6'd63) + 1'b1;
        `DISPLAY_LOGGER_NOTE("error injection: CMD index")
      end
      if (inject_general_response_error) begin
        int err_flag_idx = -1;
        case (last_rsp.rsp_kind)
          R1:
            if (!$urandom_range(7)) begin
              bit [3:0] prev_contents = last_rsp.contents[0][12:9];
              last_rsp.contents[0][12:9] = $urandom() % 16;
              `DISPLAY_LOGGER_NOTE($sformatf(
                  "error injection: SD card state in R1 response set to %0h instead of %0h",
                  last_rsp.contents[0][12:9], prev_contents))
            end
            else
              do
                err_flag_idx = $urandom_range(0, 31);
              while (err_flag_idx inside {9, 10, 11, 12});
          R5:
            if (!$urandom_range(7)) begin
              bit [1:0] prev_contents = last_rsp.contents[0][13:12];
              last_rsp.contents[0][13:12] = $urandom() % 4;
              `DISPLAY_LOGGER_NOTE($sformatf(
                  "error injection: SDIO card state in R5 response set to %0d instead of %0d",
                  last_rsp.contents[0][13:12], prev_contents))
            end
            else
              do
                err_flag_idx = $urandom_range(8, 15);
              while (err_flag_idx inside {12, 13});
          default:
            rsp_err_inj_err: assert (0) else $fatal(1, "Internal Card Model implementation error");
        endcase
        if (err_flag_idx >= 0) begin
          last_rsp.contents[0][err_flag_idx] = `TRUE;
          `DISPLAY_LOGGER_NOTE($sformatf("error injection: response bit %0d", err_flag_idx))
        end
      end
      if (last_rsp.check_response_error_flag) begin
        go_to_previous_state(last_rsp.rsp_kind, prev_st);
        if (this.data_transf != null &&
            (~go_for_acmd && ~last_cmd.app &&
             last_cmd.index inside {6'd17, 6'd18, 6'd24, 6'd25,
                                    6'd32, 6'd33, 6'd38, 6'd53})
             /* || (go_for_acmd | last_cmd.app) */ )
          this.data_transf = null;
        if (~go_for_acmd && ~last_cmd.app && last_cmd.index inside {6'd24, 6'd25, 6'd53})
          this.last_rsp.wr_dat_blklen = -1;
      end
    endtask : inject_response_errors

    // -------------------------------------------------------------------- //

    protected task inject_dat_timeout_error(output bit timeout, input bit enforce = `FALSE);
        error_gen_sem.get(1);
        if (error_gen.dat_tout && (enforce || !$urandom_range(9))) begin
          timeout = `TRUE;
          error_gen.dat_tout = `FALSE;
          `DISPLAY_LOGGER_INFO("DAT timeout error injection")
        end
        else
          timeout = `FALSE;
        error_gen_sem.put(1);
    endtask : inject_dat_timeout_error

    // -------------------------------------------------------------------- //

    protected task respond_with_r1;
      last_rsp = new(R1);
      last_rsp.index = last_cmd.index;
      last_rsp.contents[0] = csr_reg;
    endtask : respond_with_r1

    // -------------------------------------------------------------------- //

    protected virtual function void inappropriate_state;
      `DISPLAY_LOGGER_WARNING($sformatf(
          "%sCMD%0d is illegal in the current state: %s",
          (last_cmd.app || go_for_acmd) ? "A" : " ",
          last_cmd.index, card_st.name))
      illegal_cmd = `TRUE;
    endfunction : inappropriate_state

    // ------------------------------------------------------------------- //

    function void not_implemented_cmd;
      `DISPLAY_LOGGER_WARNING($sformatf(
          "%sCMD%0d is not implemented in card model",
         (last_cmd.app || this.go_for_acmd) ? "A" : "",
          last_cmd.index))
      illegal_cmd = `TRUE;
    endfunction : not_implemented_cmd

    // =================================================================== //

    // ***** switch functions manipulated with CMD6 *****

    local bit [511:0] card_functions = {
      16'h0000,              // [511:496] max current/power consumption

      16'h0001,              // [495:480] function group 6 support bits
      16'h0001,              // [479:464] function group 5 support bits
      16'h0001,              // [463:448] function group 4 support bits
      16'h0001,              // [447:432] function group 3 support bits
      16'h0001,              // [431:416] function group 2 support bits
      16'h0001,              // [415:400] function group 1 support bits

      4'h0,                  // [399:396] function group 6 selection
      4'h0,                  // [395:392] function group 5 selection
      4'h0,                  // [391:388] function group 4 selection
      4'h0,                  // [387:384] function group 3 selection
      4'h0,                  // [383:380] function group 2 selection
      4'h0,                  // [379:376] function group 1 selection

      8'h00,                 // [375:368] data structure version

      {6{16'h0000}},         // function group N busy status
      {17{16'h0000}}         // RESERVED
    };

    // -------------------------------------------------------------------- //

    protected virtual task pass_bus_info_to_xtor;
      if (!uhsii_based) begin
        sd_meta bus_meta = new;
        bus_meta.change_speed = `TRUE;

        if (volt18_switched)
          case (card_functions[379:376])
            4'h0:    bus_meta.new_speed = SDR12;
            4'h1:    bus_meta.new_speed = SDR25;
            4'h2:    bus_meta.new_speed = SDR50;
            4'h3:    bus_meta.new_speed = SDR104;
            4'h4:    bus_meta.new_speed = DDR50;
            default: bus_meta.change_speed = `FALSE;
          endcase
        else if (card_st == IDLE_ST  || card_st == READY_ST ||
                 card_st == IDENT_ST || card_st == INA_ST)
          bus_meta.new_speed = IDENT_SPEED;
        else
          case (card_functions[379:376])
            4'h0:    bus_meta.new_speed = DEFAULT_SPEED;
            4'h1:    bus_meta.new_speed = HIGH_SPEED;
            default: bus_meta.change_speed = `FALSE;
          endcase

        if (bus_meta.change_speed && bus_speed != bus_meta.new_speed) begin
          `DISPLAY_LOGGER_NOTE($sformatf(
              "Bus speed to be changed from %s to %s", bus_speed.name, bus_meta.new_speed.name))
          bus_speed = bus_meta.new_speed;
        end

        case (ssr_reg[511:510])
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
          fork
            begin
              bus_speed_th_obj = process::self();
              #7ns;
              `WAIT_COND (mbx_rsp.num() == 0, 8.3ns)
              wait (card_st != DATA_ST);
              #7ns;
              mbx_dat_rd.put(bus_meta);
              bus_speed_th_obj = null;
            end
          join_none
      end
    endtask : pass_bus_info_to_xtor

    // -------------------------------------------------------------------- //

    local task check_or_set_sd_functions;
      automatic bit [399:376] card_func_temp;
      automatic bit [511:496] max_pow_or_curr;

      last_dat = new(`FALSE, `FALSE, bus_width);

      card_functions[404:400] = uhsii_based      ? 5'b00001 :
                                volt18_switched  ? 5'b11111 :
                                                   5'b00011;
      // group 1
      card_func_temp[379:376] =
        last_cmd.arg[3:0] == 4'hF ? card_functions[379:376] :
        card_functions[16'd400 + last_cmd.arg[3:0]] ?
          last_cmd.arg[3:0] : 4'hF;
      // group 2
      card_func_temp[383:380] =
        last_cmd.arg[7:4] == 4'hF ? card_functions[383:380] :
        card_functions[16'd400 + last_cmd.arg[7:4]] ?
          last_cmd.arg[7:4] : 4'hF;
      // group 3
      card_func_temp[387:384] =
        last_cmd.arg[11:8] == 4'hF ? card_functions[387:384] :
        card_functions[16'd400 + last_cmd.arg[11:8]] ?
          last_cmd.arg[11:8] : 4'hF;
      // group 4
      card_func_temp[391:388] =
        last_cmd.arg[15:12] == 4'hF ? card_functions[391:388] :
        card_functions[16'd400 + last_cmd.arg[15:12]] ?
          last_cmd.arg[15:12] : 4'hF;
      // group 5
      card_func_temp[395:392] =
        last_cmd.arg[19:16] == 4'hF ? card_functions[395:392] :
        card_functions[16'd400 + last_cmd.arg[19:16]] ?
          last_cmd.arg[19:16] : 4'hF;
      // group 6
      card_func_temp[399:396] =
        last_cmd.arg[23:20] == 4'hF ? card_functions[399:396] :
        card_functions[16'd400 + last_cmd.arg[23:20]] ?
        last_cmd.arg[23:20] : 4'hF;

      if (card_func_temp[379:376] == 4'hF ||
          card_func_temp[383:380] == 4'hF ||
          card_func_temp[387:384] == 4'hF ||
          card_func_temp[391:388] == 4'hF ||
          card_func_temp[395:392] == 4'hF ||
          card_func_temp[399:396] == 4'hF)
        max_pow_or_curr = 0;
      else
        max_pow_or_curr = ((card_func_temp[379:376] + 5) << 3) +
                          ((card_func_temp[383:380] + 4) << 2) +
                          ((card_func_temp[387:384] + 3) << 1) +
                           (card_func_temp[391:388] + 2);

      if (last_cmd.arg[31] && max_pow_or_curr > 0) begin // set function
        card_functions[511:496] = max_pow_or_curr;
        card_functions[399:376] = card_func_temp;
        pass_bus_info_to_xtor;
      end

      last_dat.data = new [64];
      for (int i = 0; i < 512; ++i)
        last_dat.data[i/8][7-i%8] = card_functions[511-i];

      if (!last_cmd.arg[31]) begin // check only
        {last_dat.data[0],
         last_dat.data[1]} = max_pow_or_curr;
        {last_dat.data[14],
         last_dat.data[15],
         last_dat.data[16]} = card_func_temp;
      end
      set_n_ac_delay(last_dat);
      mbx_dat_rd.put(last_dat);
    endtask : check_or_set_sd_functions

    // -------------------------------------------------------------------- //

    protected virtual function void reset_bus_if;
      card_functions[399:0] = {400{`FALSE}};
      ssr_reg[511:510]  =  2'b00;
      `DISPLAY_LOGGER_NOTE("Bus conditions reset");
      if (!uhsii_based)
        fork send_card_busy(`FALSE); join_none
    endfunction : reset_bus_if

    // ==================================================================== //

    //------------------------------------------------------------------------
    // TASKS FOR EXECUTION OF SD COMMANDS -- DETAILED
    //------------------------------------------------------------------------

    // ***** regular commands *****

    protected virtual task execute_cmd0;
      // GO_IDLE_STATE
      if (card_st == INA_ST)
        return;
      cancel_ongoing_read_blocks;
      cancel_ongoing_write_blocks;
      internal_reset(`FALSE);
      pass_bus_info_to_xtor;
    endtask : execute_cmd0

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd1;
      // reserved (CMD1)
      not_implemented_cmd;
    endtask : execute_cmd1

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd2;
      // ALL_SEND_CID
      if (card_st == READY_ST) begin
        change_state(IDENT_ST);
        last_rsp = new(R2);
        last_rsp.index = 6'b111111;
        last_rsp.contents[0] =  cid_reg[127:96];
        last_rsp.contents[1] =  cid_reg[95:64];
        last_rsp.contents[2] =  cid_reg[63:32];
        last_rsp.contents[3] = {cid_reg[31:1], 1'b1};
        last_rsp.delay_cycles = 5; // use N_ID delay
      end
      else
        inappropriate_state;
    endtask : execute_cmd2

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd3;
      // SEND_RELATIVE_ADDR
      if (mbx_lvs.num() >0) begin
        mbx_lvs.get(lvs);
        if (lvs) begin
          volt18_switched = `TRUE;
          card_functions[379:376] = 4'h0;
        end
      end
      if (card_st == IDENT_ST)
        change_state(STBY_ST);
      if (card_st == STBY_ST) begin
        if (!uhsii_based)
          rca_reg  = ($urandom() % 32'h0000FFFF) + 32'h00000001;
        last_rsp = new (R6);
        last_rsp.index = 6'd3;
        last_rsp.contents[0] = {rca_reg,
                                csr_reg[23:22], csr_reg[19], csr_reg[12:0]};
        `DISPLAY_LOGGER_NOTE($sformatf("%h published as new RCA", rca_reg))
        pass_bus_info_to_xtor;
      end
      else
        inappropriate_state;
    endtask : execute_cmd3

    // --------------------------------------------------------------------- //

    protected virtual task execute_cmd4;
      // SET_DSR
      if (card_st == STBY_ST) begin
        dsr_reg = last_cmd.arg[31:16];
      end
      else
        inappropriate_state;
    endtask : execute_cmd4

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd5;
      // reserved for SDIO (CMD5)
      not_implemented_cmd;
    endtask : execute_cmd5

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd6;
      // SWITCH_FUNC
      if (card_st == TRAN_ST) begin
        respond_with_r1;
        check_or_set_sd_functions;
        change_state(DATA_ST);
      end
      else
        inappropriate_state;
    endtask : execute_cmd6

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd7;
      // (DE)SELECT_CARD
      #0.1ns;
      `DISPLAY_LOGGER_NOTE($sformatf("CMD7 %s arg=%h rca_reg=%h", (last_cmd.arg[31:16] == rca_reg ?
          "select" : "deselect"), last_cmd.arg[31:16], rca_reg))
      if (last_cmd.arg[31:16] == rca_reg) begin
        // -> select
        if (card_st == STBY_ST) begin
          change_state(TRAN_ST);
          if (!uhsii_based)
            fork : select_busy_thread
              begin
                select_th_obj = process::self();
                //bit busy_timeout;
                send_card_busy(`TRUE);
                `WAIT_COND (mbx_rsp.num() == 0, 8.3ns)
                #1385ns;
                send_card_busy(`FALSE);
                select_th_obj = null;
              end
            join_none
        end
        else if (card_st == DIS_ST) begin
          change_state(PRG_ST);
          if (!uhsii_based)
            send_card_busy(`TRUE);
        end
        else
          inappropriate_state;
      end
      else begin
        // -> deselect
        if (card_st == STBY_ST || card_st == TRAN_ST || card_st == DATA_ST)
          change_state(STBY_ST);
        else if (card_st == PRG_ST && !uhsii_based) begin
          change_state(DIS_ST);
          if (!uhsii_based)
            fork : deselect_busy_thread
              begin
                //bit busy_timeout;
                select_th_obj = process::self();
                #143ns;
                send_card_busy(`FALSE);
                select_th_obj = null;
              end
            join_none
        end
        else
          inappropriate_state;
      end

      if (!illegal_cmd && last_cmd.arg[31:16] == rca_reg)
        respond_with_r1;
    endtask : execute_cmd7

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd8;
      // SEND_IF_COND
      if (card_st == IDLE_ST) begin
        if (last_cmd.arg[11:8] == 4'b0001 ||
            last_cmd.arg[11:8] == 4'b0010) begin
          last_rsp = new (R7);
          last_rsp.index = 6'd8;
          last_rsp.contents[0][31:12] = 20'h00000;          // reserved
          last_rsp.contents[0][11:0]  = last_cmd.arg[11:0]; // voltage + echo
          last_rsp.delay_cycles = 5; // use N_ID delay
        end
      end
      else
        inappropriate_state;
    endtask : execute_cmd8

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd9;
      // SEND_CSD
      if (uhsii_based || last_cmd.arg[31:16] == rca_reg) begin
      // RCA arg is ignored in UHS card for cmnds other than CMD7
        if (card_st == STBY_ST) begin
          last_rsp = new(R2);
          last_rsp.contents[0] =  csd_reg[127:96];
          last_rsp.contents[1] =  csd_reg[95:64];
          last_rsp.contents[2] =  csd_reg[63:32];
          last_rsp.contents[3] = {csd_reg[31:1], 1'b1};
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd9

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd10;
      // SEND_CID
      if (uhsii_based || last_cmd.arg[31:16] == rca_reg) begin
      // RCA arg is ignored in UHS card for cmnds other than CMD7
        if (card_st == STBY_ST) begin
          last_rsp = new(R2);
          last_rsp.contents[0] =  cid_reg[127:96];
          last_rsp.contents[1] =  cid_reg[95:64];
          last_rsp.contents[2] =  cid_reg[63:32];
          last_rsp.contents[3] = {cid_reg[31:1], 1'b1};
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd10

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd11;
      // VOLTAGE_SWITCH
      if (uhsii_based) // not supported in UHS-II
        illegal_cmd = `TRUE;
      else if (card_st == READY_ST
          ) begin
        respond_with_r1;
        last_rsp.switch2volt18 = `TRUE;
        ocr_reg[24] = `FALSE; // S18A
        volt18_switched = `TRUE;
        //////??????
        pass_bus_info_to_xtor;
      end
      else
        inappropriate_state;
    endtask : execute_cmd11

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd12;
      // STOP_TRANSMISSION
      if (card_st == DATA_ST ||
          card_st == RCV_ST) begin
        respond_with_r1;
        if (card_st == RCV_ST)
          last_rsp.wr_dat_blklen = 0;

        data_transf = null;
        cancel_ongoing_read_blocks;
        cancel_ongoing_write_blocks;
      end
      else
        inappropriate_state;
    endtask : execute_cmd12

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd13;
      // SEND_STATUS
      if (uhsii_based || last_cmd.arg[31:16] == rca_reg) begin
        if (card_st == STBY_ST || card_st == TRAN_ST || card_st == DATA_ST ||
            card_st == RCV_ST  || card_st == PRG_ST  || card_st == DIS_ST)
          respond_with_r1;
        else
          inappropriate_state;
      end
      else
      `DISPLAY_LOGGER_WARNING($sformatf("CMD13 ignored arg=%h rca_reg=%h", last_cmd.arg[31:16], rca_reg))
    endtask : execute_cmd13

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd14;
      // reserved (CMD14)
      not_implemented_cmd;
    endtask : execute_cmd14

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd15;
      // GO_INACTIVE_STATE
      /*if (uhsii_based) // not supported in UHS-II ??
        illegal_cmd = `TRUE;
      else*/
      if (last_cmd.arg[31:16] == rca_reg) begin
        if (card_st == STBY_ST || card_st == TRAN_ST || card_st == DATA_ST ||
            card_st == RCV_ST  || card_st == PRG_ST  || card_st == DIS_ST) begin
          change_state(INA_ST);
          pass_bus_info_to_xtor;//??
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd15

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd16;
      // SET_BLOCKLEN
      if (card_st == TRAN_ST) begin
        respond_with_r1;
        block_length = last_cmd.arg;
        `DISPLAY_LOGGER_NOTE($sformatf("block length set to %d", block_length))
        if (!correct_block_length)
          csr_reg[BLOCK_LEN_ERROR_CSR_BIT] = `TRUE;
      end
      else
        inappropriate_state;
    endtask : execute_cmd16

    // --------------------------------------------------------------------- //

    protected virtual task execute_cmd17;
      // READ_SINGLE_BLOCK
      block_count = 1;
      execute_cmd18;
      last_rsp.index = 6'd17;
      block_count = 0;
      if ((last_cmd.arg == TRAINING_PATTERN_ADDR_4B  ||
           last_cmd.arg == TRAINING_PATTERN_ADDR_8B) &&
          this.data_transf != null)
        this.data_transf.set_training;
    endtask : execute_cmd17

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd18;
      // READ_MULTIPLE_BLOCK
      if (card_st == TRAN_ST) begin
        respond_with_r1;

        if (csr_reg[BLOCK_LEN_ERROR_CSR_BIT] |
            csr_reg[ADDRESS_ERROR_CSR_BIT])
          `DISPLAY_LOGGER_WARNING("block length or address error, READ transfer not started")
        else begin
          data_transf = new(last_cmd.arg, card_config.card_cap, data_mem,
                            block_length, block_count, READ_OPER,
                            csd_reg[READ_BLK_MISALIGN_CSD_BIT], uhsii_based, this.datagen);
        `ifdef USE_LOGGERS
          data_transf.init_logging(logger, log_id, hierarchy);
        `endif // USE_LOGGERS
          `DISPLAY_LOGGER_INFO($sformatf(
              "new READ transfer defined: %s", data_transf.to_string))
          change_state(DATA_ST);
        end
      end
      else
        inappropriate_state;

        // if we do a multiple read with short blocks and bus width larger then 1,
        // card is to send the response faster and even faster in SDR104/HS200/HS400 modes:
      if (this.data_transf != null && this.last_rsp.rsp_kind == R1 &&
          this.data_transf.get_blklen < 5 && this.bus_width > L1 &&
         (this.data_transf.get_blkcnt > 1 || this.data_transf.get_blkcnt == 0) )
        last_rsp.delay_cycles = $urandom_range(
            (uses_fastest(bus_speed) ? 9 : 21)/(5-this.data_transf.get_blklen), 2);
        // ------------------------------------
    endtask : execute_cmd18

    // -------------------------------------------------------------------- //

    const static bit [7:0] tuning_block_pattern[] = '{
      8'hFF, 8'h0F, 8'hFF, 8'h00,    8'hFF, 8'hCC, 8'hC3, 8'hCC,
      8'hC3, 8'h3C, 8'hCC, 8'hFF,    8'hFE, 8'hFF, 8'hFE, 8'hEF,

      8'hFF, 8'hDF, 8'hFF, 8'hDD,    8'hFF, 8'hFB, 8'hFF, 8'hFB,
      8'hBF, 8'hFF, 8'h7F, 8'hFF,    8'h77, 8'hF7, 8'hBD, 8'hEF,

      8'hFF, 8'hF0, 8'hFF, 8'hF0,    8'h0F, 8'hFC, 8'hCC, 8'h3C,
      8'hCC, 8'h33, 8'hCC, 8'hCF,    8'hFF, 8'hEF, 8'hFF, 8'hEE,

      8'hFF, 8'hFD, 8'hFF, 8'hFD,    8'hDF, 8'hFF, 8'hBF, 8'hFF,
      8'hBB, 8'hFF, 8'hF7, 8'hFF,    8'hF7, 8'h7F, 8'h7B, 8'hDE };

    protected virtual task execute_cmd19;
      // SEND_TUNING_BLOCK
      if (uhsii_based) // not supported in UHS-II
        illegal_cmd = `TRUE;
      else if (card_st == TRAN_ST) begin
        if (volt18_switched && bus_speed == SDR104 && bus_width == L4) begin
          automatic bit timeout;
          respond_with_r1;

          inject_dat_timeout_error(timeout);
          if (timeout) return;

          last_dat = new(`FALSE, `FALSE, bus_width);
          last_dat.data = tuning_block_pattern;
          last_dat.tuning_block = `TRUE;
          set_n_ac_delay(last_dat);
          mbx_dat_rd.put(last_dat);
          change_state(DATA_ST);
        end
        else
          `DISPLAY_LOGGER_WARNING($sformatf(
              "CMD19 is illegal in current conditions: %s %s %s",
              bus_speed.name, bus_width.name,
              volt18_switched ? "" : "and voltage not switched"))
      end
      else
        inappropriate_state;
    endtask : execute_cmd19

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd20;
      // SPEED_CLASS_CONTROL
      not_implemented_cmd;
    endtask : execute_cmd20

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd21;
      // reserved (CMD21)
      not_implemented_cmd;
    endtask : execute_cmd21

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd22;
      // reserved (CMD22)
      not_implemented_cmd;
    endtask : execute_cmd22

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd23;
      // SET_BLOCK_COUNT
      if (uhsii_based); // ignored in UHS-II
      else if (card_st == TRAN_ST) begin
        respond_with_r1;
        block_count = last_cmd.arg;
      end
      else
        inappropriate_state;
    endtask : execute_cmd23

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd24;
      // WRITE_BLOCK // single
      block_count = 1;
      execute_cmd25;
      last_rsp.index = 6'd24;
      block_count = 0;
    endtask : execute_cmd24

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd25;
      // WRITE_MULTIPLE_BLOCK
      if (card_st == TRAN_ST) begin
        respond_with_r1;

        if (csr_reg[BLOCK_LEN_ERROR_CSR_BIT] |
            csr_reg[ADDRESS_ERROR_CSR_BIT]   |
           !correct_block_length)
          `DISPLAY_LOGGER_WARNING(
              "block length or address error, WRITE transfer not started")
        else begin
          data_transf = new(last_cmd.arg, card_config.card_cap, data_mem,
                            block_length, block_count, WRITE_OPER,
                            csd_reg[WRITE_BLK_MISALIGN_CSD_BIT], uhsii_based, this.datagen
                            );
        `ifdef USE_LOGGERS
          data_transf.init_logging(logger, log_id, hierarchy);
        `endif // USE_LOGGERS
          last_rsp.wr_dat_blklen = data_transf.get_blklen;
          `DISPLAY_LOGGER_INFO($sformatf(
              "new WRITE transfer defined: %s", data_transf.to_string))
          change_state(RCV_ST);
        end
      end
      else
        inappropriate_state;
    endtask : execute_cmd25

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd26;
      // reserved for manufacturer (CMD26)
      not_implemented_cmd;
    endtask : execute_cmd26

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd27;
      // PROGRAM_CSD
      not_implemented_cmd;
    endtask : execute_cmd27

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd28;
      // SET_WRITE_PROT
      // XXX not in SDHC and SDXC
      not_implemented_cmd;
    endtask : execute_cmd28

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd29;
      // CLR_WRITE_PROT
      // XXX not in SDHC and SDXC
      not_implemented_cmd;
    endtask : execute_cmd29

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd30;
      // SEND_WRITE_PROT
      // XXX not in SDHC and SDXC
      not_implemented_cmd;
    endtask : execute_cmd30

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd31;
      // reserved (CMD31)
      not_implemented_cmd;
    endtask : execute_cmd31

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd32;
      // ERASE_WR_BLK_START
      if (card_st == TRAN_ST) begin
        if (data_transf != null) begin
          csr_reg[ERASE_SEQ_ERROR_CSR_BIT] = `TRUE;
          if (data_transf.erase_start)
            data_transf = null;
          `DISPLAY_LOGGER_WARNING("unexpected erase command")
        end
        else begin
          data_transf = new(last_cmd.arg, card_config.card_cap, data_mem,
                            block_length, block_count, ERASE_OPER, `FALSE, uhsii_based);
          data_transf.erase_start = `TRUE;
        end

        respond_with_r1;
      end
      else
        inappropriate_state;
    endtask : execute_cmd32

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd33;
      // ERASE_WR_BLK_END
      if (card_st == TRAN_ST) begin
        if (data_transf == null || !data_transf.erase_start ||
                                    data_transf.erase_end) begin
          csr_reg[ERASE_SEQ_ERROR_CSR_BIT] = `TRUE;
          if (data_transf != null && data_transf.erase_start)
            data_transf = null;
          `DISPLAY_LOGGER_WARNING("unexpected erase command")
        end
        else begin
          data_transf.set_end_blk_addr(last_cmd.arg);
          data_transf.erase_end = `TRUE;
        end

        respond_with_r1;
      end
      else
        inappropriate_state;
    endtask : execute_cmd33

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd34;
      // reserved for switch function (CMD34)
      not_implemented_cmd;
    endtask : execute_cmd34

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd35;
      // reserved for switch function (CMD35)
      not_implemented_cmd;
    endtask : execute_cmd35

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd36;
      // reserved for switch function (CMD36)
      not_implemented_cmd;
    endtask : execute_cmd36

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd37;
      // reserved for switch function (CMD37)
      not_implemented_cmd;
    endtask : execute_cmd37

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd38;
      // ERASE
      if (card_st == TRAN_ST) begin
        if (data_transf == null || !data_transf.erase_end) begin
          csr_reg[ERASE_SEQ_ERROR_CSR_BIT] = `TRUE;
          if (data_transf != null && data_transf.erase_start)
            data_transf = null;
          `DISPLAY_LOGGER_WARNING("unexpected erase command")
        end
        else
          change_state(PRG_ST);

        respond_with_r1;
      end
      else
        inappropriate_state;
    endtask : execute_cmd38

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd39;
      // reserved (CMD39)
      not_implemented_cmd;
    endtask : execute_cmd39

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd40;
      // reserved for security (CMD40)
      not_implemented_cmd;
    endtask : execute_cmd40

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd41;
      // reserved (CMD41)
      not_implemented_cmd;
    endtask : execute_cmd41

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd42;
      // LOCK_UNLOCK
      not_implemented_cmd;
    endtask : execute_cmd42

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd43;
      // reserved (CMD43)
      not_implemented_cmd;
    endtask : execute_cmd43

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd44;
      // reserved (CMD44)
      not_implemented_cmd;
    endtask : execute_cmd44

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd45;
      // reserved (CMD45)
      not_implemented_cmd;
    endtask : execute_cmd45

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd46;
      // reserved (CMD46)
      not_implemented_cmd;
    endtask : execute_cmd46

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd47;
      // reserved (CMD47)
      not_implemented_cmd;
    endtask : execute_cmd47

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd48;
      // TBD (CMD48)
      not_implemented_cmd;
    endtask : execute_cmd48

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd49;
      // TBD (CMD49)
      not_implemented_cmd;
    endtask : execute_cmd49

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd50;
      // reserved for switch function (CMD50)
      not_implemented_cmd;
    endtask : execute_cmd50

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd51;
      // reserved (CMD51)
      not_implemented_cmd;
    endtask : execute_cmd51

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd52;
      // IO_RW_DIRECT
      not_implemented_cmd;
    endtask : execute_cmd52

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd53;
      // IO_RW_EXTENDED
      not_implemented_cmd;
    endtask : execute_cmd53

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd54;
      // SDIO
      not_implemented_cmd;
    endtask : execute_cmd54

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd55; // APP_CMD
      if (uhsii_based); // ignored in UHS-II
      else if (last_cmd.arg[31:16] == rca_reg ||
               last_cmd.arg[31:16] == 16'h0000) begin
        if (card_st == IDLE_ST || card_st == STBY_ST || card_st == TRAN_ST ||
            card_st == DATA_ST || card_st == RCV_ST  || card_st == PRG_ST  ||
            card_st == DIS_ST) begin
          csr_reg[APP_CMD_CSR_BIT] = `TRUE;
          respond_with_r1;
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd55

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd56;
      // GEN_CMD
      not_implemented_cmd;
    endtask : execute_cmd56

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd57;
      // reserved for switch function (CMD57)
      not_implemented_cmd;
    endtask : execute_cmd57

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd58;
      // reserved (CMD58)
      not_implemented_cmd;
    endtask : execute_cmd58

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd59;
      // reserved (CMD59)
      not_implemented_cmd;
    endtask : execute_cmd59

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd60;
      // reserved for manufacturer (CMD60)
      not_implemented_cmd;
    endtask : execute_cmd60

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd61;
      // reserved for manufacturer (CMD61)
      not_implemented_cmd;
    endtask : execute_cmd61

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd62;
      // reserved for manufacturer (CMD62)
      not_implemented_cmd;
    endtask : execute_cmd62

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd63;
      // reserved for manufacturer (CMD63)
      not_implemented_cmd;
    endtask : execute_cmd63

    // ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ //

    // ***** application commands *****

    protected virtual task execute_acmd0;
      // not mentioned in spec ?
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd0;
    endtask : execute_acmd0

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd1;
      // reserved (ACMD1)
      not_implemented_cmd;
    endtask : execute_acmd1

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd2;
      // reserved (ACMD2)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd2;
    endtask : execute_acmd2

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd3;
      // reserved (ACMD3)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd3;
    endtask : execute_acmd3

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd4;
      // reserved (ACMD4)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd4;
    endtask : execute_acmd4

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd5;
      // reserved (ACMD5)
      not_implemented_cmd;
    endtask : execute_acmd5

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd6;
      // SET_BUS_WIDTH
      if (uhsii_based) // not supported in UHS-II
        not_implemented_cmd;
      else if (card_st == TRAN_ST &&
        (last_cmd.arg[1:0] == 2'b00 ||
         last_cmd.arg[1:0] == 2'b10) ) begin
        respond_with_r1;

        ssr_reg[511:510] = last_cmd.arg[1:0];
        pass_bus_info_to_xtor;
      end
      else
        inappropriate_state;
    endtask : execute_acmd6

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd7;
      // reserved (ACMD7)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd7;
    endtask : execute_acmd7

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd8;
      // reserved (ACMD8)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd8;
    endtask : execute_acmd8

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd9;
      // reserved (ACMD9)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd9;
    endtask : execute_acmd9

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd10;
      // reserved (ACMD10)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd10;
    endtask : execute_acmd10

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd11;
      // reserved (ACMD11)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd11;
    endtask : execute_acmd11

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd12;
      // reserved (ACMD12)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd12;
    endtask : execute_acmd12

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd13;
      // SD_STATUS
      if (card_st == TRAN_ST) begin
        respond_with_r1;

        last_dat = new(`FALSE, `FALSE, bus_width);
        last_dat.data = new [64];
        for (int i = 0; i < 512; ++i)
          last_dat.data[i/8][7-i%8] = ssr_reg[511-i];
        set_n_ac_delay(last_dat);
        mbx_dat_rd.put(last_dat);
        change_state(DATA_ST);
      end
    endtask : execute_acmd13

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd14;
      // reserved for security spec (ACMD14)
      not_implemented_cmd;
    endtask : execute_acmd14

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd15;
      // reserved for security spec (ACMD15)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd15;
    endtask : execute_acmd15

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd16;
      // reserved for security spec (ACMD16)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd16;
    endtask : execute_acmd16

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd17;
      // reserved (ACMD17)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd17;
    endtask : execute_acmd17

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd18;
      // reserved for SD security app (ACMD18)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd18;
    endtask : execute_acmd18

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd19;
      // reserved (ACMD19)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd19;
    endtask : execute_acmd19

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd20;
      // reserved (ACMD20)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd20;
    endtask : execute_acmd20

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd21;
      // reserved (ACMD21)
      not_implemented_cmd;
    endtask : execute_acmd21

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd22;
      // SEND_NUM_WR_BLOCKS
      not_implemented_cmd;
    endtask : execute_acmd22

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd23;
      // SET_WR_BLK_ERASE_COUNT
      not_implemented_cmd;
    endtask : execute_acmd23

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd24;
      // reserved (ACMD24)
      not_implemented_cmd;
    endtask : execute_acmd24

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd25;
      // reserved for SD security app (ACMD25)
      not_implemented_cmd;
    endtask : execute_acmd25

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd26;
      // reserved for SD security app (ACMD26)
      not_implemented_cmd;
    endtask : execute_acmd26

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd27;
      // reserved for security spec (ACMD27)
    endtask : execute_acmd27

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd28;
      // reserved for security spec (ACMD28)
      not_implemented_cmd;
    endtask : execute_acmd28

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd29;
      // reserved (ACMD29)
      not_implemented_cmd;
    endtask : execute_acmd29

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd30;
      // reserved for security spec (ACMD30)
    endtask : execute_acmd30

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd31;
      // reserved for security spec (ACMD31)
      illegal_cmd = `TRUE;
    endtask : execute_acmd31

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd32;
      // reserved for security spec (ACMD32)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd32;
    endtask : execute_acmd32

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd33;
      // reserved for security spec (ACMD33)
      if (uhsii_based)
        not_implemented_cmd;
      else
        execute_cmd33;
    endtask : execute_acmd33

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd34;
      // reserved for security spec (ACMD34)
      not_implemented_cmd;
    endtask : execute_acmd34

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd35;
      // reserved for security spec (ACMD35)
      not_implemented_cmd;
    endtask : execute_acmd35

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd36;
      // reserved (ACMD36)
      not_implemented_cmd;
    endtask : execute_acmd36

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd37;
      // reserved (ACMD37)
      not_implemented_cmd;
    endtask : execute_acmd37

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd38;
      // reserved for SD security app (ACMD38)
    endtask : execute_acmd38

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd39;
      // reserved (ACMD39)
      not_implemented_cmd;
    endtask : execute_acmd39

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd40;
      // reserved (ACMD40)
      not_implemented_cmd;
    endtask : execute_acmd40

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd41;
      // SD_SEND_OP_COND
      bit voltage_match = `FALSE;

      if (card_st == IDLE_ST) begin
        if (last_cmd.arg[23:0] == 0); // inquiry mode
        else if (uhsii_based & !last_cmd.arg[30])
          return; // in UHSII must be CCS=1
        else if (voltage_init.try_get) begin
          // look for voltage match
          if (!uhsii_based)
            for (int i = 23; i >= 8 && !voltage_match; --i)
              voltage_match = (last_cmd.arg[i] & ocr_reg[i]);
          if (voltage_match | uhsii_based) begin
            ocr_reg[29] = this.uhsii_based; // UHS-II
            ocr_reg[30] = (last_cmd.arg[30] &&
              (card_config.card_cap == SDHC ||
               card_config.card_cap == SDXC)); // CCS
            fork : voltage_init_thread
              fork
              begin
                // launch voltage initialization
                bit [31:0] voltage_init_arg = last_cmd.arg;
                volt_init_th_obj = process::self();
                if (!uhsii_based) begin
                  wait_units = (wait_units % 355000) + 20563;
                  `DISPLAY_LOGGER_INFO($sformatf(
                      "voltage initialization started, wait_units=%0dns", wait_units))
                  #(wait_units * 1ns);
                  ocr_reg[24] = voltage_init_arg[24]; // S18A
                end

                ocr_reg[31] = !(!voltage_init_arg[30] &&
                  (card_config.card_cap == SDHC ||
                   card_config.card_cap == SDXC)); // Ready (Busy)
                volt_init_th_obj = null;
              end
              join
            join_none
            #3ns;
          end
          else begin
            `DISPLAY_LOGGER_INFO($sformatf("Voltage not matched ocr_reg=%0h", ocr_reg))
            change_state(INA_ST);
          end
        end

        last_rsp = new (R3);
        last_rsp.index = 6'b111111;
        last_rsp.contents[0] = ocr_reg;
        last_rsp.delay_cycles = 5; // use N_ID delay
        if (ocr_reg[31])
          change_state(READY_ST);
      end
      else
        inappropriate_state;
    endtask : execute_acmd41

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd42;
      // SET_CLR_CARD_DETECT
      // XXX diff in UHS-II
      not_implemented_cmd;
    endtask : execute_acmd42

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd43;
      // reserved for SD security app (ACMD43)
      not_implemented_cmd;
    endtask : execute_acmd43

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd44;
      // reserved for SD security app (ACMD44)
      not_implemented_cmd;
    endtask : execute_acmd44

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd45;
      // reserved for SD security app (ACMD45)
      not_implemented_cmd;
    endtask : execute_acmd45

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd46;
      // reserved for SD security app (ACMD46)
      not_implemented_cmd;
    endtask : execute_acmd46

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd47;
      // reserved for SD security app (ACMD47)
      not_implemented_cmd;
    endtask : execute_acmd47

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd48;
      // reserved for SD security app (ACMD48)
    endtask : execute_acmd48

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd49;
      // reserved for SD security app (ACMD49)
      not_implemented_cmd;
    endtask : execute_acmd49

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd50;
      not_implemented_cmd;
    endtask : execute_acmd50

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd51;
      // SEND_SCR
      if (card_st == TRAN_ST) begin
        automatic bit timeout;

        respond_with_r1;

        inject_dat_timeout_error(timeout);
        if (timeout) return;

        last_dat = new(`FALSE, `FALSE, bus_width);
        last_dat.data = new [8];
        for (int i = 0; i < 64; ++i)
          last_dat.data[i/8][7-i%8] = scr_reg[63-i];
        set_n_ac_delay(last_dat);
        mbx_dat_rd.put(last_dat);
        change_state(DATA_ST);
      end
      else
        inappropriate_state;
    endtask : execute_acmd51

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd52;
      // reserved for security spec (ACMD52)
      not_implemented_cmd;
    endtask : execute_acmd52

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd53;
    endtask : execute_acmd53

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd54;
      // reserved for security spec (ACMD53)
      not_implemented_cmd;
    endtask : execute_acmd54

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd55;
      // = CMD55 :: ACMD55 does not exist!
      execute_cmd55;
    endtask : execute_acmd55

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd56;
      // reserved for security spec (ACMD56)
      not_implemented_cmd;
    endtask : execute_acmd56

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd57;
      // reserved for security spec (ACMD57)
      not_implemented_cmd;
    endtask : execute_acmd57

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd58;
      // reserved for security spec (ACMD58)
      not_implemented_cmd;
    endtask : execute_acmd58

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd59;
      // reserved for security spec (ACMD59)
      not_implemented_cmd;
    endtask : execute_acmd59

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd60;
      // not mentioned in spec ?
      not_implemented_cmd;
    endtask : execute_acmd60

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd61;
      // not mentioned in spec ?
    endtask : execute_acmd61

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd62;
      // not mentioned in spec ?
    endtask : execute_acmd62

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd63;
      // not mentioned in spec ?
      not_implemented_cmd;
    endtask : execute_acmd63

    // -------------------------------------------------------------------- //

    protected function void set_n_ac_delay(sd_dat dat);
      if (uhsii_based)
        return;
      if (ENFORCE_N_AC != 0)
        dat.delay_cycles = ENFORCE_N_AC;
      else if (card_config.no_dat_delays)
        dat.delay_cycles = uses_fast(this.bus_speed) ? 8 : 2;
        // otherwise delay_cycles remains 0, then it will be randomized
    endfunction : set_n_ac_delay

    // -------------------------------------------------------------------- //

    local function void set_n_crc_delay(sd_meta crc);
      if (uhsii_based)
        return;
      if (card_config.no_dat_delays)
        crc.delay_cycles = 2;
    endfunction : set_n_crc_delay

    // -------------------------------------------------------------------- //

    local task go_optional_busy_randomized;
      if ($urandom_range(card_config.no_dat_delays ? 111 : 11))
        return;
      send_card_busy(`TRUE);
      wait_busy_randomized;
      // ensure that the transfer has not ended meanwhile
      if (data_transf != null) begin
        bit busy_timeout;
        inject_dat_timeout_error(busy_timeout);
        if (~busy_timeout)
          send_card_busy(`FALSE);
      end
    endtask : go_optional_busy_randomized

    // -------------------------------------------------------------------- //

    local task wait_busy_randomized;
      int clock_cycles =  card_config.no_dat_delays ? 2 :
                          $urandom_range(5)         ? $urandom_range(35,  2) :
                                                      $urandom_range(280, 30);
      // limit the length of busy time when clock is very slow:
      while (clock_cycles > 33 && is_card_ident_mode(this.card_st))
        clock_cycles /= $urandom_range(9, 4);
      `DISPLAY_LOGGER_NOTE($sformatf("BUSY delay: %0d cycle(s)", clock_cycles))
      #(clock_cycles * 1ns * min_clock_period_in_ns(this.bus_speed));
    endtask : wait_busy_randomized

    // -----------------------------------------------------------------------
    //                              THREADS
    // -----------------------------------------------------------------------

    // ***** DATA (read) thread ****
    local function int count_dat_blk_cycle_length;
      if (this.data_transf == null)
        return 32'h7FFFFFFF;
      else
        return 18  +  (data_transf.get_blklen * 8) /
        /* CRC ^^ */  (this.bus_width * (uses_ddr(this.bus_speed) ? 2 : 1));
    endfunction : count_dat_blk_cycle_length

    local task align_data_with_response(input int blk_index);
      if (blk_index < 3 && last_rsp != null && last_rsp.rsp_kind inside {R1, R5, NONE_RSP}) begin
        // for true SDIO transfers:
        if (data_transf.check_rsp_aligned)
          last_dat.delay_cycles = last_rsp.delay_cycles + 48 +
          (card_config.no_dat_delays ? 0 : $urandom_range(172, 0));
        // for other transfers with short blocks... (8 is to compensate also for N_RC timing!)
        else if (data_transf.get_blklen < 58 &&
                 blk_index == 1 && delay_1st_read_block &&
                 count_dat_blk_cycle_length < (last_rsp.rsp_kind == NONE_RSP ? 65 : last_rsp.delay_cycles + 48 + 8))
          last_dat.delay_cycles = $urandom_range(
          		last_rsp.rsp_kind == NONE_RSP ? 55 : (last_rsp.delay_cycles + 32 + 8),
          		last_rsp.delay_cycles + 78);
        else if (data_transf.get_blklen < 44 &&
                (2 * count_dat_blk_cycle_length) < last_rsp.delay_cycles + 48)
          last_dat.delay_cycles = $urandom_range(last_rsp.delay_cycles / 2 + 12, last_rsp.delay_cycles + 78);
      end
    endtask : align_data_with_response

    local task data_th;
      automatic int blklen_tmp;
      automatic bit timeout;
      automatic int blk_cntr = 0;

      wait (card_st == DATA_ST || card_st == BTST_ST);
      `WAIT_COND (mbx_dat_rd.num() == 0, 1.1ns)
      if (card_st == BTST_ST)
        wait (data_transf != null || card_st != BTST_ST);

      blklen_tmp = data_transf != null ? data_transf.get_blklen : 0;
      #1.1ns;
      while (data_transf != null && data_transf.has_next_blk &&
                                   !data_transf.is_misaligned &&
                                   !data_transf.out_of_range) begin
        inject_dat_timeout_error(timeout);
        if (timeout) break;

        last_dat = new(`FALSE, `FALSE, bus_width);
        last_dat.data = data_transf.read_curr_blk;
        last_dat.tuning_block = data_transf.is_training;
      `ifdef DATA_INTEGRITY_CHECK_DEBUG_READ
        for (int i = 0; i < last_dat.data.size && i < 16; ++i)
          `DISPLAY_LOGGER_NOTE($sformatf(
              "i=%0d\t to be sent: %h", i, last_dat.data[i]))
      `endif // DATA_INTEGRITY_CHECK_DEBUG_READ
        set_n_ac_delay(last_dat);
        align_data_with_response(++blk_cntr);
        mbx_dat_rd.put(last_dat);
        #4.1ns;

        `WAIT_COND (mbx_dat_rd.num() == 0, 0.1ns)

        if (data_transf != null && !data_transf.is_training)
          echo_data_read(blklen_tmp);
      end

      csr_reg[ADDRESS_ERROR_CSR_BIT] =
        data_transf != null ? data_transf.is_misaligned : `FALSE;
      csr_reg[OUT_OF_RANGE_CSR_BIT] =
        data_transf != null ? data_transf.out_of_range  : `FALSE;

      if (data_transf != null) begin
        if (!data_transf.has_next_blk &&
            !data_transf.is_misaligned &&
            !data_transf.out_of_range)
          data_transf = null; // CMD23 or CMD17 has been used
        else
          wait (data_transf == null); // wait for CMD12
      end

      if (uhsii_based && card_st == DATA_ST) begin
        #155ns;
        send_card_busy(`TRUE);
        send_card_busy(`TRUE);
        send_card_busy(`FALSE);
      end
      `WAIT_COND (mbx_dat_rd.num() == 0, 8.3ns) // for passing the bus speed info
      operation_compl;
    endtask : data_th

    // -------------------------------------------------------------------- //

    // ***** RCV (write) thread *****

    local task rcv_th;
      bit crc_err; // once occurred, rest of data is ignored
      bit timeout; // timeout error enforced

      wait (card_st == RCV_ST);
      crc_err = `FALSE;
      timeout = `FALSE;

      while (data_transf != null && data_transf.has_next_blk &&
                                   !data_transf.is_misaligned &&
                                   !data_transf.out_of_range) begin
        fork
          fork
            wait (data_transf == null);
            `WAIT_COND(mbx_dat_wr.num() > 0, 1.1ns)
          join_any
          disable fork;
        join

        if (data_transf != null) begin
          mbx_dat_wr.get(last_dat);
          if (last_dat.crc_err)
            `DISPLAY_LOGGER_WARNING("CRC error in received data")
          if (~crc_err)
            crc_err = last_dat.crc_err;
          if (~crc_err)
            data_transf.write_curr_blk(last_dat.data);
          echo_data_write(last_dat.data, last_dat.crc_err);

          inject_dat_timeout_error(timeout);
          // send CRC status token:
          if (!uhsii_based && !timeout &&
              !data_transf.is_misaligned &&
              !data_transf.out_of_range) begin
            last_meta = new;
            last_meta.token = `TRUE;
            last_meta.crc_err = last_dat.crc_err;
            set_n_crc_delay(last_meta);
            last_meta.wr_dat_end = (data_transf == null || ~data_transf.has_next_blk);
            mbx_dat_rd.put(last_meta);
          end

          // temporarily card can go busy
          if (!uhsii_based && !timeout && data_transf != null && data_transf.has_next_blk)
            go_optional_busy_randomized;
        end
      end

      csr_reg[ADDRESS_ERROR_CSR_BIT] =
        data_transf != null ? data_transf.is_misaligned : `FALSE;
      csr_reg[OUT_OF_RANGE_CSR_BIT] =
        data_transf != null ? data_transf.out_of_range  : `FALSE;

      if (data_transf != null) begin
        if (!data_transf.has_next_blk &&
            !data_transf.is_misaligned &&
            !data_transf.out_of_range)
          data_transf = null; // CMD23 or CMD24 has been used
        else
          wait (data_transf == null); // wait for CMD12
      end
      #0.1ns;
      if (card_st == RCV_ST) begin
        cancel_ongoing_write_blocks(`TRUE);
        #1ns;
        change_state(PRG_ST);
        csr_reg[12:9] = card_st[3:0];
      end
      else
        cancel_ongoing_write_blocks;
    endtask : rcv_th

    // -------------------------------------------------------------------- //

    // ***** PRG (program) thread *****

    local task prg_th;
      bit busy_timeout = `FALSE;
      wait (card_st == PRG_ST);
      send_card_busy(`TRUE);

      if (data_transf == null) begin
        // commit program
        `WAIT_COND (mbx_rsp.num() == 0, 8.3ns)
        if (uhsii_based)
          #1270ns;
        else begin
          wait_busy_randomized;
          void'(mbx_dat_wr.try_get(ignore_dat));
        end
      end
      else begin
        // commit erase
        data_transf.perform_erase;
        data_transf = null;

        if (uhsii_based)
          #8705ns;
        else
          wait_busy_randomized;
      end

      #3ns;

      if (!uhsii_based)
        inject_dat_timeout_error(busy_timeout);
      if (~busy_timeout) begin
        send_card_busy(`FALSE);
        operation_compl;
      end
      else
        wait (card_st != PRG_ST);
    endtask : prg_th

    // ==================================================================== //

    // -----------------------------------------------------------------------
    //         MISSING METHODS (for SCBD reporting, SD-Tran integration)
    // -----------------------------------------------------------------------

    function int get_curr_blklen;
      return data_transf == null ? 0 : data_transf.get_blklen;
    endfunction : get_curr_blklen

    function void set_temp_blklen(int blklen);
      if (data_transf != null) begin
        `DISPLAY_LOGGER_NOTE($sformatf("Block length changed to %0d byte(s)", blklen))
        data_transf.set_blklen(blklen); // !! data_transf.allow_misalign = `TRUE;
      end
    endfunction

    function void enumerate_executed(bit [3:0] own_node_id);
      rca_reg = {12'd0, own_node_id};
    endfunction : enumerate_executed

    function void add_event_echo(
        input mailbox #(card_echo_event_cl) event_echo);
      this.event_echo = event_echo;
    endfunction : add_event_echo

    function void init_datagen(input int               randgen_mode,
                               input int               blkcnt,
                               input int               blklen,
                               input int               seed,
                               input logic [7:0]       pattern[] = '{8'd0});
      datagen_mode_T temp = datagen_mode_T'(randgen_mode);
      `DISPLAY_LOGGER_DEBUG(1, $sformatf(
          "Init datagen mode=%s blkcnt=%0d blklen=%0d seed=%h", temp.name, blkcnt, blklen, seed))
      datagen.new_transfer(randgen_mode, blkcnt, blklen, seed, pattern);
    endfunction : init_datagen

    function void register_event_echo(
        input mailbox #(card_echo_event_cl) event_echo);
      this.event_echo = event_echo;
    endfunction : register_event_echo

    local function void put_training_pattern_into_memory_4b;
      int patt_len = tuning_block_pattern.size;
      mem_blk blk_temp = new;
      if (this.data_mem == null) return;

      blk_temp.data = new [512];
      foreach (blk_temp.data[i])
        blk_temp.data[i] = tuning_block_pattern[i % patt_len];
      this.data_mem.put_mem_blk(blk_temp, TRAINING_PATTERN_ADDR_4B);
    endfunction : put_training_pattern_into_memory_4b

    local function void put_training_pattern_into_memory_8b;
      int       patt_len              = tuning_block_pattern.size * 2;
      bit [7:0] temp_tuning_pattern[] = new [patt_len];
      mem_blk blk_temp = new;
      if (this.data_mem == null) return;

      foreach (tuning_block_pattern[i]) begin
        temp_tuning_pattern[2*i]   = {2{tuning_block_pattern[i][7:4]}};
        temp_tuning_pattern[2*i+1] = {2{tuning_block_pattern[i][3:0]}};
      end
      blk_temp.data = new [512];
      foreach (blk_temp.data[i])
        blk_temp.data[i] = temp_tuning_pattern[i % patt_len];
      this.data_mem.put_mem_blk(blk_temp, TRAINING_PATTERN_ADDR_8B);
    endfunction : put_training_pattern_into_memory_8b

  endclass : sd_card_cl
endpackage : sd_card_pkg
