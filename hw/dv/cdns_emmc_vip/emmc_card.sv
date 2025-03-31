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
//   eMMC card model                                                            
//   
//   File contents  : package emmc_card_pkg
//                    class   emmc_card_cl                                      
//------------------------------------------------------------------------------


// timeunit 1ns; timeprecision 100ps;

package emmc_card_pkg;
`include "card_logging.svh"
  import uvm_pkg::*;
  import tb_pkg::*;
  import components_pkg::*;
`ifdef USE_LOGGERS
  import logger_pkg::*;
  import logger_params_pkg::*;
`endif // USE_LOGGERS
  import card_echo_event_pkg::*;
  import sd_tok_pkg::*;
  import sd_card_pkg::*;

  class emmc_card_cl extends sd_card_cl;
    // additional members for eMMC support
    local bit [7:0]     ext_csd_reg[512];
    local mailbox #(bit)     mbx_lvs;
    // bus test ongoing flag
    local sd_dat        bus_test_dat;

    // enforced boot params:
    local bit           boot_part_enforce;
    local bit [31:0]    boot_part_addr;
    local int unsigned  boot_part_len;
                                      
    // ==================================================================== //

    virtual function bit [127:0] generate_cid;
      // MID:
      generate_cid[127:120]   = $urandom % 256;
      // reserved:
      generate_cid[119:114]   = 6'h00;
      // CBX:
      generate_cid[113:112]   = 2'b00;
      // OID:
      generate_cid[111:104]   = $urandom % 256;

      // PNM:
      generate_cid[103:96]    = 8'h43; // C
      generate_cid[95:88]     = 8'h45; // E
      generate_cid[87:80]     = 8'h4D; // M
      generate_cid[79:72]     = 8'h4D; // M
      generate_cid[71:64]     = 8'h43; // C
      generate_cid[63:56]     = 8'h35; // 5draft

      // PRV:
      generate_cid[55:48]     = 8'b0000_0001;
      // PSN:
      // generate_cid[55:24]     = $urandom;
      generate_cid[47:16]     = $urandom;
      // reserved:
      // generate_cid[23:20]     = 4'h0;
      // MDT:
      generate_cid[15:8]      = {4'd9, 4'hF}; // 2012 sept
      // CRC:
      generate_cid[7:1]       = calc_crc7(generate_cid[127:8], 120);
      generate_cid[0]         = `HIGH;
    endfunction : generate_cid

    // -------------------------------------------------------------------- //

    virtual function bit [127:0] generate_csd(bit v2 = `TRUE);
      // CSD_STRUCT:
      generate_csd[127:126]   = 2'b11;
      // SPEC_VERS:
      generate_csd[125:122]   = 4'h4;//?
      // reserved:
      generate_csd[121:120]   = 2'b00;
      // TAAC:
      generate_csd[119:112]   = {1'b0, 4'h3, 3'h0} /*1.3ns*/;
      // NSAC:      
      generate_csd[111:104]   = 8'h0C;//?
      // TRAN_SPEED:
      generate_csd[103:96]    = 8'h32;
      // CCC:
      generate_csd[95:84]     = 12'b010110110101;
      // READ_BL_LEN:
      generate_csd[83:80]     = 4'd9; // ?
      // READ_BL_PARTIAL:
      generate_csd[79]        = ~v2;
      // XXX_BLK_MISALIGN:
      generate_csd[WRITE_BLK_MISALIGN_CSD_BIT]  = ~v2;
      generate_csd[READ_BLK_MISALIGN_CSD_BIT]   = ~v2;
      // DSR_IMPL:
      generate_csd[76]        = `FALSE;
      // reserved:
      generate_csd[75:74]     = 2'b00;
      // C_SIZE:
      generate_csd[73:62]     = 12'h400;

      // VDD_R_CURR_MIN:
      generate_csd[61:59]     = 3'h0;
      // VDD_R_CURR_MAX:
      generate_csd[58:56]     = 3'h7;
      // VDD_W_CURR_MIN:
      generate_csd[55:53]     = 3'h0;
      // VDD_W_CURR_MAX:
      generate_csd[52:50]     = 3'h7;
      // C_SIZE_MULT:
      generate_csd[49:47]     = 3'h0;

      // ERASE_GRP_SIZE:
      generate_csd[46:42]     = 5'd0;
      // ERASE_GRP_MULT:
      generate_csd[41:37]     = 5'd0;
      // WP_GRP_SIZE:
      generate_csd[36:32]     = 5'd0;
      // WP_GRP_ENABLE:
      generate_csd[31]        = `LOW;
      // DEFAULT_ECC:
      generate_csd[30:29]     = 2'b00;

      // R2W_FACTOR:
      generate_csd[28:26]     = 3'b001;

      // WRITE_BL_LEN
      generate_csd[25:22]     = 4'h9;
      // WRITE_BL_PARTIAL:
      generate_csd[21]        = ~v2;
      // reserved:
      generate_csd[20:17]     = 4'b0000;

      // CONTENT_PROT_APP:
      generate_csd[16]        = `LOW;
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

    task generate_ext_csd_reg;
      // BOOT_INFO
      ext_csd_reg[228] = 8'b00000111; // supports: HS, DDR & alt
      // BOOT_SIZE_MULT:
      ext_csd_reg[226] = 8'hFF; // max: 32640 kB
      // ACC_SIZE:
      ext_csd_reg[225] = 8'h01;
      // HC_ERASE_GRP_SIZE:
      ext_csd_reg[224] = 8'h01;
      // DRIVER_STRENGTH:
      ext_csd_reg[197] = 8'h0F;
      // DEVICE_TYPE:
      ext_csd_reg[196] = 8'hFF;
      // CSD_STRUCTURE:
      ext_csd_reg[194] = 8'h02;
      // HS_TIMING:
      ext_csd_reg[185] = 8'h00;
      // BUS_WIDTH:
      ext_csd_reg[183] = 8'h00;
      // ERASED_MEM_CONT:
      ext_csd_reg[181] = 8'h00;
      // (boot) PARTITION_CONFIG:
      ext_csd_reg[179] = 8'o070;
      // BOOT_BUS_CONDITIONS:
      ext_csd_reg[177] = {3'b000, 2'b00, 1'b0, 2'b00};
    endtask : generate_ext_csd_reg
    
    // ==================================================================== //

    function new(input string             _name,
                 input component_cl       _parent,
                 input mailbox #(sd_cmd)  mbx_cmd,
                 input mailbox #(sd_rsp)  mbx_rsp,
                 input mailbox #(sd_dat)  mbx_dat_rd,
                 input mailbox #(sd_dat)  mbx_dat_wr,
                 input legacy_config_cl   card_config,
                 input bit                use_datagen);
      super.new(_name, _parent, mbx_cmd, mbx_rsp, mbx_dat_rd, mbx_dat_wr, mbx_lvs,
                null, null, `FALSE, use_datagen);
      
      if (card_config == null)
        this.card_config = new(EMMC_BYTE, legacy_config_cl::random_ocr_emmc());
      else
        this.card_config = card_config;
    endfunction : new

    function string get_class_name;
      return "emmc_card_cl";
    endfunction : get_class_name

    // ==================================================================== //

    protected virtual task set_register_values;
      this.cid_reg       = generate_cid;
      this.csd_reg       = generate_csd(get_ccs(this.card_config.card_cap));
      this.scr_reg       = generate_scr(this.card_config.card_cap);

      generate_ext_csd_reg;
    endtask : set_register_values

    // -------------------------------------------------------------------- //

    function void obsolete_cmd;
      `DISPLAY_LOGGER_WARNING($sformatf("%sCMD%0d is obsolete for eMMC 4.51",
         (last_cmd.app || this.go_for_acmd) ? "A" : "",
          last_cmd.index))
      illegal_cmd = `TRUE;
    endfunction : obsolete_cmd

    // -------------------------------------------------------------------- //

    function void improper_cmd;
      `DISPLAY_LOGGER_WARNING($sformatf("%sCMD%0d is not supported by eMMC 4.51",
         (last_cmd.app || this.go_for_acmd) ? "A" : "",
          last_cmd.index))
      illegal_cmd = `TRUE;
    endfunction : improper_cmd

    // -------------------------------------------------------------------- //

    protected virtual task pass_bus_info_to_xtor;
      sd_meta bus_meta = new;
      bus_meta.change_speed = `TRUE;

      case (ext_csd_reg[185][3:0])
        4'h0:    bus_meta.new_speed =                        DEFAULT_EMMC;
        4'h1:    bus_meta.new_speed = (ext_csd_reg[183][2] ? DDR_EMMC : SDR_EMMC);
        4'h2:    bus_meta.new_speed =                        HS200_EMMC;
        4'h3:    bus_meta.new_speed =                        HS400_EMMC;
        default: bus_meta.change_speed = `FALSE;
      endcase

      if (bus_meta.change_speed && bus_speed != bus_meta.new_speed) begin
        `DISPLAY_LOGGER_NOTE($sformatf(
            "Bus speed to be changed from %s to %s", bus_speed.name, bus_meta.new_speed.name))
        bus_speed = bus_meta.new_speed;
      end

      if (ext_csd_reg[183] < 8'd7 && ext_csd_reg[183] != 8'd4 && ext_csd_reg[183] != 8'd3)
        bus_meta.new_width = (ext_csd_reg[183][1:0] == 2 ? L8 :
                              ext_csd_reg[183][1:0] == 1 ? L4 :
                              ext_csd_reg[183][1:0] == 0 ? L1 : LERR);
      else
        bus_meta.new_width = LERR;

      if (bus_meta.new_width != LERR && bus_width != bus_meta.new_width) begin
        `DISPLAY_LOGGER_NOTE($sformatf(
            "Bus width to be changed from %s to %s", bus_width.name, bus_meta.new_width.name))
        bus_width = bus_meta.new_width;
      end
      else if (~bus_meta.change_speed)
        bus_meta = null;

      if (bus_meta != null) begin
        if (ext_csd_reg[185][3:0] != 4'h1 && ext_csd_reg[185][3:0] != 4'h3 && (
            ext_csd_reg[183] == 5 || ext_csd_reg[183] == 6))
          `DISPLAY_LOGGER_WARNING($sformatf(
              "DDR is not supported in speed mode: %s", bus_meta.new_speed.name))
        if (ext_csd_reg[185][3:0] inside {4'h2, 4'h3} && ext_csd_reg[183] == 8'd0)
          `DISPLAY_LOGGER_WARNING($sformatf(
              "1-bit bus width is not supported in speed mode: %s", bus_meta.new_speed.name))
        if (ext_csd_reg[185][3:0] == 8'd4 && ext_csd_reg[183] != 8'd6)
          `DISPLAY_LOGGER_WARNING($sformatf(
              "8-bit DDR bus width only is supported in speed mode: %s", bus_meta.new_speed.name))

        fork
          begin
            bus_speed_th_obj = process::self();
            #3ns;
            `WAIT_COND (mbx_rsp.num() == 0, 8.3ns)
            wait (card_st != PRG_ST);
            #1ns;
            mbx_dat_rd.put(bus_meta);
            bus_speed_th_obj = null;
          end
        join_none
      end
    endtask : pass_bus_info_to_xtor

    // -------------------------------------------------------------------- //

    protected virtual function void reset_bus_if;
      ext_csd_reg[183] = 8'h00;
      ext_csd_reg[185] = 8'h00;
      `DISPLAY_LOGGER_NOTE("Bus conditions reset")
      fork send_card_busy(`FALSE); join_none
    endfunction : reset_bus_if

    // ==================================================================== //

    protected virtual function void change_state(card_st_e new_st);
    `ifdef USE_LOGGERS
      `DISPLAY_LOGGER_MSG($sformatf(
          "eMMC card state changed from <i>%s</i> to <b>%s</b>",
          card_st.name, new_st.name))
    `else // USE_LOGGERS
      `DISPLAY_LOGGER_MSG($sformatf(
          "eMMC card state changed from %s to %s",
          card_st.name, new_st.name))      
    `endif // !USE_LOGGERS
      card_st = new_st;
      if (card_st == PREIDLE_ST) begin
        bit boot_procedure = (ext_csd_reg[179][5:3] inside {3'o1, 2'o2, 3'o7});
        change_state(boot_procedure ? PREBTST_ST : IDLE_ST);
      end
    endfunction : change_state

    // -------------------------------------------------------------------- //

    protected virtual task internal_reset(bit volt_back = `TRUE);;
      change_state(PREIDLE_ST);
      voltage_init      =  new(1);
      volt18_switched   = `FALSE;
      ocr_reg           = {8'h00, this.card_config.voltage_window};
      ssr_reg[511:510]  =  2'b00;
      rca_reg           = 16'h0001; // distinctive for eMMC

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
        `DISPLAY_LOGGER_NOTE("misc_th_obj killed")
      end
      reset_bus_if;
    endtask : internal_reset

    // -------------------------------------------------------------------- //

    virtual function void irq_st_compl();
      if (!last_cmd.app && !go_for_acmd && 
           last_cmd.index != 6'd55 && card_st == IRQ_ST)
        change_state(STBY_ST);
    endfunction : irq_st_compl

    // ==================================================================== //

    local task boot_th;
    endtask

    protected virtual task init_boot_procedure;
      if (card_st != PREBTST_ST) begin
        `DISPLAY_LOGGER_WARNING($sformatf(
            "EMMC card is %s, possibly does not support the boot procedure", card_st.name))
        return;
      end

      `DISPLAY_LOGGER_NOTE("Boot procedure has been requested.")
      data_transf = null;
      change_state(BTST_ST); 

      fork
        begin
          bit boot_start_addr;
          bit send_boot_ack = ext_csd_reg[179][6];
          misc_th_obj = process::self();
          `WAIT_COND (mbx_dat_rd.num() == 0, 0.4ns)

          if (send_boot_ack) begin
            wait_units = (wait_units % 50000) + 34703;
            #(212us + wait_units * 10ns);
            last_meta = new;
            last_meta.token = `TRUE;
            last_meta.crc_err = `FALSE;
            mbx_dat_rd.put(last_meta);
          end
          wait_units = (wait_units % 15000) + 7919;
          #(723us + wait_units * 100ns);

          // set the bus speed and width requested for boot:
          case (ext_csd_reg[177][4:3])
            2'b00: begin // SDR + backwards compatible timing
              ext_csd_reg[185][3:0] = 4'h0;
              ext_csd_reg[183][2]   = 1'b0;
            end
            2'b01: begin // SDR HS
              ext_csd_reg[185][3:0] = 4'h1;
              ext_csd_reg[183][2]   = 1'b0;
            end
            2'b10: begin // DDR HS
              ext_csd_reg[185][3:0] = 4'h1;
              ext_csd_reg[183][2]   = 1'b1;
            end
            2'b11: `DISPLAY_LOGGER_WARNING("Incorrect bus timing for boot operation")
          endcase
          case (ext_csd_reg[177][1:0]) 
            2'b11: `DISPLAY_LOGGER_WARNING("Incorrect bus timing for boot operation")
            default:
              if (ext_csd_reg[177][1:0] == 2'b00 && ext_csd_reg[177][4:3] == 2'b10)
                // min 4 DAT lines in case of DDR
                ext_csd_reg[183][1:0] = 2'b01;
              else
                // just copy settings in other cases
                ext_csd_reg[183][1:0] = ext_csd_reg[177][1:0];
          endcase
          pass_bus_info_to_xtor;

          #5ns;
          block_length = 512;
          if (boot_part_enforce) begin
            boot_start_addr = boot_part_addr;
            block_count = boot_part_len;
          end
          else begin
            boot_start_addr = 32'hFFFF0000;//temp solution
            block_count  = 128;
          end

          data_transf = new(boot_start_addr, card_config.card_cap, data_mem,
                            block_length, block_count, READ_OPER,
                            csd_reg[READ_BLK_MISALIGN_CSD_BIT], `FALSE, this.datagen);

          // wait until boot is finished or cancelled:
          wait (data_transf == null);

          if (ext_csd_reg[177][2]); // retain bus conditions
          else begin
            // reset bus conditions
            #0.5ns;
            reset_bus_if;
            pass_bus_info_to_xtor;
            #5ns;
          end
          misc_th_obj = null;
        end
      join_none
    endtask : init_boot_procedure

    //-  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -//

    protected virtual task stop_boot_procedure;
      if (card_st == BTST_ST) begin
        `DISPLAY_LOGGER_NOTE("Boot stop requested.")
        data_transf = null;
        cancel_ongoing_read_blocks;
      end
      else
        `DISPLAY_LOGGER_NOTE("Boot data exhausted.")
    endtask : stop_boot_procedure

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd0;
      if (card_st == INA_ST)
        return;
      case (last_cmd.arg)
        32'hFFFFFFFA: begin
          // BOOT_INITIATION
          init_boot_procedure;
        end
        32'hF0F0F0F0: begin
          // GO_PREIDLE_STATE
          internal_reset;
          change_state(PREIDLE_ST);
        end
        default: begin // 32'h00000000 (or any other arg for compatibility reasons)
          if (card_st == BTST_ST) // no reset, just stop booting
            stop_boot_procedure;
          else begin
            // GO_IDLE_STATE (pure old reset)
            internal_reset;
            change_state(IDLE_ST);
          end
        end
      endcase

      cancel_ongoing_read_blocks;
      cancel_ongoing_write_blocks;
      // reset state and CSD EXT
      pass_bus_info_to_xtor;
    endtask : execute_cmd0

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd1;
      // SEND_OP_COND
      bit voltage_match = `FALSE;
      
      if (card_st == PREBTST_ST)
        change_state(IDLE_ST);
      if (card_st == IDLE_ST) begin
        if (last_cmd.arg[23:15] == 0); // voltage range validation
        else if (last_cmd.arg[30:29] != 2'b10 && /*host doesn't support sector access*/
                 this.card_config.card_cap == EMMC_SECTOR /*card requires it*/)
          change_state(INA_ST);
        else if (voltage_init.try_get) begin
          // look for voltage match:
          for (int i = 23; i >= 8 && !voltage_match; --i)
            voltage_match = (last_cmd.arg[i] & ocr_reg[i]);
          if (voltage_match) begin
            fork
              begin : voltage_init_th
                volt_init_th_obj = process::self();
                wait_units = wait_units % 80000 + 17232;
                `DISPLAY_LOGGER_INFO($sformatf(
                    "voltage initialization started (eMMC), wait_units=%0dns", wait_units))
                #((wait_units - 1) * 1ns);
                ocr_reg[30] = get_ccs(this.card_config.card_cap);
                #1ns;
                ocr_reg[31] = `TRUE;
                volt_init_th_obj = null;
              end
            join_none
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
    endtask : execute_cmd1

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd3;
      // SET_RELATIVE_ADDR
      if (card_st == IDENT_ST) begin
        rca_reg = last_cmd.arg[31:16];
        `DISPLAY_LOGGER_NOTE($sformatf("%h assigned as new RCA", rca_reg))
        respond_with_r1;
        change_state(STBY_ST);
        pass_bus_info_to_xtor;
      end
      else
        inappropriate_state;
    endtask : execute_cmd3

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd5;
      // SLEEP_AWAKE
      if (last_cmd.arg[31:16] == rca_reg) begin
        bit sw = last_cmd.arg[15];
        if (card_st == (sw ? STBY_ST : SLP_ST)) begin
          respond_with_r1;
          fork
            begin
              select_th_obj = process::self();
              send_card_busy(`TRUE);
          //    wait (mbx_rsp.num() == 0);
              do
                #1ps;
              while (mbx_rsp.num() != 0);   //VCS
              #885ns;
              change_state(last_cmd.arg[15] ? SLP_ST : STBY_ST);
              send_card_busy(`FALSE);
              select_th_obj = null;
            end
          join_none
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd5

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd6;
      // SWITCH
      if (card_st == TRAN_ST) begin
        bit [7:0]    addr = last_cmd.arg[23:16],
                     val = last_cmd.arg[15:8];
        bit [1:0]    oper = last_cmd.arg[25:24];
        respond_with_r1;
        case (oper)
          2'b00: ; // command set
          2'b01: ext_csd_reg[addr] |=  val; // set bits
          2'b10: ext_csd_reg[addr] &= ~val; // clear bits
          2'b11: ext_csd_reg[addr]  =  val; // write byte
        endcase
        `DISPLAY_LOGGER_NOTE($sformatf("New value ext_csd_reg[%0d]=%h", addr, val))
        change_state(PRG_ST);

        if (oper != 2'b00 && (addr == 183 || addr == 185))
          pass_bus_info_to_xtor;
      end
      else
        inappropriate_state;
    endtask : execute_cmd6

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd7;
      // (DE)SELECT_CARD
      #0.1ns;
      `DISPLAY_LOGGER_NOTE($sformatf(
          "CMD7 arg=%h rca_reg=%h", last_cmd.arg[31:16], rca_reg))
      if (last_cmd.arg[31:16] == rca_reg) begin
        // -> select
        if (card_st == STBY_ST)
          change_state(TRAN_ST);
        else if (card_st == DIS_ST) begin
          change_state(PRG_ST);
          send_card_busy(`TRUE);
        end
        else
          inappropriate_state;
        if (!illegal_cmd)
          respond_with_r1;
      end
      else begin
        // -> deselect
        if (card_st == STBY_ST || card_st == TRAN_ST || card_st == DATA_ST)
          change_state(STBY_ST);
        else if (card_st == PRG_ST) begin
          change_state(DIS_ST);
          fork : deselect_busy_thread
            begin
              select_th_obj = process::self();
              #688ns;
              send_card_busy(`FALSE);
              select_th_obj = null;
            end
          join_none
        end
        else
          inappropriate_state;
      end
    endtask : execute_cmd7
    

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd8;
      // SEND_EXT_CSD
      if (card_st == TRAN_ST) begin
        respond_with_r1;
        last_dat = new(`FALSE, `FALSE, bus_width);
        last_dat.data = new [512];
        for (int i = 0; i < 512; ++i)
          last_dat.data[i] = ext_csd_reg[511-i];
        set_n_ac_delay(last_dat);
        mbx_dat_rd.put(last_dat);
        change_state(DATA_ST);
      end
      else
        inappropriate_state;
    endtask : execute_cmd8

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd11;
       // obsolete
      obsolete_cmd;
    endtask : execute_cmd11

    // -------------------------------------------------------------------- //

    local task do_bustest;
      bus_test_dat = null;
      last_meta = new;
      last_meta.wr_dat_end = `TRUE;
      mbx_dat_rd.put(last_meta);

      if (last_dat != null) begin
        bus_test_dat = new(`FALSE, `FALSE, last_dat.lines);
        bus_test_dat.lines = 8;
        case (last_dat.lines)
          1:
            if (last_dat.data.size > 0 && last_dat.data[0][7:6] == 2'b10)
              bus_test_dat.data = '{8'h00, 8'b00000001, 8'h00, 8'h00, 8'h00, 8'h00 };
            else
              bus_test_dat = null;
          4:
            if (last_dat.data.size > 0 && last_dat.data[0] == 8'b01011010)
              bus_test_dat.data = '{8'b00001010, 8'b00000101, 8'h00, 8'h00, 8'h00, 8'h00 };
            else
              bus_test_dat = null;
          8:
            if (last_dat.data.size > 1 && last_dat.data[0] == 8'b01010101 &&
                                          last_dat.data[1] == 8'b10101010) begin
              bus_test_dat.data = '{8'b10101010, 8'b01010101, 8'h00, 8'h00, 8'h00, 8'h00 };
            end
            else begin
              bus_test_dat = null;
            end
          default:
            bus_test_dat = null;
        endcase
      end
    endtask : do_bustest

    protected virtual task execute_cmd14;
      // BUSTEST_R
      if (card_st == BTST_ST && bus_speed != DDR_EMMC && bus_test_dat != null) begin
        respond_with_r1;
        fork
          begin
            set_n_ac_delay(last_dat);
            mbx_dat_rd.put(bus_test_dat);
            bus_test_dat = null;
            change_state(TRAN_ST);
          end
        join_none
      end
      else
        inappropriate_state;
    endtask : execute_cmd14

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd19;
      // BUSTEST_W
      if (card_st == TRAN_ST && bus_speed != DDR_EMMC) begin
        respond_with_r1;
        last_rsp.wr_dat_blklen = 2;
        fork
          begin
            change_state(BTST_ST);
            last_dat = null;
            mbx_dat_wr.get(last_dat);
            do_bustest;
          end
        join_none
      end
      else
        inappropriate_state;
    endtask : execute_cmd19

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd20;
      // obsolete
      obsolete_cmd;
    endtask : execute_cmd20

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd21;
      // SEND_TUNING_BLOCK
      if (card_st == TRAN_ST) begin
        if (bus_speed == HS200_EMMC && (bus_width == L4 || bus_width == L8)) begin
          respond_with_r1;
          last_dat = new(`FALSE, `FALSE, bus_width);
          if (bus_width == L4)
            last_dat.data = sd_card_cl::tuning_block_pattern;
          else begin // == L8
            bit [7:0] temp_tuning_pattern[] = new [tuning_block_pattern.size * 2];
            for (int i = 0; i < tuning_block_pattern.size; ++i) begin
              temp_tuning_pattern[2*i]   = {2{tuning_block_pattern[i][7:4]}};
              temp_tuning_pattern[2*i+1] = {2{tuning_block_pattern[i][3:0]}};
            end
            last_dat.data = temp_tuning_pattern;
          end
          last_dat.tuning_block = `TRUE;
          set_n_ac_delay(last_dat);
          mbx_dat_rd.put(last_dat);
          change_state(DATA_ST);
        end
        else
          `DISPLAY_LOGGER_WARNING($sformatf(
              "CMD21 is illegal in current conditions: %s %s",
              bus_speed.name, bus_width.name))
      end
      else
        inappropriate_state;
    endtask : execute_cmd21

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd23;
      // SET_BLOCK_COUNT
      if (card_st == TRAN_ST) begin
        respond_with_r1;
        block_count = last_cmd.arg[15:0];
      end
      else
        inappropriate_state;
    endtask: execute_cmd23

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd32;
      // obsolete
      obsolete_cmd;
    endtask : execute_cmd32

    // -------------------------------------------------------------------- //

    protected virtual task execute_cmd33;
      // obsolete
      obsolete_cmd;
    endtask : execute_cmd33

    // -------------------------------------------------------------------- //

    protected virtual task execute_acmd41;
      improper_cmd;
    endtask : execute_acmd41

    //////////////////////////////////////////////////////////////////////////

    // for testing purposes only:

    function void set_boot_params(input bit [1:0]      speed,
                                  input bit [1:0]      width,
                                  input bit            boot_ack,
                                  input bit            retain_speed);
      ext_csd_reg[177][4:3] = speed;
      ext_csd_reg[177][1:0] = width;
      ext_csd_reg[179][6]   = boot_ack;
      ext_csd_reg[177][2]   = retain_speed;
    endfunction : set_boot_params

    function void set_boot_params_ext(input bit           set_clear_n    = `FALSE,
                                      input bit [31:0]    boot_part_addr = 32'h00000000,
                                      input int unsigned  boot_part_len  = 32'h00000000);
      this.boot_part_enforce = set_clear_n;
      if (this.boot_part_enforce) begin
        this.boot_part_addr = boot_part_addr;
        this.boot_part_len  = boot_part_len;
      end
    endfunction : set_boot_params_ext
    
  endclass : emmc_card_cl
endpackage : emmc_card_pkg
