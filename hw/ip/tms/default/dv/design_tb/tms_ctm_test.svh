// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_tests
// CTM test
task ctm_test();
  tms_paddr_t addr;

  // program ctm registers
  `uvm_info("CTM_TEST", "STARTING_CTM_TEST", UVM_NONE)
  set_offset_comp_registers        ();
  set_thrm_shtdwn_thresh_registers ();
  set_thrm_warn_thresh_registers   ();
  set_throttle_on_off_registers    ();
  set_thermal_warning_sel_regsister();

  fork
    begin : fork_ctm_test
      pvt_driver_model();
      pvt_measure();
    end
  join_any

  //TEMP
  #1us;

endtask

//==============================================================================
task pvt_measure();
  tms_pdata_t data       ;
  tms_pdata_t rdata      ;
  bit         en_ts      ;
  bit         en_adc_ts  ;
  bit         soc_ts     ; // start ts
  bit [5:0]   bjt_sel_ts ; // channel select
  bit [3:0]   sel_ts     ; // adc select
  bit [2:0]   mux_addr_ts; // test mode
  bit [2:0]   avg_mode_ts; // average mode.
  bit         soc_ps     ; // start ps
  bit [2:0]   en_ps      ; // process sensor enable
  bit         done       ;
  bit         sw_mode    ;

  for (int k=0; k<100; k++) begin
    for (int i=0; i<NB_TEMP_SENSE; i++) begin
      #2us;
      en_ts       = 1          ;
      en_adc_ts   = 1          ;
      soc_ts      = 0          ; // start ts
      bjt_sel_ts  = i + 1      ;
      sel_ts      = 1          ;
      mux_addr_ts = 0          ;
      avg_mode_ts = 1          ;
      soc_ps      = 0          ; // start ps
      en_ps       = 0          ;
      sw_mode     = 1          ;

      // set channel enable
      data[    0] = en_ts      ;
      data[    1] = en_adc_ts  ;
      data[21: 2] = 0          ;
      data[   22] = sw_mode    ;
      data[31:23] = 0          ; // start ts

      apb_write(tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET, data);

      #(11us); // TSETUP > 1us Table5-1.

      soc_ts      = 1          ;

      data[    2] = soc_ts     ; // start ts
      data[ 8: 3] = bjt_sel_ts ;
      data[12: 9] = sel_ts     ;
      data[15:13] = mux_addr_ts;
      data[17:16] = avg_mode_ts;
      data[   18] = soc_ps     ; // start ps
      data[21:19] = en_ps      ;
      data[   22] = sw_mode    ;

      apb_write(tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET, data);

      done = 0;
      do begin
        #(1us); // TCONV 10us min : 30000us max.
        apb_read(tms_csr_reg_pkg::TMS_CSR_PVT_DATA_OFFSET, rdata);
        `uvm_info("PVT_MEASURE", $sformatf("Poll PVT Data Chan: %2d Data: %4x", i, rdata), UVM_HIGH)
        // check for EOC
        if (rdata[TW]) begin
          `uvm_info("PVT_EOC", $sformatf("EOC PVT Data Chan: %2d Data: %4x", i, rdata), UVM_HIGH)
          // check read data matches PVT data
          check_pvt_data(`PVT.OUT_12BIT_TS, rdata[TW-1:0]);
          done = 1;
        end
      end while (!done);

      #(1us);

      // Clear conversion start
      soc_ts      = 0          ;

      data[    2] = soc_ts     ; // start ts
      data[ 8: 3] = bjt_sel_ts ;
      data[12: 9] = sel_ts     ;
      data[15:13] = mux_addr_ts;
      data[17:16] = avg_mode_ts;
      data[   18] = soc_ps     ; // start ps
      data[21:19] = en_ps      ;
      data[   22] = sw_mode    ;
      apb_write(tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET, data);

      #(10us);

      // read and check the ctm temperature registers
      read_ctm_temp_regs_sw(i);

      // read and check the threshold status registers
      read_ctm_thresh_status_regs_sw(i);
    end
  end
endtask

//==============================================================================
task pvt_driver_model();
  bit done;
  bit done1;
  int tout;

  fork
    begin : fork_pvt_driver
      // initialize outputs
      // force are required for VCS simulation.
      // PVT is black box for Questa
      force `PVT.EOC_TS       = 1'h0;
      force `PVT.EOC_PS       = 1'h0;
      force `PVT.OUT_12BIT_TS =   '0;
      force `PVT.OUT_12BIT_PS =   '0;

      forever begin
        ->ev_debug0;
        @(posedge `PVT.SOC_TS);
        ->ev_debug1;

        done = 0;
        do begin
          repeat(250) @ (posedge tb_pvt_clk);
          if (!`PVT.SOC_TS) begin
            done = 1;
          end else begin
            force `PVT.OUT_12BIT_TS = $urandom();
            force `PVT.EOC_TS = 1'h1;

            // Set thermal throttle force to random
            //i_thermal_throttle = $urandom();
          end

          done1=0;
          tout=0;
          do begin
            repeat(10) @ (posedge tb_pvt_clk);
            if (tout >= 250)  begin
              done1 = 1;
            end
            if (!`PVT.SOC_TS) begin
              done1 = 1;
            end
            tout++;
          end while(!done1);
          //wait (!`PVT.SOC_TS);
          force `PVT.EOC_TS = 1'h0;

          done = 1;
        end while(!done);

        // set the throttle/warning output mux select
        set_thermal_warning_sel_regsister();
      end
    end
  join_none
endtask

//==============================================================================
task read_ctm_temp_regs_sw(input int channel);
  tms_pdata_t rdata;

  // min temp
  for (int i=0; i<2; i++) begin
    case(channel)
       0,  1 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET, rdata);

        // these are shared registers.
        // Get read data from upper reg when it is selected
        rdata = channel[0] ? rdata >> TW : rdata;
      end
       2,  3 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       4,  5 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       6,  7 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       8,  9 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
      10, 11 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
    endcase
    check_temp(channel, "MINREG", rdata, predicted_ctm_min_temp[channel]);

    // clear predicted value
    predicted_ctm_min_temp[channel] = '0;
  end

  // max temp
  for (int i=0; i<2; i++) begin
    case(channel)
       0,  1 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       2,  3 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       4,  5 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       6,  7 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       8,  9 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
      10, 11 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
    endcase
    check_temp(channel, "MAXREG", rdata, predicted_ctm_max_temp[channel]);

    // clear predicted value
    predicted_ctm_max_temp[channel] = '0;
  end

  // cur temp
  // rewgister are clear and read.
  // Read twice and check value:
  // loop0: read data matches predicted value
  // loop1: read data = 0. Clear on read works ok.
  // clear predicted value after first read.
  for (int i=0; i<2; i++) begin
    case(channel)
       0,  1 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       2,  3 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       4,  5 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       6,  7 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
       8,  9 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
      10, 11 : begin
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET, rdata);

        rdata = channel[0] ? rdata >> TW : rdata;
      end
    endcase
    check_temp(channel, "CURREG", rdata, predicted_ctm_cur_temp[channel]);

    // clear predicted value
    predicted_ctm_cur_temp[channel] = '0;
  end
endtask

//==============================================================================
// read and check the ctm threshold status
task read_ctm_thresh_status_regs_sw(input int channel);
  tms_pdata_t rdata;
  case (channel)
     0 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_0_OFFSET , rdata);
    end
     1 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_1_OFFSET , rdata);
    end
     2 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_2_OFFSET , rdata);
    end
     3 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_3_OFFSET , rdata);
    end
     4 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_4_OFFSET , rdata);
    end
     5 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_5_OFFSET , rdata);
    end
     6 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_6_OFFSET , rdata);
    end
     7 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_7_OFFSET , rdata);
    end
     8 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_8_OFFSET , rdata);
    end
     9 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_9_OFFSET , rdata);
    end
    10 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_10_OFFSET, rdata);
    end
    11 : begin
      apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_11_OFFSET, rdata);
    end
  endcase
  `uvm_info("CTM_THRESH", $sformatf("CTM Thermal Status Read Chan: %0d Act: %2x Exp: %2x", channel, rdata, {predicted_ctm_thermal_throttle[channel],predicted_ctm_thermal_warning[channel],predicted_ctm_thermal_shutdown[channel]}), UVM_HIGH)

  check_temp_threshold(channel, "REGSHTDWN", rdata[0], predicted_ctm_thermal_shutdown[channel]);
  check_temp_threshold(channel, "REGWARN"  , rdata[1], predicted_ctm_thermal_warning [channel]);
  check_temp_threshold(channel, "REGTHRTL" , rdata[2], i_thermal_throttle ? 1'h1 : predicted_ctm_thermal_throttle[channel], i_thermal_throttle);
endtask


