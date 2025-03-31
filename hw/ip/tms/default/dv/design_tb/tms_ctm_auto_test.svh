// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_tests
// CTM auto test. HW drives pvt conversion by default.
// No register interventions except reading the CTM status
// and threshold configuration

task ctm_auto_test();
  tms_paddr_t addr;
  
  fork
    begin : fork_ctm_auto_test
      pvt_driver_model();
    end
  join_none

  // program ctm registers
  `uvm_info("CTM_AUTO_TEST", "STARTING_CTM_AUTO_TEST", UVM_NONE)
  
  set_offset_comp_registers        ();
  set_thrm_shtdwn_thresh_registers ();
  set_thrm_warn_thresh_registers   ();
  set_throttle_on_off_registers    ();
  set_thermal_warning_sel_regsister();

  // delay for auto measure
  #100ms;

  for (int i=0; i<NB_TEMP_SENSE; i++) begin
    // read and check the ctm temperature registers
    read_ctm_temp_regs_auto(i);
  end

  for (int i=0; i<NB_TEMP_SENSE; i++) begin
    // read and check the threshold status registers
    read_ctm_thresh_status_regs_auto(i);
  end

  // clear ctm to stop fsm
  clear_ctm_mode();
  #55us;
endtask

//==============================================================================
task clear_ctm_mode();
  tms_pdata_t data       ;

  data     = 0;
  data[22] = 1;
  apb_write(tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET, data);
endtask

//==============================================================================
task read_ctm_temp_regs_auto(input int channel);
  tms_pdata_t rdata;

  // min temp
  for (int i=0; i<1; i++) begin
    case(channel)
       0,  1 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[0] = rdata;
        end
        
        // these are share registers. 
        // Get read data from upper reg when it is selected
        rdata = channel[0] ? regs_min[0] >> TW : rdata;
      end
       2,  3 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[1] = rdata;
        end
        
        rdata = channel[0] ? regs_min[1] >> TW : rdata;
      end
       4,  5 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[2] = rdata;
        end
        
        rdata = channel[0] ? regs_min[2] >> TW : rdata;
      end
       6,  7 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[3] = rdata;
        end
        
        rdata = channel[0] ? regs_min[3] >> TW : rdata;
      end
       8,  9 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[4] = rdata;
        end
        
        rdata = channel[0] ? regs_min[4] >> TW : rdata;
      end
      10, 11 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET, rdata);

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_min[5] = rdata;
        end
        
        rdata = channel[0] ? regs_min[5] >> TW : rdata;
      end
    endcase
    check_temp(channel, "MINREG", rdata, predicted_ctm_min_temp[channel]); 
  end

  // max temp
  for (int i=0; i<1; i++) begin
    case(channel)
       0,  1 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[0] = rdata;
        end
        
        rdata = channel[0] ? regs_max[0] >> TW : rdata;
      end
       2,  3 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[1] = rdata;
        end

        rdata = channel[0] ? regs_max[1] >> TW : rdata;
      end
       4,  5 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[2] = rdata;
        end

        rdata = channel[0] ? regs_max[2] >> TW : rdata;
      end
       6,  7 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[3] = rdata;
        end

        rdata = channel[0] ? regs_max[3] >> TW : rdata;
      end
       8,  9 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[4] = rdata;
        end

        rdata = channel[0] ? regs_max[4] >> TW : rdata;
      end
      10, 11 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_max[5] = rdata;
        end

        rdata = channel[0] ? regs_max[5] >> TW : rdata;
      end
    endcase
    check_temp(channel, "MAXREG", rdata, predicted_ctm_max_temp[channel]); 
  end

  // cur temp
  // rewgister are clear and read.
  // Read twice and check value:
  // loop0: read data matches predicted value
  // loop1: read data = 0. Clear on read works ok.
  // clear predicted value after first read. 
  for (int i=0; i<1; i++) begin
    case(channel)
       0,  1 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[0] = rdata;
        end

        rdata = channel[0] ? regs_cur[0] >> TW : rdata;
      end
       2,  3 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[1] = rdata;
        end

        rdata = channel[0] ? regs_cur[1] >> TW : rdata;
      end
       4,  5 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[2] = rdata;
        end

        rdata = channel[0] ? regs_cur[2] >> TW : rdata;
      end
       6,  7 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[3] = rdata;
        end

        rdata = channel[0] ? regs_cur[3] >> TW : rdata;
      end
       8,  9 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[4] = rdata;
        end

        rdata = channel[0] ? regs_cur[4] >> TW : rdata;
      end
      10, 11 : begin 
        apb_read(tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET, rdata); 

        // store the data to support checking with clear on read
        if (!channel[0]) begin
          regs_cur[5] = rdata;
        end

        rdata = channel[0] ? regs_cur[5] >> TW : rdata;
      end
    endcase
    check_temp(channel, "CURREG", rdata, predicted_ctm_cur_temp[channel]); 
  end
endtask

//==============================================================================
// read and check the ctm threshold status
task read_ctm_thresh_status_regs_auto(input int channel);
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


