//============================================================================
// report test status
function void test_report(int fail_cnt);
  static uvm_report_server rs = uvm_report_server::get_server();

  `uvm_info("TEST REPORT", $sformatf("*****************************"), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("*** TEST COMPLETE: %0s ****", !fail_cnt ? "PASSED" : "FAILED"), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("*****************************"), UVM_NONE)


  `uvm_info("TEST REPORT", $sformatf("UVM_ERROR :    %0d", rs.get_severity_count(UVM_ERROR)), UVM_NONE)
  `uvm_info("TEST REPORT", $sformatf("UVM_FATAL :    %0d", rs.get_severity_count(UVM_FATAL)), UVM_NONE)
endfunction

//============================================================================
// initialize all inputs
task init_inputs();
  i_cfg_apb4_s_paddr      = '0  ;
  i_cfg_apb4_s_pwdata     = '0  ;
  i_cfg_apb4_s_pwrite     = '0  ;
  i_cfg_apb4_s_psel       = '0  ;
  i_cfg_apb4_s_penable    = '0  ;
  i_cfg_apb4_s_pstrb      = '0  ;
  i_cfg_apb4_s_pprot      = '0  ;
  i_jtag_tck              = '0  ;
  i_jtag_rst_n            = '0  ;
  i_thermal_throttle      = '0  ;
  tb_pvt_clk              = '0  ;
endtask

//============================================================================
task apb_write(input tms_paddr_t addr, tms_pdata_t data);
  bit done;

  @(posedge tb_clk)
  i_cfg_apb4_s_psel     = 1    ;
  i_cfg_apb4_s_penable  = 0    ;
  i_cfg_apb4_s_paddr    = addr ;
  i_cfg_apb4_s_pwdata   = data ;
  i_cfg_apb4_s_pwrite   = 1    ;
  i_cfg_apb4_s_pstrb    = '1   ;
  i_cfg_apb4_s_pprot    = '0   ;

  @(posedge tb_clk)
  i_cfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge tb_clk)
    if (o_cfg_apb4_s_pready) begin
      done = 1;
    end
  end while (!done);
  i_cfg_apb4_s_psel     = 0    ;
  i_cfg_apb4_s_penable  = 0    ;

  @(posedge tb_clk);
  regs_wdata[addr>>2] = data;

  `uvm_info("APB_WRITE_COMPLETE", $sformatf("DEBUG340 ADDR: %0x Data: %0x,%0x", addr, data, addr>>2), UVM_HIGH)

endtask

//============================================================================
task apb_read(input tms_paddr_t addr, output tms_pdata_t data);
  bit done;

  @(posedge tb_clk)
  i_cfg_apb4_s_psel     = 1    ;
  i_cfg_apb4_s_penable  = 0    ;
  i_cfg_apb4_s_paddr    = addr ;
  i_cfg_apb4_s_pwdata   = '0   ;
  i_cfg_apb4_s_pwrite   = 0    ;
  i_cfg_apb4_s_pstrb    = '1   ;
  i_cfg_apb4_s_pprot    = '0   ;

  @(posedge tb_clk)
  i_cfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge tb_clk)
    data = o_cfg_apb4_s_prdata;
    if (o_cfg_apb4_s_pready) begin
      done = 1;
    end
  end while (!done);
  i_cfg_apb4_s_psel     = 0    ;
  i_cfg_apb4_s_penable  = 0    ;

  @(posedge tb_clk);

  `uvm_info("APB_READ_COMPLETE", $sformatf("ADDR: %0x Data: %0x", addr, data), UVM_HIGH)

endtask

//==============================================================================
task drive_pvt_clk();
  tb_pvt_clk = 0;
  fork
    begin : fork_drive_pvt_clk
      forever begin
        #(PVT_CLK_PER/2)
        tb_pvt_clk = ~tb_pvt_clk;
      end
    end
  join_none
endtask

//==============================================================================
// write ctm offset comp registers
task set_offset_comp_registers();
  // set offset compensation registers
  for (int i=tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_0_OFFSET; i<=tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_5_OFFSET; i+=4) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("SET_OFFSET_COMP_REGISTERS", "Randomize failed")
    end
    apb_write(i, regs_txn.wdata);
  end
endtask

// set thermal shutdown registers
task set_thrm_shtdwn_thresh_registers();
  for (int i=tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_0_OFFSET; i<=tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_5_OFFSET; i+=4) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("SET_SHUTDOWN_THRESH_REGISTERS", "Randomize failed")
    end
    apb_write(i, regs_txn.wdata);
  end
endtask

// set thermal warning registers
task set_thrm_warn_thresh_registers();
  for (int i=tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_0_OFFSET; i<=tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_5_OFFSET; i+=4) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("SET_WARN_THRESH_REGISTERS", "Randomize failed")
    end
    apb_write(i, regs_txn.wdata);
  end
endtask

// Set throttle on/off registers
task set_throttle_on_off_registers();
  for (int i=tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_0_OFFSET; i<=tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_5_OFFSET; i+=4) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("SET_THROTTLE_ON_REGISTERS", "Randomize failed")
    end
    apb_write(i, regs_txn.wdata);
  end
  for (int i=tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_0_OFFSET; i<=tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_5_OFFSET; i+=4) begin
    if (!regs_txn.randomize()) begin
      `uvm_error("SET_THROTTLE_ON_REGISTERS", "Randomize failed")
    end
    apb_write(i, regs_txn.wdata);
  end
endtask

// Set the select for the thermal warning output mux
task set_thermal_warning_sel_regsister();

  if (!regs_txn.randomize()) begin
    `uvm_error("THERMAL_WARNING_SEL", "Randomize failed")
  end

  apb_write(tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET, regs_txn.wdata);
endtask

//============================================================================
task reset_jtag(time delay);
  i_jtag_rst_n = 1'h0;
  #(delay);
  i_jtag_rst_n = 1'h1;
endtask

task drive_tck();

  i_jtag_tck = 0;
  fork
    begin : fork_drive_tck
      forever begin
        #(JTAG_CLK_PER/2)
        i_jtag_tck = ~i_jtag_tck;
      end
    end
  join_none

endtask

task jtag_tdr_init();

  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_paddr      = '0;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_pwrite     = 1'b0;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_pwdata     = '0;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_transaction_id = 1'b0;

endtask

//============================================================================

task jtag_read_data(input tms_paddr_t addr, output tms_pdata_t data);
  logic transaction_id;

  transaction_id = i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_transaction_id;

  @(posedge i_jtag_tck);

  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_paddr = addr;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_pwrite = 1'b0;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_transaction_id = ~transaction_id;

  @(posedge i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.i_jtag_ready);
  data = i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.i_apb_prdata;

endtask

task jtag_write_data(input tms_paddr_t addr, tms_pdata_t data);
  tms_paddr_t addr_pre;
  tms_pdata_t data_pre;
  logic transaction_id;

  // store the write data
  addr_pre = addr;
  data_pre = data;

  transaction_id = i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_transaction_id;

  @(posedge i_jtag_tck);

  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_paddr = addr;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_pwrite = 1'b1;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_apb_pwdata = data;
  force i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.o_transaction_id = ~transaction_id;

  @(posedge i_tms_dut.u_tms_jtag_to_apb.u_axe_jtag_to_apb_tdr.u_axe_jtag_to_apb_tdr_core.i_jtag_ready);

  regs_wdata[addr_pre>>2] = data_pre;
  `uvm_info("jtag_write_data", $sformatf("Addr: %0x, Data: %0x, Written: %0x", addr_pre, data_pre, regs_wdata[addr_pre>>2]), UVM_HIGH)

endtask

//==============================================================================
task read_ctm_temp_regs(input int channel);
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

    // clear predicted value
    predicted_ctm_min_temp[channel] = '0;
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

    // clear predicted value
    predicted_ctm_max_temp[channel] = '0;
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

    // clear predicted value
    predicted_ctm_cur_temp[channel] = '0;
  end
endtask

//==============================================================================
// read and check the ctm threshold status
task read_ctm_thresh_status_regs(input int channel);
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
  check_temp_threshold(channel, "REGTHRTL" , rdata[2], predicted_ctm_thermal_throttle[channel]);
endtask

//==============================================================================
function void check_reg_read_data(string reg_if_name, reg_name, tms_paddr_t addr, tms_pdata_t prdata, chkdata);
  if (prdata != chkdata) begin
    `uvm_error("CHECK_REG_READ_DATA", $sformatf("ERROR Read Data Failed. IF: %0s Reg: %0s Addr: %0x Act: %0x Exp: %0x", reg_if_name, reg_name, addr, prdata, chkdata))
    fail_cnt++;
  end
endfunction

//==============================================================================
function void check_reg_write_and_read_data(string access_id, string regname, tms_paddr_t addr, tms_pdata_t wdata, rdata);
  tms_pdata_t chkdata;

  chkdata = wdata & get_reg_mask(regname);

  if (addr <= LAST_REG_ADDR) begin
    if (rdata != chkdata) begin
      `uvm_error("CHECK_REG_WRITE_AND_READ_DATA", $sformatf("ERROR Read Data does not match Access: %0s Reg: %0s Addr: %0x Write: %0x Read: %0x Expected: %0x", access_id, regname, addr, wdata, rdata, chkdata))
      fail_cnt++;
    end
  end
endfunction

//==============================================================================
//==============================================================================
function void check_pvt_data(tms_pvt_temp_t pvt_data, reg_data);
  if (pvt_data != reg_data) begin
    `uvm_error("CHECK_PVT_DATA", $sformatf("ERROR PVT Data Mismatch Act: %0x Reg: %0x", pvt_data, reg_data))
    fail_cnt++;
  end
endfunction

//==============================================================================
function void check_temp(int channel, string id, tms_pvt_temp_t act, exp);
  if (act != exp) begin
    `uvm_error("CHECK_TEMP", $sformatf("ERROR %s Temp Chan: %2d Act: %2x Exp: %2x", id, channel, act, exp))
    fail_cnt++;
  end
endfunction

//==============================================================================
function void check_temp_threshold(int channel, string id, bit act, exp, frc_thrtl = 0);
  if (act != exp) begin
    `uvm_error("CHECK_TEMP_THRESHOLD", $sformatf("ERROR Threshold: %s Chan: %2d Act: %0x Exp: %0x FRC_THRTL: %0x", id, channel, act, exp, frc_thrtl))
    fail_cnt++;
  end
endfunction

//==============================================================================
// Checker form thermal status outputs
function void check_thermal_shutdown(bit shutdown, tms_temp_t predicted);
  bit exp;

  exp = |predicted;

  if (shutdown != exp) begin
    `uvm_error("CHECK_SHUTDOWN", $sformatf("ERROR Thermal Shutdown Act: %0x Exp: %0x Predicted: %0x", shutdown, exp, predicted))
    fail_cnt++;
  end
endfunction

function void check_thermal_warning(tms_temp_t warning, predicted);
  if (warning != predicted) begin
    `uvm_error("CHECK_THERMAL_WARNING", $sformatf("ERROR Thermal Waring Act: %3x Exp: %3x", warning, predicted))
    fail_cnt++;
  end
endfunction

function void check_thermal_throttle(tms_temp_t throttle, bit throttle_force, tms_temp_t predicted);
  if (throttle_force) begin
    if (throttle != {TW{1'h1}}) begin
      `uvm_error("CHECK_THROTTLE_FORCE", $sformatf("ERROR Thermal Throttle Force: %0x Throttle Act: %0x Exp: %0x", throttle_force, throttle, {TW{1'h1}}))
      fail_cnt++;
    end
  end else begin
    if (throttle != predicted) begin
      `uvm_error("CHECK_THERMAL_THROTTLE", $sformatf("ERROR Thermal Throttle Act: %3x Exp: %3x", throttle, predicted))
      fail_cnt++;
    end
  end
endfunction

function void check_thermal_throttle_warning(tms_temp_t act, bit throttle_force, bit sel, tms_temp_t predicted_warning, predicted_throttle);
  bit exp;

  if (!sel) begin : check_warning
    exp = |predicted_warning;
    if (act != exp) begin
      `uvm_error("CHECK_THRTL_WARN_WARNING", $sformatf("ERROR Thermal Throttle/Warn Sel: %0x Act: %0x Exp: %0x Predicted: %3x", sel, act, exp, predicted_warning))
      fail_cnt++;
    end
  end else begin : check_throttle
    if (throttle_force) begin
      if (act != 1'h1) begin
        `uvm_error("CHECK_THRTL_WARN_THROTTLE_FORCE", $sformatf("ERROR Throttle Force: %0x Sel: %0x Act: %0x Exp: %0x", throttle_force, sel, act, 1'h1))
        fail_cnt++;
      end
    end else begin
      exp = |predicted_throttle;
      if (act != exp) begin
        `uvm_error("CHECK_THRTL_WARN_THROTTLE", $sformatf("ERROR Thermal Throttle Sel %0x Act: %0x Exp: %0x", sel, act, exp))
        fail_cnt++;
      end
    end
  end
endfunction

function string get_reg_name(tms_paddr_t addr);
  case(addr)
    tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET                    : begin return "PVT_MODE_CTRL"           ; end
    tms_csr_reg_pkg::TMS_CSR_PVT_DATA_OFFSET                         : begin return "PVT_DATA"                ; end
    tms_csr_reg_pkg::TMS_CSR_PVT_CTRL_OFFSET                         : begin return "PVT_CTRL"                ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_0_OFFSET                : begin return "OFFSET_COMP_0"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_1_OFFSET                : begin return "OFFSET_COMP_1"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_2_OFFSET                : begin return "OFFSET_COMP_2"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_3_OFFSET                : begin return "OFFSET_COMP_3"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_4_OFFSET                : begin return "OFFSET_COMP_4"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_5_OFFSET                : begin return "OFFSET_COMP_5"           ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_0_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_0"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_1_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_1"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_2_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_2"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_3_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_3"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_4_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_4"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_5_OFFSET         : begin return "CTM_THRM_SHTDWN_THRESH_5"; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_0_OFFSET           : begin return "CTM_THRM_WARN_THRESH_0"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_1_OFFSET           : begin return "CTM_THRM_WARN_THRESH_1"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_2_OFFSET           : begin return "CTM_THRM_WARN_THRESH_2"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_3_OFFSET           : begin return "CTM_THRM_WARN_THRESH_3"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_4_OFFSET           : begin return "CTM_THRM_WARN_THRESH_4"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_5_OFFSET           : begin return "CTM_THRM_WARN_THRESH_5"  ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_0_OFFSET              : begin return "CTM_THRTL_ON_TEMP_0"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_1_OFFSET              : begin return "CTM_THRTL_ON_TEMP_1"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_2_OFFSET              : begin return "CTM_THRTL_ON_TEMP_2"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_3_OFFSET              : begin return "CTM_THRTL_ON_TEMP_3"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_4_OFFSET              : begin return "CTM_THRTL_ON_TEMP_4"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_5_OFFSET              : begin return "CTM_THRTL_ON_TEMP_5"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_0_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_0"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_1_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_1"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_2_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_2"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_3_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_3"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_4_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_4"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_5_OFFSET             : begin return "CTM_THRTL_OFF_TEMP_5"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET                   : begin return "CTM_MIN_TEMP_0"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET                   : begin return "CTM_MIN_TEMP_1"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET                   : begin return "CTM_MIN_TEMP_2"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET                   : begin return "CTM_MIN_TEMP_3"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET                   : begin return "CTM_MIN_TEMP_4"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET                   : begin return "CTM_MIN_TEMP_5"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET                   : begin return "CTM_MAX_TEMP_0"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET                   : begin return "CTM_MAX_TEMP_1"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET                   : begin return "CTM_MAX_TEMP_2"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET                   : begin return "CTM_MAX_TEMP_3"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET                   : begin return "CTM_MAX_TEMP_4"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET                   : begin return "CTM_MAX_TEMP_5"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET                   : begin return "CTM_CUR_TEMP_0"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET                   : begin return "CTM_CUR_TEMP_1"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET                   : begin return "CTM_CUR_TEMP_2"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET                   : begin return "CTM_CUR_TEMP_3"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET                   : begin return "CTM_CUR_TEMP_4"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET                   : begin return "CTM_CUR_TEMP_5"          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_0_OFFSET               : begin return "CTM_THERMAL_CTRL_0"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_1_OFFSET               : begin return "CTM_THERMAL_CTRL_1"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_2_OFFSET               : begin return "CTM_THERMAL_CTRL_2"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_3_OFFSET               : begin return "CTM_THERMAL_CTRL_3"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_4_OFFSET               : begin return "CTM_THERMAL_CTRL_4"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_5_OFFSET               : begin return "CTM_THERMAL_CTRL_5"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_6_OFFSET               : begin return "CTM_THERMAL_CTRL_6"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_7_OFFSET               : begin return "CTM_THERMAL_CTRL_7"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_8_OFFSET               : begin return "CTM_THERMAL_CTRL_8"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_9_OFFSET               : begin return "CTM_THERMAL_CTRL_9"      ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_10_OFFSET              : begin return "CTM_THERMAL_CTRL_10"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_11_OFFSET              : begin return "CTM_THERMAL_CTRL_11"     ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_0_OFFSET             : begin return "CTM_THERMAL_STATUS_0"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_1_OFFSET             : begin return "CTM_THERMAL_STATUS_1"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_2_OFFSET             : begin return "CTM_THERMAL_STATUS_2"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_3_OFFSET             : begin return "CTM_THERMAL_STATUS_3"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_4_OFFSET             : begin return "CTM_THERMAL_STATUS_4"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_5_OFFSET             : begin return "CTM_THERMAL_STATUS_5"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_6_OFFSET             : begin return "CTM_THERMAL_STATUS_6"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_7_OFFSET             : begin return "CTM_THERMAL_STATUS_7"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_8_OFFSET             : begin return "CTM_THERMAL_STATUS_8"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_9_OFFSET             : begin return "CTM_THERMAL_STATUS_9"    ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_10_OFFSET            : begin return "CTM_THERMAL_STATUS_10"   ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_11_OFFSET            : begin return "CTM_THERMAL_STATUS_11"   ; end
    tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET             : begin return "THERMAL_WARNING_CTRL"            ; end
    default                                                          : begin return "NO_REG"                  ; end
  endcase
endfunction

//==============================================================================
function tms_pdata_t get_reg_reset_value(tms_paddr_t addr);
  case(addr)
    tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET                    : begin return 'h30001    ; end
    tms_csr_reg_pkg::TMS_CSR_PVT_DATA_OFFSET                         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_PVT_CTRL_OFFSET                         : begin return 'h1cc21000 ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_0_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_1_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_2_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_3_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_4_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_OFFSET_COMP_5_OFFSET                : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_0_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_1_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_2_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_3_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_4_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_SHTDWN_THRESH_5_OFFSET         : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_0_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_1_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_2_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_3_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_4_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRM_WARN_THRESH_5_OFFSET           : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_0_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_1_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_2_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_3_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_4_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_ON_TEMP_5_OFFSET              : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_0_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_1_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_2_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_3_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_4_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THRTL_OFF_TEMP_5_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_0_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_1_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_2_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_3_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_4_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MIN_TEMP_5_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_0_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_1_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_2_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_3_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_4_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_MAX_TEMP_5_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_0_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_1_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_2_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_3_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_4_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_CUR_TEMP_5_OFFSET                   : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_0_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_1_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_2_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_3_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_4_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_5_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_6_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_7_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_8_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_9_OFFSET               : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_10_OFFSET              : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_CTRL_11_OFFSET              : begin return 'h7        ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_0_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_1_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_2_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_3_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_4_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_5_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_6_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_7_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_8_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_9_OFFSET             : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_10_OFFSET            : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_CTM_THERMAL_STATUS_11_OFFSET            : begin return 0          ; end
    tms_csr_reg_pkg::TMS_CSR_THERMAL_WARNING_CTRL_OFFSET             : begin return 0          ; end
    default                                                          : begin return 'hDEAD_DEAD; end
  endcase
  return 'hDEAD_DEAD;
endfunction

function tms_pdata_t get_reg_mask(string regname);
  case(regname)
    "PVT_MODE_CTRL"            : return {23{1'h1}};
    "PVT_CTRL"                 : return {30{1'h1}};
    "PVT_DATA"                 : return        0;
    "OFFSET_COMP_0"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_1"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_2"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_2"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_3"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_4"            : return {24{1'h1}}; // 2x 12bit regs
    "OFFSET_COMP_5"            : return {24{1'h1}}; // 2x 12bit regs
    "CTM_THRM_SHTDWN_THRESH_0" : return {24{1'h1}};
    "CTM_THRM_SHTDWN_THRESH_1" : return {24{1'h1}};
    "CTM_THRM_SHTDWN_THRESH_2" : return {24{1'h1}};
    "CTM_THRM_SHTDWN_THRESH_3" : return {24{1'h1}};
    "CTM_THRM_SHTDWN_THRESH_4" : return {24{1'h1}};
    "CTM_THRM_SHTDWN_THRESH_5" : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_0"   : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_1"   : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_2"   : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_3"   : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_4"   : return {24{1'h1}};
    "CTM_THRM_WARN_THRESH_5"   : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_0"      : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_1"      : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_2"      : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_3"      : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_4"      : return {24{1'h1}};
    "CTM_THRTL_ON_TEMP_5"      : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_0"     : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_1"     : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_2"     : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_3"     : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_4"     : return {24{1'h1}};
    "CTM_THRTL_OFF_TEMP_5"     : return {24{1'h1}};
    "CTM_MIN_TEMP_0"           : return        0;
    "CTM_MIN_TEMP_1"           : return        0;
    "CTM_MIN_TEMP_2"           : return        0;
    "CTM_MIN_TEMP_3"           : return        0;
    "CTM_MIN_TEMP_4"           : return        0;
    "CTM_MIN_TEMP_5"           : return        0;
    "CTM_MAX_TEMP_0"           : return        0;
    "CTM_MAX_TEMP_1"           : return        0;
    "CTM_MAX_TEMP_2"           : return        0;
    "CTM_MAX_TEMP_3"           : return        0;
    "CTM_MAX_TEMP_4"           : return        0;
    "CTM_MAX_TEMP_5"           : return        0;
    "CTM_CUR_TEMP_0"           : return        0;
    "CTM_CUR_TEMP_1"           : return        0;
    "CTM_CUR_TEMP_2"           : return        0;
    "CTM_CUR_TEMP_3"           : return        0;
    "CTM_CUR_TEMP_4"           : return        0;
    "CTM_CUR_TEMP_5"           : return        0;
    "CTM_THERMAL_CTRL_0"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_1"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_2"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_3"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_4"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_5"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_6"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_7"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_8"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_9"       : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_10"      : return  {3{1'h1}};
    "CTM_THERMAL_CTRL_11"      : return  {3{1'h1}};
    "CTM_THERMAL_STATUS_0"     : return        0;
    "CTM_THERMAL_STATUS_1"     : return        0;
    "CTM_THERMAL_STATUS_2"     : return        0;
    "CTM_THERMAL_STATUS_3"     : return        0;
    "CTM_THERMAL_STATUS_4"     : return        0;
    "CTM_THERMAL_STATUS_5"     : return        0;
    "CTM_THERMAL_STATUS_6"     : return        0;
    "CTM_THERMAL_STATUS_7"     : return        0;
    "CTM_THERMAL_STATUS_8"     : return        0;
    "CTM_THERMAL_STATUS_9"     : return        0;
    "CTM_THERMAL_STATUS_10"    : return        0;
    "CTM_THERMAL_STATUS_11"    : return        0;
    "THERMAL_WARNING_CTRL"     : return  {1{1'h1}};




    default                    : return '1;
  endcase

  return 'hDEAD_DEAD;
endfunction
