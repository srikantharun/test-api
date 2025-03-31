// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>
//
// tms_tests
// PS test
task ps_test();
  tms_paddr_t addr;

  // program ctm registers
  `uvm_info("PS_TEST", "STARTING PS_TEST", UVM_NONE)

  fork
    begin : fork_ctm_test
      pvt_ps_driver_model();
      pvt_ps_measure();
    end
  join_any

  //TEMP
  #1us;

endtask

//==============================================================================
// Write register to trigger conversion
task pvt_ps_measure();
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
      sw_mode     = 0          ;

      // set channel enable
      data[    0] = en_ts      ;
      data[    1] = en_adc_ts  ;
      data[21: 2] = 0          ;
      data[   22] = sw_mode    ;
      data[31:23] = 0          ; // start ts

      apb_write(tms_csr_reg_pkg::TMS_CSR_PVT_MODE_CTRL_OFFSET, data);

      #(11us); // TSETUP > 1us Table5-1.

      soc_ps      = 1          ;

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
        `uvm_info("PVT_PS_MEASURE", $sformatf("Poll PVT Data Chan: %2d Data: %4x", i, rdata), UVM_HIGH)
        // check for EOC
        if (rdata[PS_EOC_POS]) begin
          `uvm_info("PVT_EOC", $sformatf("EOC PVT Data Chan: %2d Data: %4x", i, rdata), UVM_HIGH)
          // check read data matches PVT data
          check_pvt_data(`PVT.OUT_12BIT_PS, rdata[PS_DATA_MSB-:TW]);
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
task pvt_ps_driver_model();
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
        @(posedge `PVT.SOC_PS);
        ->ev_debug1;

        done = 0;
        do begin
          repeat(250) @ (posedge tb_pvt_clk);
          if (!`PVT.SOC_PS) begin
            done = 1;
          end else begin
            force `PVT.OUT_12BIT_PS = $urandom();
            force `PVT.EOC_PS = 1'h1;
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
          force `PVT.EOC_PS = 1'h0;

          done = 1;
        end while(!done);
      end
    end
  join_none
endtask

