// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Tasks for ddr west clock gen testbench

task init_inputs();
  i_ref_clk                = 0 ;
  i_rst_n                  = 1 ;
  i_syscfg_apb4_s_paddr    = 0 ;
  i_syscfg_apb4_s_pwdata   = 0 ;
  i_syscfg_apb4_s_pwrite   = 0 ;
  i_syscfg_apb4_s_psel     = 0 ;
  i_syscfg_apb4_s_penable  = 0 ;
  i_syscfg_apb4_s_pstrb    = 0 ;
  i_syscfg_apb4_s_pprot    = 0 ;
  ijtag_tck                = 0 ;
  ijtag_reset              = 1 ;
  ijtag_sel                = 0 ;
  ijtag_ue                 = 0 ;
  ijtag_se                 = 0 ;
  ijtag_ce                 = 0 ;
  ijtag_si                 = 0 ;
  test_clk                 = 0 ;
  test_mode                = 0 ;
  edt_update               = 0 ;
  scan_en                  = 0 ;
  scan_in                  = 0 ;
  bisr_clk                 = 0 ;
  bisr_reset               = 0 ;
  bisr_shift_en            = 0 ;
  bisr_si                  = 0 ;
endtask

//==============================================================================
// drive the clock
task drv_ref_clk();
  i_ref_clk = 0;
  fork
    forever begin
      #10ns
      i_ref_clk = ~i_ref_clk;
    end
  join_none
endtask

//==============================================================================
//set reset input
task do_reset();
  #4ns
  i_rst_n = 0;

  repeat(5) @ (posedge i_ref_clk);
  i_rst_n = 1;
endtask

//==============================================================================
function void test_report(int unsigned fail_cnt);
  `uvm_info("REPORT", "=============================", UVM_NONE)

  if (fail_cnt) begin
    `uvm_info("REPORT", "TEST FAILED", UVM_NONE)
  end else begin
    `uvm_info("REPORT", "TEST PASSED", UVM_NONE)
  end

  `uvm_info("REPORT", "=============================", UVM_NONE)
endfunction

//============================================================================
task apb_write(input chip_syscfg_addr_t addr, chip_apb_syscfg_data_t data);
  bit done;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_psel     = 1    ;
  i_syscfg_apb4_s_penable  = 0    ;
  i_syscfg_apb4_s_paddr    = addr ;
  i_syscfg_apb4_s_pwdata   = data ;
  i_syscfg_apb4_s_pwrite   = 1    ;
  i_syscfg_apb4_s_pstrb    = '1   ;
  i_syscfg_apb4_s_pprot    = '0   ;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge i_ref_clk)
    if (o_syscfg_apb4_s_pready) begin
      done = 1;
    end
  end while (!done);
  i_syscfg_apb4_s_psel     = 0    ;
  i_syscfg_apb4_s_penable  = 0    ;

  @(posedge i_ref_clk);

  `uvm_info("APB_WRITE_COMPLETE", $sformatf("APB Write ADDR: %0x Data: %0x", addr, data), UVM_HIGH)

endtask

//============================================================================
task apb_read(input chip_syscfg_addr_t addr, output chip_apb_syscfg_data_t data);
  bit done;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_psel     = 1    ;
  i_syscfg_apb4_s_penable  = 0    ;
  i_syscfg_apb4_s_paddr    = addr ;
  i_syscfg_apb4_s_pwdata   = '0   ;
  i_syscfg_apb4_s_pwrite   = 0    ;
  i_syscfg_apb4_s_pstrb    = '1   ;
  i_syscfg_apb4_s_pprot    = '0   ;

  @(posedge i_ref_clk)
  i_syscfg_apb4_s_penable  = 1    ;

  done = 0;
  do begin
    @(posedge i_ref_clk)
    data = o_syscfg_apb4_s_prdata;
    if (o_syscfg_apb4_s_pready) begin
      done = 1;
    end
  end while (!done);
  i_syscfg_apb4_s_psel     = 0    ;
  i_syscfg_apb4_s_penable  = 0    ;

  @(posedge i_ref_clk);

  `uvm_info("APB_READ_COMPLETE", $sformatf("APB Read ADDR: %0x Data: %0x", addr, data), UVM_HIGH)

endtask

//==============================================================================
// enable pll and set clock mux
// Set pll to 800MHz for DDR
// For:
// pll fvco = (m*Fin) / p MUst be bertween 1600 - 3200
// Pll fout = (m*Fin) /(p *2^s)
//
task ddr_clk_setup();
  pll_config(160, 5, 1, '1); // PLL DDR= 800Hz

  // Wait for lock
  wait_pll_lock();
  repeat(10) @ (posedge i_ref_clk);

  clk_mux_select();

  #10us;
endtask

//==============================================================================
// configure pll
task pll_config(chip_axi_lt_data_t pll_m, pll_p, pll_s, reset_data);
  chip_axi_lt_data_t      div_data  ;
  chip_axi_lt_data_t      mode_data ; // not used

  `uvm_info("PLL_CONFIG", $sformatf("PLL Settings M: %0d, P: %0d S: %0d", pll_m, pll_p, pll_s), UVM_NONE)

  div_data         = 0;
  div_data [ 5: 0] = pll_p;
  div_data [15: 6] = pll_m;
  div_data [18:16] = pll_s;

  mode_data        = 0;
  mode_data[    1] = 1; // pll reset

  `uvm_info("PLL_CONFIG", $sformatf("Write PLL Regs Addr: %0x Data: %0x", ddr_west_clock_gen_csr_reg_pkg::DDR_WEST_CLOCK_GEN_CSR_PLL_DIVIDER_OFFSET, div_data), UVM_NONE)
  apb_write(ddr_west_clock_gen_csr_reg_pkg::DDR_WEST_CLOCK_GEN_CSR_PLL_DIVIDER_OFFSET, div_data );
  apb_write(ddr_west_clock_gen_csr_reg_pkg::DDR_WEST_CLOCK_GEN_CSR_PLL_RESET_OFFSET  , mode_data);
endtask

//=============================================================================-
task wait_pll_lock();
  bit done;
  int cnt;

  cnt  = 0;
  done = 0;
  do begin
    apb_read(ddr_west_clock_gen_csr_reg_pkg::DDR_WEST_CLOCK_GEN_CSR_PLL_LOCK_OFFSET, reg_read_data);
    `uvm_info("WAIT_PLL_LOCK", $sformatf("%4d,%0x", cnt, reg_read_data), UVM_HIGH)
    cnt++;
    if (reg_read_data) begin
      done = 1;
    end
    /// timeout
    if (cnt > 50) begin
      done = 1;
      fail_cnt++;
      `uvm_error("WAIT_PLL_LOCK", "PLL Lock nock set within timeout")
    end
    #1us;
  end while(!done);
endtask 

//=============================================================================-
// write the clock switch select
task clk_mux_select();
  chip_axi_addr_t    test_addr;
  chip_axi_lt_data_t sel_data ;

  test_addr = ddr_west_clock_gen_csr_reg_pkg::DDR_WEST_CLOCK_GEN_CSR_CLK_SELECT_OFFSET;
  sel_data  = 1;

  // write the registers and check the response
  apb_write(test_addr, sel_data);

endtask

