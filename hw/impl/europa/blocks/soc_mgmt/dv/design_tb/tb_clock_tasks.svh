// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>
//
// Testbench clock tasks
//


//==============================================================================
function void check_meas_freq(int clk_num, bit [31:0] meas_freq, exp_meas);
  bit [31:0] exp_min;
  bit [31:0] exp_max;

  if (exp_meas > 0) begin
    exp_min = exp_meas - 1;
    exp_max = exp_meas + 1;
  end else begin
    exp_min = exp_meas;
    exp_max = exp_meas + 1;
  end

  if (!(meas_freq inside {[exp_min:exp_max]})) begin
    `uvm_error("CHECK_MEAS_FREQ", $sformatf("ERROR Meas Freq. Clock: %0d Act: %0x Exp Min: %0x Max: %0x", clk_num, meas_freq, exp_min, exp_max))
    fail_cnt++;
  end
endfunction

//==============================================================================
// enable pll and set clock mux
// Use default PLL configuration, only set RESETB.
//
// PLL0: Fast clock - 1.2GHz
// PLL1: APU        - 1.2GHz
//
task fast_clk_setup();
  chip_apb_syscfg_data_t data;
  bit pslverr;
  data = 1;
  syso_syscfg_apb_write(CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_CONFIG_CTRL_0_OFFSET, data, pslverr);
  syso_syscfg_apb_write(CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_CONFIG_CTRL_1_OFFSET, data, pslverr);
  syso_syscfg_apb_write(CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_CONFIG_CTRL_2_OFFSET, data, pslverr);

  #10us;
  wait_pll_lock();

  // PLL is locked, switch clock muxes from REFCLK to PLL clocks.
  // Fast clock
  data = 0;
  data[0]  = 1'b1; // DIV_MUX_ENABLE
  data[4]  = 1'b1; // DIV_MUX_SELECT
  data[8]  = 1'b1; // PLL_MUX_ENABLE
  data[12] = 1'b0; // PLL_MUX_SELECT - PLL0
  data[16] = 1'b1; // DIVISOR
  syso_syscfg_apb_write(CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_MUX_DIV_CONFIG_0_OFFSET, data, pslverr);
  // APU clock
  data = 0;
  data[0]  = 1'b1; // DIV_MUX_ENABLE
  data[4]  = 1'b1; // DIV_MUX_SELECT
  data[8]  = 1'b1; // PLL_MUX_ENABLE
  data[12] = 1'b1; // PLL_MUX_SELECT - PLL1
  data[16] = 1'b1; // DIVISOR
  syso_syscfg_apb_write(CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_MUX_DIV_CONFIG_1_OFFSET, data, pslverr);

endtask

//=============================================================================-
task wait_pll_lock();
  bit done;
  int cnt;
  chip_apb_syscfg_data_t data_pll0;
  chip_apb_syscfg_data_t data_pll1;
  chip_apb_syscfg_data_t data_pll2;
  bit pslverr;

  cnt  = 0;
  done = 0;
  do begin
    syso_syscfg_apb_read(CLK_GEN_APB_BASE_ADDR + soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_STATUS_0_OFFSET, data_pll0, pslverr);
    syso_syscfg_apb_read(CLK_GEN_APB_BASE_ADDR + soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_STATUS_1_OFFSET, data_pll1, pslverr);
    syso_syscfg_apb_read(CLK_GEN_APB_BASE_ADDR + soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_PLL_STATUS_2_OFFSET, data_pll2, pslverr);

    cnt++;
    if (data_pll0[0] && data_pll1[0] && data_pll2[0]) begin
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
// clock gen register reset test
task do_clk_gen_reg_check();

endtask

//==============================================================================
task do_clk_freq_meas(int unsigned num_meas = 5);
  chip_pkg::chip_axi_addr_t    test_addr  ;
  chip_pkg::chip_axi_lt_data_t exp_data   ;
  bit                          done       ;
  bit [31:0]                   clk_freq[5];
  int                          ptr        ;

  // base address for clock frequency result register
  for (int i=0; i<num_meas; i++) begin
    test_addr = CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_FREQ_COUNTER_0_OFFSET;

    ptr  = 0;
    done = 0;
    do begin

      syso_syscfg_apb_read(test_addr, reg_read_data, syscfg_slverr);

      `uvm_info("CLK_FREQ_MEAS", $sformatf("Freq Chan: %2d, Addr: %0x, Rd Data: %0x, Clk Freq: %0x", i, test_addr, reg_read_data, clk_freq[ptr]), UVM_HIGH)

      if (test_addr[2]) begin
        if (ptr == 5) begin
        end else begin
          if (i) begin
            check_meas_freq(ptr, reg_read_data[63:32], clk_freq[ptr]);
          end
        end
        clk_freq[ptr] = reg_read_data[63:32];
      end else begin
        if (ptr == 5) begin
        end else begin
          if (i) begin
            check_meas_freq(ptr, reg_read_data[31:0], clk_freq[ptr]);
          end
        end
        clk_freq[ptr] = reg_read_data[31: 0];
      end
      ptr++;

      test_addr += 4;
      if (test_addr > CLK_GEN_APB_BASE_ADDR+soc_mgmt_clk_gen_csr_reg_pkg::SOC_MGMT_CLK_GEN_CSR_FREQ_COUNTER_4_OFFSET) begin
        done = 1;
      end
    end while (!done);
    #10us;
  end

  // delay for slow clock check
  #2500us;


endtask
