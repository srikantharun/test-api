// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// clock_gen block testbench for the soc management IP
//
task clock_test ();
  `uvm_warning("CLOCK_TEST", "USING FORCE")
  `uvm_info("CLOCK_TEST", "Clock test Start", UVM_NONE)

  // Set the pll
  fast_clk_setup();

  repeat(10) @ (posedge i_ref_clk);

  #10us;

  // Same random reads
  begin
    int unsigned incr;
    incr = 4;
    repeat(10) begin
      syso_syscfg_apb_read(CLK_GEN_APB_BASE_ADDR+incr, reg_read_data, syscfg_slverr);
      `uvm_info("CLK_GEN_READ", $sformatf("DEBUG100 %0x,%0x",CLK_GEN_APB_BASE_ADDR+incr, reg_read_data), UVM_NONE)
      incr+=4;
    end
  end

  ->ev_debug1;
  #10us;
  //syso_syscfg_apb_read(RST_GEN_APB_BASE_ADDR, reg_read_data, syscfg_slverr);
  //check_axi_resp(RST_GEN_CSR_BASE_ADDR, axi_resp_e'(reg_resp), AXI_RESP_OKAY);
  //->ev_debug0;
  //#10us;

  // register read check
  #10us;
  do_clk_gen_reg_check();

//  #10us;
//  do_clk_freq_meas(2);

endtask
