`ifndef GUARD_SOC_MGMT_CLKGEN_TEST_SV
`define GUARD_SOC_MGMT_CLKGEN_TEST_SV
// Extends from AI CORE soc_mgmt base test class
class soc_mgmt_clkgen_test extends soc_mgmt_base_test;

  /** UVM Component Utility macro */
  `uvm_component_utils(soc_mgmt_clkgen_test)
  
  bit [15:0] apb_address;
  bit [31:0] apb_wr_data;
  bit [31:0] apb_rd_data;
  
  int  apb_write_addr;
  int  apb_write_data;
  int loop_strt;
  int loop_len;

  apb_master_wr_sequence apb_wr_seq;
  apb_master_rd_sequence apb_rd_seq;

  // soc_mgmt user Inteface Handle
  virtual soc_mgmt_if soc_mgmt_if;

  /** Class Constructor */
  function new(string name = "soc_mgmt_clkgen_test", uvm_component parent=null);
    super.new(name,parent);
  endfunction: new

  // Build Phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info("Build phase", "Entered...", UVM_LOW)
    super.build_phase(phase);


    /** Factory override of the master transaction object */
    set_type_override_by_type (svt_axi_master_transaction::get_type(), cust_svt_axi_master_transaction::get_type());

    `uvm_info("build_phase", "Loaded cust_svt_axi_system_configuration ", UVM_LOW)

    // random selection of slave response normal or zero delay sequence
    apb_wr_seq	= apb_master_wr_sequence::type_id::create("apb_wr_seq");
    apb_rd_seq	= apb_master_rd_sequence::type_id::create("apb_rd_seq");

    // Recieve soc_mgmt user interface handle
    uvm_config_db#(virtual soc_mgmt_if)::get(
        uvm_root::get(), "uvm_test_top", "soc_mgmt_if", soc_mgmt_if);

    `uvm_info("build_phase", "Exiting...", UVM_LOW)
  endfunction: build_phase

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    `uvm_info("base_test:run_phase", "Entered...", UVM_LOW)


     soc_mgmt_if.fast_clk_check_en   = 0;
     soc_mgmt_if.apu_clk_check_en    = 0;
     soc_mgmt_if.codec_clk_check_en  = 0;
     soc_mgmt_if.emmc_clk_check_en   = 0;
     soc_mgmt_if.periph_clk_check_en = 0;
     soc_mgmt_if.pvt_clk_check_en    = 0;
     soc_mgmt_if.ddr_clk_check_en    = 0;
     
    @(posedge soc_mgmt_if.o_ao_rst_n);
    `uvm_info("SOC_MGMT_APB",$sformatf("introducing delay .. "), UVM_LOW)
    #100;
    `uvm_info("SOC_MGMT_APB",$sformatf("after delay .. "), UVM_LOW)


     /////////////////////////////////////////////////////////////////
     //////////////////////// FAST_CLK ///////////////////////////////
     ////////////////////////  1.2Ghz  ///////////////////////////////
     // Set FAST_CLK to PLL0 (no division) through MUX_DIV_CONFIG_0
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_0_OFFSET;
     apb_wr_data = 32'h0001_0111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)
     
     
     /////////////////////////////////////////////////////////////////
     //////////////////////// APU_CLK ///////////////////////////////
     ////////////////////////  1GHz ////////////////////////////////
     // Set APU_CLK to PLL1 (no division) through MUX_DIV_CONFIG_1
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_1_OFFSET;
     apb_wr_data = 32'h0001_1111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)
     
     
     /////////////////////////////////////////////////////////////////
     //////////////////////// CODEC_CLK ///////////////////////////////
     ////////////////////////  600MHz   //////////////////////////////
     // Set CODEC_CLK to PLL0 with division by 2 through MUX_DIV_CONFIG_2
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_2_OFFSET;
     apb_wr_data = 32'h0002_0111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)     
     


     /////////////////////////////////////////////////////////////////
     //////////////////////// EMMC_CLK ///////////////////////////////
     ////////////////////////  200MHz   //////////////////////////////
     // Set EMMC_CLK to PLL0 with division by 6 through MUX_DIV_CONFIG_3
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_3_OFFSET;
     apb_wr_data = 32'h0006_0111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)
     
     
     
     
     /////////////////////////////////////////////////////////////////
     //////////////////////// PERIPH_CLK ///////////////////////////////
     ////////////////////////  100MHz   //////////////////////////////
     // Set PERIPH_CLK to PLL0 with division by 12 through MUX_DIV_CONFIG_4
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_4_OFFSET;
     apb_wr_data = 32'h000C_0111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)
     
     
     /////////////////////////////////////////////////////////////////
     //////////////////////// PVT_CLK ///////////////////////////////
     ////////////////////////  4MHz   //////////////////////////////
     // Set PVT_CLK to PLL0 with division by 300 through MUX_DIV_CONFIG_5
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DIV_CONFIG_5_OFFSET;
     apb_wr_data = 32'h012C_0111;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)     
     
     
     
     /////////////////////////////////////////////////////////////////
     //////////////////////// DDR_REF_EAST_CLK ///////////////////////////////
     // Set DDR_REF_EAST_CLK to PLL DDR MUX_DDR_CONFIG
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_MUX_DDR_CONFIG_OFFSET;
     apb_wr_data = 32'h0000_0011;
    
     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)     
     
     
     
     
     // Deassert reset of PLL0
     // PLL_CONFIG_CTRL_0.RESETB_0 = 1
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_0_OFFSET;
     apb_wr_data = 1;

     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)

     
     // Deassert reset of PLL1
     // PLL_CONFIG_CTRL_1.RESETB_1 = 1
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_1_OFFSET;
     apb_wr_data = 1;

     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)

     
     // Deassert reset of PLL DDR
     // PLL_CONFIG_CTRL_2.RESETB_2 = 1
     apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_CONFIG_CTRL_2_OFFSET;
     apb_wr_data = 1;

     apb_wr_seq.randomize() with {
     cfg_addr	     == apb_address;
     cfg_data	     == apb_wr_data;
     };
     // Start the sequence on the respective sequencer
     apb_wr_seq.start(env.apb_master_env.master.sequencer);
     `uvm_info("SOC_MGMT_AXI",$sformatf("sequence ended for addr %0h",apb_address), UVM_LOW)


     // Poll PLL_STATUS_0.LOCK
     fork
      begin
       apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_0_OFFSET;
       do begin
        #400;
        apb_rd_seq.randomize() with {
        cfg_addr	     == apb_address;
        };
        // Start the sequence on the respective sequencer
        apb_rd_seq.start(env.apb_master_env.master.sequencer);
        apb_rd_data = apb_rd_seq.rd_data;
       end while (apb_rd_data[0:0] == 0);
      end
      begin
       #50000;
       `uvm_error("SOC_MGMT_AXI", "Timeout waiting for PLL0 to lock.");
      end
     join_any
     disable fork;
     
     // Poll PLL_STATUS_1.LOCK
     fork
      begin
       apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_1_OFFSET;
       do begin
        #400;
        apb_rd_seq.randomize() with {
        cfg_addr	     == apb_address;
        };
        // Start the sequence on the respective sequencer
        apb_rd_seq.start(env.apb_master_env.master.sequencer);
        apb_rd_data = apb_rd_seq.rd_data;
       end while (apb_rd_data[0:0] == 0);
      end
      begin
       #50000;
       `uvm_error("SOC_MGMT_AXI", "Timeout waiting for PLL1 to lock.");
      end
     join_any
     disable fork;
     
     // Poll PLL_STATUS_2.LOCK
     fork
      begin
       apb_address = soc_mgmt_common_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_2_OFFSET;
       do begin
        #400;
        apb_rd_seq.randomize() with {
        cfg_addr	     == apb_address;
        };
        // Start the sequence on the respective sequencer
        apb_rd_seq.start(env.apb_master_env.master.sequencer);
        apb_rd_data = apb_rd_seq.rd_data;
       end while (apb_rd_data[0:0] == 0);
      end
      begin
       #50000;
       `uvm_error("SOC_MGMT_AXI", "Timeout waiting for PLL2 to lock.");
      end
     join_any
     disable fork;
     
     
     soc_mgmt_if.fast_clk_check_en   = 1;
     soc_mgmt_if.apu_clk_check_en    = 1;
     soc_mgmt_if.codec_clk_check_en  = 1;
     soc_mgmt_if.emmc_clk_check_en   = 1;
     soc_mgmt_if.periph_clk_check_en = 1;
     soc_mgmt_if.pvt_clk_check_en    = 1;
     soc_mgmt_if.ddr_clk_check_en    = 1;

     
     // Some waits for the clock frequency checker     
     #2000;


    
    `uvm_info("base_test:run_phase", "Exiting...", UVM_LOW)
    phase.drop_objection(this);
  endtask

endclass:soc_mgmt_clkgen_test

`endif // GUARD_SOC_MGMT_CLKGEN_TEST_SV
