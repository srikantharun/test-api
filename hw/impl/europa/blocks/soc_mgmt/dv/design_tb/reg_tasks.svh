// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// Tssks for the soc management_testbench to support register accesses and
// checking
//
//==============================================================================

localparam int unsigned REG_SIZE               = 'h10000    ;
localparam int unsigned ROT_BASE_ADDR          = aipu_addr_map_pkg::SOC_MGMT_ROT_KSE_ST_ADDR;
localparam int unsigned OTP_HOST_BASE_ADDR     = aipu_addr_map_pkg::SOC_MGMT_OTP_HOST_ST_ADDR;
localparam int unsigned AOR_HOST_BASE_ADDR     = aipu_addr_map_pkg::SOC_MGMT_ROT_AO_ST_ADDR;
localparam int unsigned TMS_CSR_BASE_ADDR      = 'h0205_0000;
localparam int unsigned CLK_GEN_CSR_BASE_ADDR  = 'h0206_0000; // REG_BASE_ADDRESS                ;
localparam int unsigned RST_GEN_CSR_BASE_ADDR  = 'h0207_0000; // CLK_GEN_CSR_BASE_ADDR + REG_SIZE;
localparam int unsigned RTC_BASE_ADDR          = 'h0208_0000; // RST_GEN_CSR_BASE_ADDR + REG_SIZE;
localparam int unsigned WTD_BASE_ADDR          = 'h0209_0000;
localparam int unsigned DEBUGGER_BASE_ADDR     = 'h020A_0000;
localparam int unsigned MBIST_BASE_ADDR        = 'h020B_0000;
localparam int unsigned TRACE_BUF_BASE_ADDR    = 'h020C_0000;
localparam int unsigned RESRVD_BASE_ADDR       = 'h020D_0000;

localparam int unsigned CLK_GEN_APB_BASE_ADDR  = 'h0500_0000 + 'h0030_0000;
localparam int unsigned RST_GEN_APB_BASE_ADDR  = 'h0500_0000 + 'h0031_0000;
localparam int unsigned PCTL_APB_BASE_ADDR     = 'h0500_0000 + 'h0032_0000;
localparam int unsigned SYSCFG_APB_NOPOP0_ADDR = 'h0500_0000 + 'h0033_0000;
localparam int unsigned SYSCFG_APB_NOPOP1_ADDR = 'h0500_0000 + 'h0034_0000;

//=============================================================================-
// write the clock switch enable
task clk_mux_enable(bit [1:0] ena);
  chip_pkg::chip_axi_lt_data_t      ena_data  ;

  ena_data      = 0;
  ena_data[1:0] = ena;

  //ena_data = shift_axi_write_data(CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_CLK_EN_OFFSET, ena_data);
  //axi_reg_write                  (CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_CLK_EN_OFFSET, ena_data , reg_resp);

endtask

//==============================================================================
// check address if lsb is set. To adapt write data from 64-32
function chip_pkg::chip_axi_lt_data_t shift_axi_write_data(chip_pkg::chip_axi_addr_t addr, chip_pkg::chip_axi_lt_data_t data);
  if (addr[2]) begin
    return (data << 32);
  end else begin
    return data;
  end
endfunction

//==============================================================================
task read_clock_status(input int sel, output [31:0] status);
  chip_pkg::chip_axi_lt_data_t      reg_read_data          ;

  case(sel)
    0 : begin
      axi_reg_read(get_reg_address("CLOCK_GEN_CSR_CLK_STATUS_0"), reg_read_data, reg_resp);
    end
    1 : begin
      axi_reg_read(get_reg_address("CLOCK_GEN_CSR_CLK_STATUS_1"), reg_read_data, reg_resp);
    end
  endcase

  $display("%m Clock Status Register: Sel: %0d Data: %0x Resp: %0x at %0d", sel, reg_read_data, reg_resp, $time);
endtask

task kse3_jtag_tdr_init();

  @(posedge tck);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_haddr = kse3_jtag_haddr_t'(0);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_hwdata = soc_mgmt_hdata_t'(0);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_hwrite = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_valid  = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_enter_jtag_access_mode = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_init_kse3_adac_itf = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_jtag_dbg = 1'b0;

endtask

//=============================================================================
task kse3_jtag_ahb_write(input kse3_jtag_haddr_t addr, input soc_mgmt_hdata_t wdata, input kse3_jtag_resp_t jtag_resp_exp);
  logic transaction_id;

  while (!i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready)
    @(posedge tck);

  transaction_id = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id;

  @(posedge tck);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_haddr = addr;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_hwdata = wdata;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_hwrite = 1'b1;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_valid  = 1'b1;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_enter_jtag_access_mode = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_init_kse3_adac_itf = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id = ~transaction_id;
  // Wait for JTAG status to be ready
  @(posedge tck);
  @(posedge i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready);
  @(posedge tck);

  kse3_jtag_check_resp(jtag_resp_exp, "kse3_jtag_ahb_write");

endtask

task kse3_jtag_ahb_read(input kse3_jtag_haddr_t addr, output soc_mgmt_hdata_t rdata, input kse3_jtag_resp_t jtag_resp_exp);
  logic transaction_id;

  while (!i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready)
    @(posedge tck);

  transaction_id = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id;

  @(posedge tck);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_haddr = addr;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_hwrite = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_valid  = 1'b1;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_enter_jtag_access_mode = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_init_kse3_adac_itf = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id = ~transaction_id;
  // Wait for JTAG status to be ready
  @(posedge tck);
  @(posedge i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready);
  @(posedge tck);
  rdata = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_ahb_hrdata;

  kse3_jtag_check_resp(jtag_resp_exp, "kse3_jtag_ahb_read");

endtask

task kse3_send_enter_jtag_access_mode(input kse3_jtag_resp_t jtag_resp_exp);
  logic transaction_id;

  while (!i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready)
    @(posedge tck);

  transaction_id = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id;

  @(posedge tck);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_enter_jtag_access_mode = 1'b1;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_init_kse3_adac_itf = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_valid  = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id = ~transaction_id;
  // Wait for JTAG status to be ready
  @(posedge tck);
  @(posedge i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready);
  @(posedge tck);

  kse3_jtag_check_resp(jtag_resp_exp, "kse3_send_enter_jtag_access_mode");

endtask

task kse3_send_init_kse3_adac_itf(input kse3_jtag_resp_t jtag_resp_exp);
  logic transaction_id;

  while (!i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready)
    @(posedge tck);

  transaction_id = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id;

  @(posedge tck);
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_init_kse3_adac_itf = 1'b1;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_ahb_valid  = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_enter_jtag_access_mode = 1'b0;
  force i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.o_transaction_id = ~transaction_id;
  // Wait for JTAG status to be ready
  @(posedge tck);
  @(posedge i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ready);
  @(posedge tck);

  kse3_jtag_check_resp(jtag_resp_exp, "kse3_send_init_kse3_adac_itf");

endtask

function kse3_jtag_get_resp(output kse3_jtag_resp_t jtag_resp);
  jtag_resp.ahb_hrdata  = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_ahb_hrdata;
  jtag_resp.ahb_error   = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_ahb_error;
  jtag_resp.kse_error   = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_kse_error;
  jtag_resp.cmd_ignored = i_soc_mgmt_p_dut.u_soc_mgmt.u_soc_mgmt_secu_enclave.u_kse_jtag_tdr.u_kse_jtag_tdr_core.i_jtag_cmd_ignored;
endfunction

function kse3_jtag_check_resp(input kse3_jtag_resp_t jtag_resp_exp, input string reporter_msg);
  kse3_jtag_resp_t jtag_resp;

  kse3_jtag_get_resp(jtag_resp);

  if (jtag_resp.ahb_error != jtag_resp_exp.ahb_error)
    `uvm_error(reporter_msg, $sformatf("jtag_resp.ahb_error, Expected = %0b Actual = %0b", jtag_resp_exp.ahb_error, jtag_resp.ahb_error))
  if (jtag_resp.kse_error != jtag_resp_exp.kse_error)
    `uvm_error(reporter_msg, $sformatf("jtag_resp.kse_error, Expected = %0b Actual = %0b", jtag_resp_exp.kse_error, jtag_resp.kse_error))
  if (jtag_resp.cmd_ignored != jtag_resp_exp.cmd_ignored)
    `uvm_error(reporter_msg, $sformatf("jtag_resp.cmd_ignored, Expected = %0b Actual = %0b", jtag_resp_exp.cmd_ignored, jtag_resp.cmd_ignored))

endfunction

//=============================================================================-
task axi_reg_write(input chip_pkg::chip_axi_addr_t addr,  chip_pkg::chip_axi_lt_data_t data, output axi_pkg::axi_resp_t resp);
  bit done;

  // address phase
  @(posedge o_periph_clk);
  i_lt_axi_s_awid     <= 0;
  i_lt_axi_s_awaddr   <= addr;
  i_lt_axi_s_awlen    <= 0;
  i_lt_axi_s_awsize   <= AXI_BYTES_4;
  i_lt_axi_s_awburst  <= AXI_BURST_FIXED;
  i_lt_axi_s_awlock   <= 2'h0;
  i_lt_axi_s_awcache  <= CACHE_BUFFERABLE;
  i_lt_axi_s_awprot   <= 3'h2;
  i_lt_axi_s_awvalid  <= 1;

  // wait for ready
  done = 0;
  do begin
    @(posedge o_periph_clk);
    if (o_lt_axi_s_awready) begin
      i_lt_axi_s_awvalid  <= 0;
      done = 1;
    end
  end while (!done);

  // data phase
  @ (posedge o_periph_clk);
  i_lt_axi_s_wstrb  <= addr[2] ? 8'hF0 : 8'h0F;
  i_lt_axi_s_wdata  <= data;
  i_lt_axi_s_wvalid <= 1;
  i_lt_axi_s_wlast  <= 1;

  done = 0;
  do begin
    @(posedge o_periph_clk);
    if (o_lt_axi_s_wready) begin
      done = 1;
    end
  end while (!done);

  @(posedge o_periph_clk);
  i_lt_axi_s_wvalid <= 0;
  i_lt_axi_s_wlast  <= 0;

  // Response
  while (!o_lt_axi_s_bvalid) @(posedge o_periph_clk);
  i_lt_axi_s_bready <= 1;
  resp               = o_lt_axi_s_bresp;

  @ (posedge o_periph_clk);
  i_lt_axi_s_bready <= 0;

endtask

task axi_32b_reg_write(input chip_pkg::chip_axi_addr_t addr, input logic [31:0] data, output axi_pkg::axi_resp_t resp);

  chip_pkg::chip_axi_lt_data_t wr_data;

  `uvm_info("axi_32b_reg_write", $sformatf("Writing address = %8x wr_data = %8x", addr, data), UVM_NONE)

  // word to doubleword alignment
  wr_data = addr[2] ? chip_pkg::chip_axi_lt_data_t'(data) << 32 : chip_pkg::chip_axi_lt_data_t'(data);
  axi_reg_write(addr, wr_data, resp);

endtask

task axi_reg_read(input chip_pkg::chip_axi_addr_t addr,  output chip_pkg::chip_axi_lt_data_t read_data, axi_pkg::axi_resp_t resp);
  bit done;

  // address phase
  @(posedge o_periph_clk);
  i_lt_axi_s_arid     <= 0;
  i_lt_axi_s_araddr   <= addr;
  i_lt_axi_s_arlen    <= 0;
  i_lt_axi_s_arsize   <= AXI_BYTES_4;
  i_lt_axi_s_arburst  <= AXI_BURST_FIXED;
  i_lt_axi_s_arlock   <= 2'h0;
  i_lt_axi_s_arcache  <= 4'h0;
  i_lt_axi_s_arprot   <= 3'h0;
  i_lt_axi_s_arvalid  <= 1;

  // wait for ready
  done = 0;
  do begin
    @(posedge o_periph_clk);
    if (o_lt_axi_s_arready) begin
      i_lt_axi_s_arvalid  <= 0;
      done                 = 1;
    end
  end while (!done);

  // data phase
  @ (posedge o_periph_clk);
  i_lt_axi_s_rready <= 1;

  done = 0;
  do begin
    @(posedge o_periph_clk);
    if (o_lt_axi_s_rvalid) begin
      // sample the data
      read_data = o_lt_axi_s_rdata;
      resp      = o_lt_axi_s_rresp;
      done      = 1;
    end
  end while (!done);
  i_lt_axi_s_rready <= 0;

  @(posedge o_periph_clk);

endtask

task axi_32b_reg_read(input chip_pkg::chip_axi_addr_t addr, output logic [31:0] data, output axi_pkg::axi_resp_t resp);

  chip_pkg::chip_axi_lt_data_t rd_data;

  axi_reg_read(addr, rd_data, resp);
  // Doubleword to word alignment
  data = addr[2] ? rd_data[63:32] : rd_data[31:0];

endtask

//=============================================================================-
function void check_reg_read(chip_pkg::chip_axi_addr_t addr, chip_pkg::chip_axi_lt_data_t act, exp);

  if (act != exp) begin
    fail_cnt++;
    `uvm_error("REG_READ", $sformatf("ERROR Reg Read Failed Addr: %0x, Act: %0x Exp: %0x", addr, act, exp))
  end
endfunction

//=============================================================================-
function void check_axi_resp(chip_pkg::chip_axi_addr_t addr, axi_resp_e act, exp);
  if (act != exp) begin
    fail_cnt++;
    `uvm_error("REG_RESP", $sformatf("ERROR Reg Response Failed Addr: %0x Act: %0s Exp: %0s", addr, act.name(), exp.name()))
  end
endfunction

//=============================================================================-
function string get_reg_name(bit [31:0] addr);
  case (addr) inside
//    [CLK_GEN_CSR_BASE_ADDR : RST_GEN_CSR_BASE_ADDR    - 1] : return get_clk_gen_reg_name(addr - CLK_GEN_CSR_BASE_ADDR);
//    [RST_GEN_CSR_BASE_ADDR : OTP_BASE_ADDR            - 1] : return "RST_GEN";
//    [OTP_BASE_ADDR         : OTP_BASE_ADDR + REG_SIZE - 1] : return "OTP";
    default                                                : return "NOREG";
  endcase
endfunction

function bit [31:0] get_reg_address(string reg_name);
  case (reg_name)
    //"CLOCK_GEN_CSR_CLK_MUX_SELECT"      : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_SELECT_OFFSET      ;
    //"CLOCK_GEN_CSR_CLK_MUX_CLK_EN"      : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_CLK_EN_OFFSET      ;
    //"CLOCK_GEN_CSR_CLK_STATUS_0"        : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_0_OFFSET        ;
    //"CLOCK_GEN_CSR_CLK_STATUS_1"        : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_1_OFFSET        ;
    //"CLOCK_GEN_CSR_CLK_FREQ_0"          : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_0_OFFSET          ;
    //"CLOCK_GEN_CSR_CLK_FREQ_1"          : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_1_OFFSET          ;
    //"CLOCK_GEN_CSR_CLK_FREQ_2"          : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_2_OFFSET          ;
    //"CLOCK_GEN_CSR_DEBUG_CLOCK_SELECT"  : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_SELECT_OFFSET  ;
    //"CLOCK_GEN_CSR_DEBUG_CLOCK_DIVIDER" : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_DIVIDER_OFFSET ;
    //"CLOCK_GEN_CSR_DEBUG_CLOCK_EN"      : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_EN_OFFSET      ;
    //"CLOCK_GEN_CSR_SLOW_CLOCK_EN"       : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SLOW_CLOCK_EN_OFFSET       ;
    //"CLOCK_GEN_CSR_SLOW_CLOCK_DIVIDER"  : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SLOW_CLOCK_DIVIDER_OFFSET  ;
    //"CLOCK_GEN_CSR_SCLK_DIV2_BYP"       : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SCLK_DIV2_BYP_OFFSET       ;
    //"CLOCK_GEN_CSR_PLL_DIV_CTRL_0"      : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_DIV_CTRL_0_OFFSET      ; //= 16'h34;
    //"CLOCK_GEN_CSR_PLL_DIV_CTRL_1"      : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_DIV_CTRL_1_OFFSET      ; //= 16'h38;
    //"CLOCK_GEN_CSR_PLL_MODE_CTRL_0"     : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_MODE_CTRL_0_OFFSET     ; //= 16'h3c;
    //"CLOCK_GEN_CSR_PLL_MODE_CTRL_1"     : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_MODE_CTRL_1_OFFSET     ; //= 16'h40;
    //"CLOCK_GEN_CSR_PLL_STATUS_0"        : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_0_OFFSET        ; //= 16'h44;
    //"CLOCK_GEN_CSR_PLL_STATUS_1"        : return  CLK_GEN_CSR_BASE_ADDR + soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_1_OFFSET        ; //= 16'h48;
    default                             : return 'hDEAD                                                                                                     ;
  endcase
endfunction

function bit [32:0] get_reg_reset(bit [31:0] addr);
  case (addr) inside
    //[CLK_GEN_CSR_BASE_ADDR : RST_GEN_CSR_BASE_ADDR    - 1] : return get_clk_gen_reg_reset(get_reg_name(addr));
    //[RST_GEN_CSR_BASE_ADDR : OTP_BASE_ADDR            - 1] : return 0;
    //[OTP_BASE_ADDR         : OTP_BASE_ADDR + REG_SIZE - 1] : return 0;
    default                                                : return 0;
  endcase
endfunction

//==============================================================================
function string get_clk_gen_reg_name(bit [15:0] addr);

  case(addr)
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_SELECT_OFFSET      : return  "CLOCK_GEN_CSR_CLK_MUX_SELECT"      ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_MUX_CLK_EN_OFFSET      : return  "CLOCK_GEN_CSR_CLK_MUX_CLK_EN"      ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_0_OFFSET        : return  "CLOCK_GEN_CSR_CLK_STATUS_0"        ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_1_OFFSET        : return  "CLOCK_GEN_CSR_CLK_STATUS_1"        ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_0_OFFSET          : return  "CLOCK_GEN_CSR_CLK_FREQ_0"          ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_1_OFFSET          : return  "CLOCK_GEN_CSR_CLK_FREQ_1"          ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_2_OFFSET          : return  "CLOCK_GEN_CSR_CLK_FREQ_2"          ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_SELECT_OFFSET  : return  "CLOCK_GEN_CSR_DEBUG_CLOCK_SELECT"  ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_DIVIDER_OFFSET : return  "CLOCK_GEN_CSR_DEBUG_CLOCK_DIVIDER" ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_DEBUG_CLOCK_EN_OFFSET      : return  "CLOCK_GEN_CSR_DEBUG_CLOCK_EN"      ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SLOW_CLOCK_EN_OFFSET       : return  "CLOCK_GEN_CSR_SLOW_CLOCK_EN"       ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SLOW_CLOCK_DIVIDER_OFFSET  : return  "CLOCK_GEN_CSR_SLOW_CLOCK_DIVIDER"  ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_SCLK_DIV2_BYP_OFFSET       : return  "CLOCK_GEN_CSR_SCLK_DIV2_BYP"       ;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_DIV_CTRL_0_OFFSET      : return  "CLOCK_GEN_CSR_PLL_DIV_CTRL_0"      ; //= 16'h34;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_DIV_CTRL_1_OFFSET      : return  "CLOCK_GEN_CSR_PLL_DIV_CTRL_1"      ; //= 16'h38;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_MODE_CTRL_0_OFFSET     : return  "CLOCK_GEN_CSR_PLL_MODE_CTRL_0"     ; //= 16'h3c;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_MODE_CTRL_1_OFFSET     : return  "CLOCK_GEN_CSR_PLL_MODE_CTRL_1"     ; //= 16'h40;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_0_OFFSET        : return  "CLOCK_GEN_CSR_PLL_STATUS_0"        ; //= 16'h44;
    //soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_PLL_STATUS_1_OFFSET        : return  "CLOCK_GEN_CSR_PLL_STATUS_1"        ; //= 16'h48;
    default                                                                           : return  "NOREG"                             ;
  endcase
endfunction

//==============================================================================
// 33 bit return value:
// [32]    = has reset
// [31:0]  = reset value (if any)
function bit [32:0] get_clk_gen_reg_reset(string reg_name);
  case(reg_name)
    //"CLOCK_GEN_CSR_CLK_STATUS_0"     : return  {1'h1, 28'h0, soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_0_RESVAL};
    //"CLOCK_GEN_CSR_CLK_STATUS_1"     : return  {1'h1, 28'h0, soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_STATUS_1_RESVAL};
    //"CLOCK_GEN_CSR_CLK_FREQ_0"       : return  {1'h1,        soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_0_RESVAL  };
    //"CLOCK_GEN_CSR_CLK_FREQ_1"       : return  {1'h1,        soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_1_RESVAL  };
    //"CLOCK_GEN_CSR_CLK_FREQ_2"       : return  {1'h1,        soc_mgmt_clock_gen_csr_reg_pkg::SOC_MGMT_CLOCK_GEN_CSR_CLK_FREQ_2_RESVAL  };
    //"CLOCK_GEN_CSR_PLL_DIV_CTRL_0"   : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    //"CLOCK_GEN_CSR_PLL_DIV_CTRL_1"   : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    //"CLOCK_GEN_CSR_PLL_MODE_CTRL_0"  : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    //"CLOCK_GEN_CSR_PLL_MODE_CTRL_1"  : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    //"CLOCK_GEN_CSR_PLL_STATUS_0"     : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    //"CLOCK_GEN_CSR_PLL_STATUS_1"     : return  {1'h1, 32'h0} ; //TODO check value. Add other registers
    default                               : return  0;
  endcase

endfunction

