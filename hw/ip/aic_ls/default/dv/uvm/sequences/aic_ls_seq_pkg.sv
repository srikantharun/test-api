
// AI CORE LS Seq package
package aic_ls_seq_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import l1_pkg::*;
  import aic_common_pkg::*;
  import aic_ls_pkg::*;
  import v_utils_pkg::*;
  import aic_ls_env_pkg::*;
  import aic_ls_csr_ral_pkg::*;
  import aic_ls_agent_pkg::*;
  import dmc_addr_gen_agent_pkg::*;
  import dmc_data_scoreboard_pkg::*;
  import token_agent_uvm_pkg::*;

  localparam CMDB_BASE_ADDR    = 'h1000;
  localparam AXI_LP_DATA_WIDTH = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  localparam AXI_STREAM_IFD0_DATA_WIDTH    = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam LS_IN_WORD_DW     = AXI_STREAM_IFD0_DATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;

`ifdef AXI_VIP

  // Transactions
  `include "cust_svt_axi_master_transaction.svh"
  `include "aic_ls_token_delay_seq_item.svh"
  `include "cust_svt_lp_axi_master_read_transaction.svh"

  // Sequences
  `include "axi_master_random_discrete_virtual_sequence.svh"
  `include "axi_slave_mem_response_sequence.svh"
  `include "axi_simple_reset_sequence.svh"
  `include "axi_null_virtual_sequence.svh"
  `include "axi_master_directed_sequence.svh"
  `include "axi_master_random_discrete_sequence.svh"
  `include "axi_master_stream_base_sequence.svh"

  // User define sequences/tasks
  `include "aic_ls_ral_access_single_wrrd_seq.svh"
  //`include "aic_ls_ral_prog_lc_regs_seq.svh"
  //`include "aic_ls_prg_lc_regs_seq.svh"
  `include "aic_ls_axi_cfg_if_write_sequence.svh"
  `include "aic_ls_axi_cfg_if_read_sequence.svh"
  `include "aic_ls_axi_master_write_sequence.svh"
  `include "aic_ls_axi_master_read_sequence.svh"
  //`include "aic_ls_cmd_sequence.svh"

  `include "aic_ls_ifd_seq.svh"
  `include "aic_ls_odr_seq.svh"
  `include "aic_ls_l1_init_seq.svh"
`endif
endpackage : aic_ls_seq_pkg


