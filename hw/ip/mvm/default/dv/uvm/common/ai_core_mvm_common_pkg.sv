
package ai_core_mvm_common_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import mvm_pkg::*;
  import ai_core_mvm_ral_pkg::*;

  //Defines///////////////////////////
  localparam AXI_LT_ADDR_WIDTH             = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  localparam AXI_LT_DATA_WIDTH             = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  localparam AXI_STREAM_IFDW_DATA_WIDTH    = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam AXI_STREAM_IFD0_DATA_WIDTH    = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam AXI_STREAM_IFD2_DATA_WIDTH    = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;  
  localparam AXI_STREAM_IAU_DATA_WIDTH     = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH;
  localparam AXI_TRANSACTION_BURST_SIZE_8  = 0;
  localparam AXI_TRANSACTION_BURST_SIZE_16 = 1;
  localparam AXI_TRANSACTION_BURST_SIZE_32 = 2;
  localparam AXI_TRANSACTION_BURST_SIZE_64 = 3;
  localparam AXI_TRANSACTION_BURST_FIXED   = 0;
  localparam AXI_TRANSACTION_BURST_INCR    = 1;
  localparam AXI_TRANSACTION_BURST_WRAP    = 2;
  localparam AXI_OKAY_RESPONSE             = 0;
  localparam AXI_EXOKAY_RESPONSE           = 1;
  localparam AXI_SLVERR_RESPONSE           = 2;
  localparam AXI_DECERR_RESPONSE           = 3;
  localparam ROW_OFF                       = 4;
  localparam COL_OFF                       = 3;
  localparam MATRIX_LEN                    = 4;
  localparam WT_SET                        = 2;
  localparam LOOP_LEN                      = 16;
  localparam LOOP_ITER                     = 24;
`ifndef EUROPA_ADDR_MAP
  localparam MVMEXE_CSR_START_ADDR         = 28'h009_0000;
  localparam MVMPRG_CSR_START_ADDR         = 28'h00A_0000;
  localparam MVM_EXE_CMDB_START_ADDR       = 28'h009_1000;
  localparam MVM_EXE_INSTR_START_ADDR      = 28'h009_8000;
  localparam MVM_PRG_CMDB_START_ADDR       = 28'h00A_1000;
  localparam MVM_PRG_PRG_START_ADDR        = 28'h00A_8000;
  localparam MVMEXE_CSR_END_ADDR           = 28'h009_0FFF;
  localparam MVMPRG_CSR_END_ADDR           = 28'h00A_0FFF;
  localparam MVM_EXE_CMDB_END_ADDR         = 28'h009_1FFF;
  localparam MVM_EXE_INSTR_END_ADDR        = 28'h009_FFFF;
  localparam MVM_PRG_CMDB_END_ADDR         = 28'h00A_1FFF;
  localparam MVM_PRG_PRG_END_ADDR          = 28'h00A_FFFF;
`else
  localparam MVMEXE_CSR_START_ADDR         = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_CSR_ST_ADDR;
  localparam MVMPRG_CSR_START_ADDR         = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_CSR_ST_ADDR;
  localparam MVM_EXE_CMDB_START_ADDR       = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_CMD_ST_ADDR;
  localparam MVM_EXE_INSTR_START_ADDR      = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_PRG_ST_ADDR;
  localparam MVM_PRG_CMDB_START_ADDR       = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_CMD_ST_ADDR;
  localparam MVM_PRG_PRG_START_ADDR        = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_PRG_ST_ADDR;
  localparam MVMEXE_CSR_END_ADDR           = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_CSR_END_ADDR;
  localparam MVMPRG_CSR_END_ADDR           = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_CSR_END_ADDR;
  localparam MVM_EXE_CMDB_END_ADDR         = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_CMD_END_ADDR;
  localparam MVM_EXE_INSTR_END_ADDR        = aic_addr_map_pkg::AIC_LOC_M_MVM_EXE_PRG_END_ADDR;
  localparam MVM_PRG_CMDB_END_ADDR         = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_CMD_END_ADDR;
  localparam MVM_PRG_PRG_END_ADDR          = aic_addr_map_pkg::AIC_LOC_M_MVM_PRG_PRG_END_ADDR;
`endif
  localparam MVM_EXE_SWDP_CMDB_START_ADDR  = 28'h009_2000;
  localparam MVM_PRG_SWDP_CMDB_START_ADDR  = 28'h00A_2000;
  localparam MVM_EXE_SWDP_CMDB_END_ADDR    = 28'h009_7FFF;
  localparam MVM_PRG_SWDP_CMDB_END_ADDR    = 28'h00A_7FFF;
  localparam EXE_INSTR_DEPTH               = 256;
  localparam PWORD_SIZE                    = 512;
  localparam WEIGHT_SETS                   = 4;
  localparam IMC_ROWS                      = 576;
  localparam IMC_COLUMN                    = 512;
  localparam MATRIX                        = 64;
  localparam CSRDW                         = 64;

  localparam HEADER_CMD_ID_WIDTH           = 16;
  localparam HEADER_CMD_TOK_PROD_WIDTH     = 16;
  localparam HEADER_CMD_TOK_CONS_WIDTH     = 16;
  localparam HEADER_CMD_FORMAT_WIDTH       = 8;
  localparam HEADER_CMD_RSVD_WIDTH         = 8;
  localparam VERIF_MVM_NUM_TOK_AGENTS      = 2; //program and execution
  //for DFT signals
  localparam DFT_SCAN_W                    = 8;
  
  localparam CMDBLK_DEPTH                  = 16;

  parameter longint MVM_REGION_ST_ADDR[6] = {
    MVMEXE_CSR_START_ADDR, MVM_EXE_CMDB_START_ADDR, MVM_EXE_INSTR_START_ADDR,
    MVMPRG_CSR_START_ADDR, MVM_PRG_CMDB_START_ADDR, MVM_PRG_PRG_START_ADDR
  };
  
  parameter longint MVM_REGION_END_ADDR[6] = {
    MVMEXE_CSR_END_ADDR, MVM_EXE_CMDB_END_ADDR, MVM_EXE_INSTR_END_ADDR,
    MVMPRG_CSR_END_ADDR, MVM_PRG_CMDB_END_ADDR, MVM_PRG_PRG_END_ADDR
  };

  //RAL handle
  typedef ai_core_mvm_reg_block MVM_RAL;

  //Struct
  /******************************************************************************************************************************
  Op_code	0	// CMDB descriptor operation codes0=MVM_PRG_CMDB_WR_WB_OPC (MVM-DP write weights)
  A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights set to be programmed
  A_u_pw	0..7	Programming row offset
  A_t_pw	0..7	Programming column offset
  Wb_u_pw	0..7	Programming row size, a value 0 maps to 1x64(PW gran) rows, a value of 7 maps to 8x64(PW gran) rows
  Wb_t_pw	0..7	Programming column size, a value 0 maps to 1x64(PW gran) cols, a value of 7 maps to 8x64(PW gran) cols
  *******************************************************************************************************************************/
  typedef struct packed{
  bit [7:0] wb_t_pw;
  bit [7:0] wb_u_pw;
  bit [7:0] a_t_pw;
  bit [7:0] a_u_pw;
  bit [7:0] a_s;
  bit [7:0] extra;
  } mvm_prg_cmd_struct;
  /******************************************************************************************************************************
  A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights to be used for compute
  A_u_pw	0..8 	Compute row offset (input offset)
  A_t_pw	0..7	Compute column offset (output offset)
  Wb_u_pw	0..8 	Compute row size (input size) A value of 0 maps to an operation on 1 PW, a value of 7 maps to an operation on 8 PWs
  Wb_t_pw	0..7	Compute column size (output size) A value of 0 maps to an operation on 1PW, a value of 7 maps to an operation on 8PWs
  *******************************************************************************************************************************/
  typedef struct packed{
  bit [2:0] wb_t_pw;
  bit [3:0] wb_u_pw;
  bit [2:0] a_t_pw;
  bit [3:0] a_u_pw;
  bit [1:0] a_s;
  } mvm_exe_instr_struct;
  /******************************************************************************************************************************
  Op_code	0, 1	//CMDB descriptor operation codes 0=MVM_EXE_CMDB_CMP_OPC (MVM-DP compute operation), 1=MVM_EXE_CMDB_BYP_OPC (MVM-DP bypass operation)
  Qcmd_len	1..MVM_EXE_INSTR_MEM_DEPTH-1 //Length of the qcmd section that is repeated by a qcmd iteration
  Qcmd_ptr	0.. MVM_EXE_INSTR_MEM_DEPTH-1	Start pointer for the used qcmd section
  Qcmd_iter	1..2**32-1	Number of iterations to run

  *******************************************************************************************************************************/
  typedef struct packed{
  bit [7:0]  dp_ctrl;
  bit [23:0] loop_iter;
  bit [15:0] loop_len;
  bit [15:0] loop_ptr;
  } mvm_exe_cmd_struct;

  typedef struct packed{
  bit [7:0]   rsvd;
  bit [7:0]   cmd_format;
  bit [15:0]  token_cons;
  bit [15:0]  token_prod;
  bit [15:0]  id;
  } mvm_exe_cmd_header_struct;
  /************
  Field	Allowed values	Description
  Imc_prg_we	N-hot 16b	Write enable bits of all 16 individual IMC banks, can be N-hot enabled to broadcast writes (should be used in pairs of 2 active bits to write full PWs)
  Imc_prg_row	0..IMC_NB_ROWS-1 (511)	Row address for weight writing (broadcasted to all imc banks)
  Imc_prg_ws	0.. IMC_NB_WEIGHT_SETS-1 (3)	Weight set selected for weight writing
  tlast	0..1	Tlast on PRG-DP_CMD stream, should match tlast on IFDW
  ******/
  typedef struct packed{
  bit [23:0]  rsvd;
  bit [4:0]   img_prg_ctrl_rsvd;
  bit         img_prg_ctrl_tlast;
  bit [1:0]   img_prg_ctrl_ws;
  bit [15:0]  imc_prg_row;
  bit [15:0]  imc_prg_we;
  } mvm_prg_swdp_cmd_struct;

  /**************
  Field	Allowed values	Description
  Inp_gating	N-hot 16b	Input gating enable bits (pairs of 2 bits required to match full PW)
  Oup_gating	N-hot 16b	Output gating enable bits (pairs of 2 bits required to match full PW)
  Dp_bypass	0..1	MVM-DP bypass enable bit
  Inp_buf_we	0..1	MVM-DP input buffer write enable bit (must be set to accept IFD0 stream)
  Tlast_pred	0..1	Tlast bit that should match IFD0 tlast
  Inp_buf_addr	0..7	Location where PW is put in input buffer
  P2b_st	0..1	Start flag for parallel to bit serial conversion
  Comp_off	0	Disables the IMC bank compute, should always be 0.
  Weight_set	0.. IMC_NB_WEIGHT_SETS-1	Select the weight set used for compute
  Oup_buf_addr	0..7	Determines which PW of the ouput buffer is set on the AXIS
  Oup_buf_we	0..1	Transfer selected PW from output buffer to AXIS
  Tlast	0..1	Set tlast on output AXIS
  **********/
  typedef struct packed{
  bit [23:0]  rsvd;

  bit [2:0]   out_ctrl_rsvd;
  bit         out_ctrl_tlast;
  bit         out_ctrl_oup_buf_we;
  bit [2:0]   out_ctrl_buf_addr;

  bit [4:0]   imc_ctrl_rsvd;
  bit [1:0]   imc_ctrl_weight_set;
  bit         imc_ctrl_comp_off;

  bit         inp_ctrl_rsvd;
  bit         inp_ctrl_p2b_st;
  bit [2:0]   inp_ctrl_inp_buf_addr;
  bit         inp_ctrl_tlast_pred;
  bit         inp_ctrl_inp_buf_we;
  bit         inp_ctrl_dp_bypass;
  bit [2:0]   inp_ctrl_sw_test_mode; 

  bit [15:0]  oup_gating;
  bit [15:0]  inp_gating;
  } mvm_exe_swdp_cmd_struct;

  //`define  3
  // ****************************************************************************
  // Enumerated Types
  // ****************************************************************************

  /**
   * Enum to represent transfer sizes
   */
  typedef enum bit [3:0] {
    BURST_SIZE_8BIT    = AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = AXI_TRANSACTION_BURST_SIZE_64
  } burst_size_enum;

  /**
   * Enum to represent burst type in a transaction
   */
  typedef enum bit[1:0]{
    FIXED = AXI_TRANSACTION_BURST_FIXED,
    INCR =  AXI_TRANSACTION_BURST_INCR,
    WRAP =  AXI_TRANSACTION_BURST_WRAP
  } burst_type_enum;

  /**
   * Enum to represent burst lenght in a transaction
   */
  typedef enum bit[5:0]{
    BURST_LENGTH_1 = 1,
    BURST_LENGTH_2 = 2,
    BURST_LENGTH_4 = 4,
    BURST_LENGTH_8 = 8,
    BURST_LENGTH_16 = 16
  } burst_lenght_enum;

  /**
   * Enum to represent responses in a transaction
   */
  typedef enum bit [1:0] {
    OKAY    = AXI_OKAY_RESPONSE,
    EXOKAY  = AXI_EXOKAY_RESPONSE,
    SLVERR =  AXI_SLVERR_RESPONSE,
    DECERR  = AXI_DECERR_RESPONSE
  } resp_type_enum;


  /**
    * Token related
    */
  typedef enum bit [HEADER_CMD_FORMAT_WIDTH-1:0] {
    VERIF_MVM_CMD_FULL             = 'd0,
    VERIF_MVM_CMD_BYPASS           = 'd9
  } mvm_cmd_format_t;

  typedef struct packed {
    bit [HEADER_CMD_RSVD_WIDTH-1:0]       rsvd;
    mvm_cmd_format_t                      cmd_format;
    bit [HEADER_CMD_TOK_CONS_WIDTH-1:0]   token_cons;
    bit [HEADER_CMD_TOK_PROD_WIDTH-1:0]   token_prod;
    bit [HEADER_CMD_ID_WIDTH-1:0]         cmd_id;
  } mvm_cmd_header_t;

  typedef enum {
      VERIF_MVM_PRG_TOK_AGT  = 'd0,
      VERIF_MVM_EXE_TOK_AGT  = 'd1
  } mvm_tok_agt_type_t;

  typedef string string_queue_t [$];


  `include "ai_core_mvm_utils.svh"

  endpackage : ai_core_mvm_common_pkg

