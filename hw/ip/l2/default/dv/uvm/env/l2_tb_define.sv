//Defines///////////////////////////
`define AXI_LP_ADDR_WIDTH 40
`define AXI_LP_DATA_WIDTH 512
`define AXI_STREAM_IFDW_DATA_WIDTH 512
`define AXI_STREAM_IFD0_DATA_WIDTH 512
`define AXI_STREAM_IAU_DATA_WIDTH 1664
`define AXI_TRANSACTION_BURST_SIZE_8 0
`define AXI_TRANSACTION_BURST_SIZE_16 1
`define AXI_TRANSACTION_BURST_SIZE_32 2
`define AXI_TRANSACTION_BURST_SIZE_64 3
`define AXI_TRANSACTION_BURST_SIZE_128 4
`define AXI_TRANSACTION_BURST_SIZE_256 5
`define AXI_TRANSACTION_BURST_SIZE_512 6
`define AXI_TRANSACTION_BURST_FIXED 0
`define AXI_TRANSACTION_BURST_INCR 1
`define AXI_TRANSACTION_BURST_WRAP 2
`define AXI_OKAY_RESPONSE 0
`define AXI_EXOKAY_RESPONSE 1
`define AXI_SLVERR_RESPONSE 2
`define AXI_DECERR_RESPONSE 3
`define MVM_CSR_START_ADDR 28'h009_0000
`define MVM_EXE_CMDB_START_ADDR 28'h009_1000
`define MVM_EXE_SWDP_CMDB_START_ADDR 28'h009_2000
`define MVM_EXE_QCMD_START_ADDR 28'h009_8000
`define MVM_PRG_CMDB_START_ADDR 28'h00A_1000
`define MVM_PRG_SWDP_CMDB_START_ADDR 28'h00A_2000
`define MVM_CSR_END_ADDR 28'h009_0FFF
`define MVM_EXE_CMDB_END_ADDR 28'h009_1FFF
`define MVM_EXE_SWDP_CMDB_END_ADDR 28'h009_7FFF
`define MVM_EXE_QCMD_END_ADDR 28'h009_8FFF
`define MVM_PRG_CMDB_END_ADDR 28'h00A_1FFF
`define MVM_PRG_SWDP_CMDB_END_ADDR 28'h00A_7FFF
`define QCMD_DEPTH 256
`define PWORD_SIZE 512
`define WEIGHT_SETS 4
`define IMC_ROWS 512
`define IMC_COLUMN 512
`define MATRIX 64
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
bit [7:0] op_code;
} mvm_prg_cmd_struct;
/******************************************************************************************************************************
A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights to be used for compute
A_u_pw	0..7	Compute row offset (input offset)
A_t_pw	0..7	Compute column offset (output offset)
Wb_u_pw	0..7	Compute row size (input size) A value of 0 maps to an operation on 1 PW, a value of 7 maps to an operation on 8 PWs
Wb_t_pw	0..7	Compute column size (output size) A value of 0 maps to an operation on 1PW, a value of 7 maps to an operation on 8PWs
*******************************************************************************************************************************/
typedef struct packed{
bit [2:0] wb_t_pw;
bit [2:0] wb_u_pw;
bit [2:0] a_t_pw;
bit [2:0] a_u_pw;
bit [1:0] a_s;
} mvm_qcmd_struct;
/******************************************************************************************************************************
Op_code	0, 1	//CMDB descriptor operation codes 0=MVM_EXE_CMDB_CMP_OPC (MVM-DP compute operation), 1=MVM_EXE_CMDB_BYP_OPC (MVM-DP bypass operation)
Qcmd_len	1..MVM_EXE_QCMD_MEM_DEPTH-1 //Length of the qcmd section that is repeated by a qcmd iteration
Qcmd_ptr	0.. MVM_EXE_QCMD_MEM_DEPTH-1	Start pointer for the used qcmd section
Qcmd_iter	1..2**32-1	Number of iterations to run

*******************************************************************************************************************************/
typedef struct packed{
bit [31:0] qcmd_iter;
bit [15:0] qcmd_ptr;
bit [7:0]  qcmd_len;
bit [7:0]  op_code;
} mvm_exe_cmd_struct;
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
    BURST_SIZE_8BIT    = `AXI_TRANSACTION_BURST_SIZE_8,
    BURST_SIZE_16BIT   = `AXI_TRANSACTION_BURST_SIZE_16,
    BURST_SIZE_32BIT   = `AXI_TRANSACTION_BURST_SIZE_32,
    BURST_SIZE_64BIT   = `AXI_TRANSACTION_BURST_SIZE_64,
    BURST_SIZE_128BIT  = `AXI_TRANSACTION_BURST_SIZE_128,
    BURST_SIZE_256BIT  = `AXI_TRANSACTION_BURST_SIZE_256,
    BURST_SIZE_512BIT  = `AXI_TRANSACTION_BURST_SIZE_512
  } burst_size_enum;

  /**
   * Enum to represent burst type in a transaction
   */
  typedef enum bit[1:0]{
    FIXED = `AXI_TRANSACTION_BURST_FIXED,
    INCR =  `AXI_TRANSACTION_BURST_INCR,
    WRAP =  `AXI_TRANSACTION_BURST_WRAP
  } burst_type_enum;

  /**
   * Enum to represent burst lenght in a transaction
   */
  typedef enum bit[9:0]{
    BURST_LENGTH_1 = 1,
    BURST_LENGTH_2 = 2,
    BURST_LENGTH_4 = 4,
    BURST_LENGTH_8 = 8,
    BURST_LENGTH_16 = 16,
    BURST_LENGTH_32 = 32,
    BURST_LENGTH_64 = 64,
    BURST_LENGTH_128 = 128,
    BURST_LENGTH_256 = 256
  } burst_lenght_enum;

  /**
   * Enum to represent responses in a transaction
   */
  typedef enum bit [1:0] {
    OKAY    = `AXI_OKAY_RESPONSE,
    EXOKAY  = `AXI_EXOKAY_RESPONSE,
    SLVERR =  `AXI_SLVERR_RESPONSE,
    DECERR  = `AXI_DECERR_RESPONSE
  } resp_type_enum;
