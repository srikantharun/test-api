package iau_common_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import aic_dp_cmd_gen_pkg::*;
  import aic_addr_map_pkg::*;
  import ai_core_dp_cmd_gen_uvm_pkg::*;
  import iau_pkg::*;
  import iau_csr_ral_pkg::*;

  `ifdef D_IAU
    localparam IAU_CSR_ADDR_ST           = aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_CSR];
    localparam IAU_CMD_BLOCK_ADDR_ST     = aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_CMDB];
    localparam IAU_CMD_BLOCK_ADDR_END    = aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_END_ADDR[iau_pkg::IAU_IDX_CMDB];
    localparam IAU_DPCMD_ADDR_ST         = aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_DPCMD];
    localparam IAU_DPCMD_ADDR_END        = aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_END_ADDR[iau_pkg::IAU_IDX_DPCMD];
  `else
    localparam IAU_CSR_ADDR_ST           = aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_CSR];
    localparam IAU_CMD_BLOCK_ADDR_ST     = aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_CMDB];
    localparam IAU_CMD_BLOCK_ADDR_END    = aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_END_ADDR[iau_pkg::IAU_IDX_CMDB];
    localparam IAU_DPCMD_ADDR_ST         = aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_ST_ADDR[iau_pkg::IAU_IDX_DPCMD];
    localparam IAU_DPCMD_ADDR_END        = aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_END_ADDR[iau_pkg::IAU_IDX_DPCMD];
  `endif
  localparam OBS_W                     = aic_common_pkg::AIC_DEV_OBS_DW;
  localparam CID_W                     = aic_common_pkg::AIC_CID_SUB_W;
  localparam BLOCK_ID_W                = aic_common_pkg::AIC_BLOCK_ID_WIDTH;
  localparam AXI_AW                    = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  localparam AXI_DW                    = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  localparam IN_WORD_DW                = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam OUT_WORD_DW               = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam PWORD_SIZE                = aic_common_pkg::AIC_PWORD_SIZE;
  localparam EXTEND_LEN                = OUT_WORD_DW - IN_WORD_DW;
  localparam AXIS_IW                   = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH;
  localparam AXIS_OW                   = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH;
  localparam ACC_REG_SIZE              = 8;
  localparam ADD_MAX_POS_VAL           = 2**(OUT_WORD_DW-1)-1;
  localparam ADD_MAX_NEG_VAL           = -2**(OUT_WORD_DW-1);
  localparam ADD_MAX_UNSIGNED_VAL      = 2**OUT_WORD_DW-1;
  localparam PROG_MEM_DEPTH            = 256;

  localparam CMD_MEM_WIDTH                = $bits(aic_dp_cmd_gen_pkg::cmdb_cmd_t);
  localparam HEADER_CMD_ID_WIDTH          = 16;
  localparam HEADER_CMD_TOK_PROD_WIDTH    = 16;
  localparam HEADER_CMD_TOK_CONS_WIDTH    = 16;
  localparam HEADER_CMD_FORMAT_WIDTH      = 8;
  localparam HEADER_CMD_RSVD_FORMAT_WIDTH = 8-aic_dp_cmd_gen_pkg::CmdBlockFormatWidth;
  localparam HEADER_CMD_RSVD_WIDTH        = 8;
  localparam HEADER_CMD_TRIGGERS_WIDTH    = 8;
  localparam HEADER_CMD_CONFIG_WIDTH      = 8;

  localparam CMD_NUM_ROWS_BYPASS          = 0; //bypass command does not have payload
  localparam CMD_NUM_ROWS_M1N0            = 1;
  localparam CMD_NUM_ROWS_M1N1            = 2;
  localparam CMD_NUM_ROWS_M1N2            = 3;
  localparam CMD_NUM_ROWS_M2N0            = 2;
  localparam CMD_NUM_ROWS_M2N1            = 3;
  localparam CMD_NUM_ROWS_M2N2            = 4;
  localparam CMD_NUM_ROWS_M3N0            = 3;
  localparam CMD_NUM_ROWS_M3N1            = 4;
  localparam CMD_NUM_ROWS_M3N2            = 5;

  // IAU CMD descriptor struct
  // =======================================
  typedef struct packed {
    logic [IAU_CMD_ITER_DW-1:0]  loop_iter;
    logic [IAU_CMD_LEN_DW-1:0]   loop_len;
    logic [IAU_CMD_START_DW-1:0] loop_start;
    cmd_opcode_e                 cmd_opcode;
  } iau_cmd_desc_t;



  typedef bit [AXI_DW-1:0] bit_dw_t;
  typedef bit [AXI_AW-1:0] bit_aw_t;
  typedef string string_queue_t [$];
  typedef int int_index_arr_t[int];

  typedef enum bit [HEADER_CMD_FORMAT_WIDTH-1:0] {
    CMD_OP_EXE = 'd0,
    CMD_OP_BYP = 'd1
  } iau_cmd_format_t;

  typedef struct packed {
    bit [HEADER_CMD_CONFIG_WIDTH-1:0]           h_config;
    bit [HEADER_CMD_RSVD_FORMAT_WIDTH-1:0]      rsvd_format;
    aic_dp_cmd_gen_pkg::cmd_format_e            format;
    bit [HEADER_CMD_TOK_CONS_WIDTH-1:0]         token_cons;
    bit [HEADER_CMD_TOK_PROD_WIDTH-1:0]         token_prod;
    bit [HEADER_CMD_RSVD_WIDTH-1:0]             rsvd;
    bit [HEADER_CMD_TRIGGERS_WIDTH-1:0]         triggers;
  } iau_cmd_header_t;


  typedef enum bit [3:0] {
    REG0 = 4'b0000,
    REG1 = 4'b0001,
    REG2 = 4'b0010,
    REG3 = 4'b0011,
    REG4 = 4'b0100,
    REG5 = 4'b0101,
    REG6 = 4'b0110,
    REG7 = 4'b0111,
    PUSH  = 4'b1000,
    PUSH_TLAST = 4'b1001,
    POP = 4'b1010
  } regs_t;

  typedef struct packed {
    regs_t src1;
    regs_t src0;
    regs_t dst;
    bit    rfs;
    opcode_e opcode;
  } iau_dp_cmd_t;

  typedef enum bit [5:0] {
    ERR_ACT_STREAM_IN,
    ERR_ACT_STREAM_OUT,
    ERR_EARLY_TLAST_STREAM_IN,
    ERR_EARLY_TLAST_STREAM_OUT,
    ERR_PRG_SEGFAULT,
    ERR_PRG_LEN_ZERO,
    ERR_LOOP_ITER_ZERO,
    ERR_ILLEGAL_RFS_INSTR,
    CMDBLK_CMD_DROPPED,
    DBG_SW_INTERRUPT = 32
  } irq_t;

  typedef enum bit [5:0] {
    SIGNED_OP,
    SAT_OP,
    IGNORE_SEGFAULT,
    DBG_SW_IRQ = 32
  } dp_ctrl_t;


  typedef struct packed {
    bit dbg_sw_interrupt;
    bit [21:0] rsvd;
    bit cmdblk_cmd_dropped;
    bit err_illegal_rfs_instr;
    bit err_loop_iter_zero;
    bit err_prg_len_zero;
    bit err_prg_segfault;
    bit err_early_tlast_stream_out;
    bit err_early_tlast_stream_in;
    bit err_act_stream_out;
    bit err_act_stream_in;
  } irq_en_t;


  typedef iau_csr_reg_block IAU_RAL;

  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m1n2_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m2n2_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n0_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n1_t;
  
  typedef struct packed {
    aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    aic_dp_cmd_gen_pkg::loop_description_t main_2;
    aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    aic_dp_cmd_gen_pkg::loop_description_t main_1;
    aic_dp_cmd_gen_pkg::command_extra_t    extra;
    aic_dp_cmd_gen_pkg::loop_description_t main_0;
  } cmdb_cmd_m3n2_t;

  `include "iau_cmd_tr.svh"

  function int get_cmd_num_rows (aic_dp_cmd_gen_pkg::cmd_format_e cmd_format);
    /** update get_cmd_num_rows variable depending on the format type */
    case (cmd_format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: 
        get_cmd_num_rows = CMD_NUM_ROWS_M1N0;
      aic_dp_cmd_gen_pkg::LoopsM1N1: 
        get_cmd_num_rows = CMD_NUM_ROWS_M1N1;
      aic_dp_cmd_gen_pkg::LoopsM1N2: 
        get_cmd_num_rows = CMD_NUM_ROWS_M1N2;
      aic_dp_cmd_gen_pkg::LoopsM2N0: 
        get_cmd_num_rows = CMD_NUM_ROWS_M2N0;
      aic_dp_cmd_gen_pkg::LoopsM2N1:
        get_cmd_num_rows = CMD_NUM_ROWS_M2N1;
      aic_dp_cmd_gen_pkg::LoopsM2N2: 
        get_cmd_num_rows = CMD_NUM_ROWS_M2N2;
      aic_dp_cmd_gen_pkg::LoopsM3N0:
        get_cmd_num_rows = CMD_NUM_ROWS_M3N0;
      aic_dp_cmd_gen_pkg::LoopsM3N1: 
        get_cmd_num_rows = CMD_NUM_ROWS_M3N1;
      aic_dp_cmd_gen_pkg::LoopsM3N2:
        get_cmd_num_rows = CMD_NUM_ROWS_M3N2;
      aic_dp_cmd_gen_pkg::Bypass : 
        get_cmd_num_rows = CMD_NUM_ROWS_BYPASS;
    endcase
    return get_cmd_num_rows;
  endfunction : get_cmd_num_rows

  function iau_cmd_tr get_full_cmd_from_alternative_cmd (bit [CMD_MEM_WIDTH-1:0] cmd, aic_dp_cmd_gen_pkg::cmd_format_e cmd_format);
    /** create command to send to model and set common variables */
    static iau_cmd_tr full_cmd = iau_cmd_tr::type_id::create("full_cmd");
    full_cmd.format = cmd_format;
    full_cmd.valid = 1;
    //cast the current aux_cmd to the correspondent format
    case (cmd_format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        cmdb_cmd_m1n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.main_0 = aux_cmd.main_0;
        full_cmd.extra  = aux_cmd.extra;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        cmdb_cmd_m1n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main  = aux_cmd.nested_0_map_main;
        full_cmd.nested_0           = aux_cmd.nested_0;
        full_cmd.extra              = aux_cmd.extra;
        full_cmd.main_0             = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        cmdb_cmd_m1n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main  = aux_cmd.nested_1_map_main;
        full_cmd.nested_1           = aux_cmd.nested_1;
        full_cmd.nested_0_map_main  = aux_cmd.nested_0_map_main;
        full_cmd.nested_0           = aux_cmd.nested_0;
        full_cmd.extra              = aux_cmd.extra;
        full_cmd.main_0             = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        cmdb_cmd_m2n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_1      = aux_cmd.main_1;
        full_cmd.extra       = aux_cmd.extra;
        full_cmd.main_0      = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        cmdb_cmd_m2n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main;
        full_cmd.nested_0            = aux_cmd.nested_0;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra;
        full_cmd.main_0              = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        cmdb_cmd_m2n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main   = aux_cmd.nested_1_map_main ;
        full_cmd.nested_1            = aux_cmd.nested_1 ;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main ;
        full_cmd.nested_0            = aux_cmd.nested_0 ;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra ;
        full_cmd.main_0              = aux_cmd.main_0 ;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        cmdb_cmd_m3n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_2      = aux_cmd.main_2;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_1      = aux_cmd.main_1;
        full_cmd.extra       = aux_cmd.extra;
        full_cmd.main_0      = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        cmdb_cmd_m3n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main;
        full_cmd.nested_0            = aux_cmd.nested_0;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_2              = aux_cmd.main_2;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra;
        full_cmd.main_0              = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        cmdb_cmd_m3n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main   = aux_cmd.nested_1_map_main ;
        full_cmd.nested_1            = aux_cmd.nested_1 ;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main ;
        full_cmd.nested_0            = aux_cmd.nested_0 ;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_2              = aux_cmd.main_2;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra ;
        full_cmd.main_0              = aux_cmd.main_0 ;
      end
      default : begin
        full_cmd.valid = 0;
        $fatal($sformatf("Command format %0d not implemented", cmd_format));
      end
    endcase
    return full_cmd;
  endfunction : get_full_cmd_from_alternative_cmd

endpackage:iau_common_pkg
