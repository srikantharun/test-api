
/** DPU UVM package */
package dpu_common_pkg;
  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import aic_dp_cmd_gen_pkg::*;
  import ai_core_dp_cmd_gen_uvm_pkg::*;
  import dpu_pkg::*;
  import dpu_csr_ral_pkg::*;


  localparam ICDF_TEST_PATH               = "/verif_tb/icdf_stimuli/dpu/extensive_tests/";
  // Localparam declarations
  localparam DPU_CSR_ADDR_ST              = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_ST_ADDR[dpu_pkg::DPU_IDX_CSR];
  localparam DPU_CSR_ADDR_END             = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_END_ADDR[dpu_pkg::DPU_IDX_CSR];
  localparam DPU_PRG_ADDR_ST              = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_ST_ADDR[dpu_pkg::DPU_IDX_IMEM];
  localparam DPU_PRG_ADDR_END             = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_END_ADDR[dpu_pkg::DPU_IDX_IMEM];
  localparam DPU_CMD_ADDR_ST              = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_ST_ADDR[dpu_pkg::DPU_IDX_CMDB]; 
  localparam DPU_CMD_ADDR_END             = aic_addr_map_pkg::AIC_LOC_D_DPU_REGION_END_ADDR[dpu_pkg::DPU_IDX_CMDB]; 

  localparam AXI_AW                       = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  localparam AXI_DW                       = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  localparam IN_IFD0_WORD_DW              = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam IN_IFD1_WORD_DW              = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam OUT_WORD_DW                  = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE;
  localparam PWORD_SIZE                   = aic_common_pkg::AIC_PWORD_SIZE;
  localparam IFD1_STREAM_SIZE             = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH;
  localparam CMD_MEM_WIDTH                = $bits(aic_dp_cmd_gen_pkg::cmdb_cmd_t);

  localparam HALF_PWORD_SIZE              = PWORD_SIZE/2;
  localparam QUARTER_PWORD_SIZE           = PWORD_SIZE/4;
  localparam ACC_REG_SIZE                 = dpu_pkg::A_DEPTH;
  localparam GENERAL_AND_BIN_REG_SIZE     = dpu_pkg::B_DEPTH;
  localparam PAIRED_COEF_REG_SIZE         = dpu_pkg::C_DEPTH;
  localparam LUT_REG_SIZE                 = dpu_pkg::D_DEPTH;
  localparam PROG_MEM_DEPTH               = dpu_pkg::PRG_MEM_DEPTH;

  localparam HEADER_CMD_TOK_PROD_WIDTH    = 16;
  localparam HEADER_CMD_TOK_CONS_WIDTH    = 16;
  localparam HEADER_CMD_RSVD_FORMAT_WIDTH = 8-aic_dp_cmd_gen_pkg::CmdBlockFormatWidth;
  localparam HEADER_CMD_RSVD_WIDTH        = 8;
  localparam HEADER_CMD_TRIGGERS_WIDTH    = 8;
  localparam HEADER_CMD_CONFIG_WIDTH      = 8;

  localparam DPU_PWORD_BIT_MAX            = 48;
  localparam DPU_CMD_FULL_NUMROWS         = 2;
  localparam DPU_CMD_LOOPONLY_NUMROWS     = 1;
  localparam A_REG_OFFSET                 = 'h20;
  localparam B_C_REG_OFFSET               = 'h40;
  localparam CL_REG_OFFSET                = 'h80;
  localparam CH_REG_OFFSET                = 'hC0;
  localparam LUT_REG_OFFSET               = 'h100;

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

  typedef dpu_csr_reg_block DPU_RAL;
  typedef bit [AXI_DW-1:0] bit_dw_t;
  typedef bit [AXI_AW-1:0] bit_aw_t;

  typedef struct packed {
    bit [HEADER_CMD_CONFIG_WIDTH-1:0]           h_config;
    bit [HEADER_CMD_RSVD_FORMAT_WIDTH-1:0]      rsvd_format;
    aic_dp_cmd_gen_pkg::cmd_format_e            format;
    bit [HEADER_CMD_TOK_CONS_WIDTH-1:0]         token_cons;
    bit [HEADER_CMD_TOK_PROD_WIDTH-1:0]         token_prod;
    bit [HEADER_CMD_RSVD_WIDTH-1:0]             rsvd;
    bit [HEADER_CMD_TRIGGERS_WIDTH-1:0]         triggers;
  } dpu_cmd_header_t;

  typedef enum bit [8:0] {
    //input stream 0
    i0      = 'h0,
    i0_f16  = 'h1,
    i0_f32  = 'h2,
    i0_bp   = 'h3,
    i0_i48  = 'h4,
    i0_f24  = 'h5,
    //ifd0 stream peek
    pi0      = 'h8,
    pi0_f16  = 'h9,
    pi0_f32  = 'hA,
    pi0_bp   = 'hB,
    pi0_i48  = 'hC,
    pi0_f24  = 'hD,
    //input stream 1
    i1      = 'h10,
    i1_f16  = 'h11,
    i1_f32  = 'h12,
    i1_bp   = 'h13,
    i1_i16  = 'h14,
    i1_f24  = 'h15,
    //ifd1 stream peek
    pi1      = 'h18,
    pi1_f16  = 'h19,
    pi1_f32  = 'h1A,
    pi1_bp   = 'h1B,
    pi1_i16  = 'h1C,
    pi1_f24  = 'h1D,
    //internal regs
    a[8]    = 'h20,
    b_c[64] = 'h40,
    //those below doesn't exist in rtl, created for verif purposes
    cl[64]  = 'h80,
    ch[64]  = 'hC0,
    lut     = 'h100
  } src_t;

  typedef enum bit [8:0] {
    //output stream
    o           = 'h0,
    o_f16       = 'h1,
    o_f32       = 'h2,
    o_bp        = 'h3,
    o_i16       = 'h4,
    o_f24       = 'h5,
    //output stream with TLAST asserted
    l           = 'h10,
    l_f16       = 'h11,
    l_f32       = 'h12,
    l_bp        = 'h13,
    l_i16       = 'h14,
    l_f24       = 'h15,
    //internal regs
    dst_a[8]    = 'h20,
    dst_b_c[64] = 'h40,
    //those below doesn't exist in rtl, created for verif purposes
    dst_cl[64]  = 'h80,
    dst_ch[64]  = 'hC0,
    dst_lut     = 'h100

  } dst_t;

  
  typedef struct packed {
    dpu_cmd_header_t                      header;
    aic_dp_cmd_gen_pkg::cmdb_cmd_struct_t cmd;   
  } dpu_cmd_descriptor_t;

  typedef enum bit [5:0] {
    err_act_stream_in0,
    err_act_stream_in1,
    err_act_stream_out,
    err_illegal_format,
    err_empty_program,
    err_init_segfault,
    err_loop_segfault,
    err_i0_termination,
    err_i1_termination,
    err_id_illegal_instr,
    err_i0_of,
    err_i0_uf,
    err_i0_nx,
    err_i1_of,
    err_i1_uf,
    err_i1_nx,
    err_madd_op_of,
    err_madd_op_uf,
    err_madd_op_nx,
    err_madd_op_nv,
    err_sumr_op_of,
    err_sumr_op_nx,
    err_sumr_op_nv,
    err_o_of,
    err_o_uf,
    err_o_nx,
    dbg_sw_interrupt   = 32,
    cmdblk_cmd_dropped = 40
  } dpu_irq_bit_pos_t;

  typedef struct packed {
    bit cmdblk_cmd_dropped;
    bit [6:0] rsvd2;
    bit dbg_sw_interrupt;
    bit [5:0] rsvd;
    bit err_o_nx;
    bit err_o_uf;
    bit err_o_of;
    bit err_sumr_op_nv;
    bit err_sumr_op_nx;
    bit err_sumr_op_of;
    bit err_madd_op_nv;
    bit err_madd_op_nx;
    bit err_madd_op_uf;
    bit err_madd_op_of;
    bit err_i1_nx;
    bit err_i1_uf;
    bit err_i1_of;
    bit err_i0_nx;
    bit err_i0_uf;
    bit err_i0_of;
    bit err_id_illegal_instr;
    bit err_i1_termination;
    bit err_i0_termination;
    bit err_loop_segfault;
    bit err_init_segfault;
    bit err_empty_program;
    bit err_illegal_format;
    bit err_act_stream_out;
    bit err_act_stream_in1;
    bit err_act_stream_in0;
  } dpu_irq_reg_t;

  typedef struct packed {
    bit dbg_sw_irq;
    bit [26:0] unused_27b;
    bit drop_illegal_instr;
    bit skip_illegal_prog;
    bit out_int_sgn;
    bit i1_int_sgn;
    bit i0_int_sgn;
  } dp_ctrl_reg_t;

  typedef enum bit[1:0] {NO_INSTR_SRC, SINGLE_INSTR_SRC, DUAL_INSTR_SRC, TRIPLE_INSTR_SRC} instr_src_t;

  function instr_src_t get_instr_num_srcs(dpu_dp_cmd_t cmd);
    if ( cmd.opcode == OPC_UNARY && cmd.src1 inside {[FUNC_MVCL : FUNC_SUMR]} ||
         cmd.opcode == OPC_RFS && cmd.src2 inside {[FUNC_NEG : FUNC_SUMR], FUNC_MV} ||
         cmd.opcode == OPC_MV )
      return SINGLE_INSTR_SRC;
    else if ( cmd.opcode inside {[OPC_MUL : OPC_CMADD]} || 
              cmd.opcode == OPC_LUT && cmd.src2 == FUNC_LUT ||
              cmd.opcode == OPC_RFS && cmd.src2 inside {FUNC_LUT, [FUNC_MUL : FUNC_CMADD] })
      return DUAL_INSTR_SRC;
    else if (cmd.opcode inside {OPC_MADD, OPC_MADD_RFS})
      return TRIPLE_INSTR_SRC;
    else // NOP
      return NO_INSTR_SRC;
  endfunction : get_instr_num_srcs


  //initialize a regs (non SRAM), b and c registers which are SRAMs
  task init_regs(bit rnd = 0);
    static string mem_path[3] = { "hdl_top.dut.i_dpu_dp.i_dpu_bstore.u_axe_tcl_sram.memory_q",
                                  "hdl_top.dut.i_dpu_dp.i_dpu_cstore.u_axe_tcl_sram[0].memory_q",
                                  "hdl_top.dut.i_dpu_dp.i_dpu_cstore.u_axe_tcl_sram[1].memory_q" };

    static string a_regs_path = "hdl_top.dut.i_dpu_dp.i_dpu_aregs.regs";


    foreach (mem_path[i]) begin
      if (uvm_hdl_check_path(mem_path[i])) begin
        for (int j = 0; j < PWORD_SIZE; j++) begin
          if (!uvm_hdl_deposit($sformatf("%s[%0d]", mem_path[i], j), 'h0))
            `uvm_error("init_regs", $sformatf("Deposit failed, invalid reg: %s index: %0d", mem_path[i], j));
        end
      end
      else
        `uvm_error("init_regs", $sformatf("Deposit failed, invalid path: %s", mem_path[i]));
    end

    if (uvm_hdl_check_path(a_regs_path)) begin
      for (int i = 0; i < 8; i++) begin
        for (int j = 0; j < PWORD_SIZE; j++)
          if (!uvm_hdl_deposit($sformatf("%s[%0d][%0d]", a_regs_path,i,j), 'h0))
            `uvm_error("init_regs", $sformatf("Deposit failed, invalid reg: %s[%0d]", a_regs_path, i));
      end
    end
    else
      `uvm_error("init_regs", $sformatf("Deposit failed, invalid path: %s", a_regs_path));
  endtask

  `include "dpu_cmd_tr.svh"

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

  `include "fp_utils.svh"

endpackage : dpu_common_pkg
