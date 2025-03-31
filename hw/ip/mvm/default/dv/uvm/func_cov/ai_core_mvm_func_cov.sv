`ifndef AI_CORE_MVM_FUNC_COV_SV
`define AI_CORE_MVM_FUNC_COV_SV
`uvm_analysis_imp_decl(_axi4_lp_rcv_func_cov_pkt)
`uvm_analysis_imp_decl(_axis_ifdw_rcv_func_cov_pkt)
`uvm_analysis_imp_decl(_axis_ifd0_rcv_func_cov_pkt)
`uvm_analysis_imp_decl(_axis_ifd2_rcv_func_cov_pkt)
`uvm_analysis_imp_decl(_axi4_iau_data)
//typedef ai_core_mvm_subsys_reg_block MVM_RAL;
class ai_core_mvm_func_cov extends uvm_component;
  `uvm_component_utils(ai_core_mvm_func_cov)

  uvm_analysis_imp_axi4_lp_rcv_func_cov_pkt #(svt_axi_transaction,ai_core_mvm_func_cov) axi4_lp_2_func_cov_export;
  uvm_analysis_imp_axis_ifdw_rcv_func_cov_pkt #(svt_axi_transaction,ai_core_mvm_func_cov) axis_ifdw_2_func_cov_export;
  uvm_analysis_imp_axis_ifd0_rcv_func_cov_pkt #(svt_axi_transaction,ai_core_mvm_func_cov) axis_ifd0_2_func_cov_export;
  uvm_analysis_imp_axis_ifd2_rcv_func_cov_pkt #(svt_axi_transaction,ai_core_mvm_func_cov) axis_ifd2_2_func_cov_export;
  
  /** Analysis port connected to the AXI IAU SLAVE Agent */
  uvm_analysis_imp_axi4_iau_data#(svt_axi_transaction, ai_core_mvm_func_cov) axi4_iau_data_export;
  // QCMD memory
  bit [AXI_LT_DATA_WIDTH -1: 0] qcmd_mem [EXE_INSTR_DEPTH];
  // MVM memory
  typedef logic [IMC_COLUMN-1:0] [7:0] mvm_mem_ifdw[IMC_ROWS];
  typedef logic [IMC_COLUMN-1:0] [25:0] mvm_mem[IMC_ROWS];
  mvm_mem_ifdw mvm_mem_ifdw_0;
  mvm_mem_ifdw mvm_mem_ifdw_1;
  mvm_mem_ifdw mvm_mem_ifdw_2;
  mvm_mem_ifdw mvm_mem_ifdw_3;

  mvm_mem mvm_mem_0;
  mvm_mem mvm_mem_1;
  mvm_mem mvm_mem_2;
  mvm_mem mvm_mem_3;

  uvm_status_e status;

  mvm_prg_cmd_struct prg;
  mvm_exe_instr_struct qcmd;
  mvm_exe_cmd_header_struct exe_header;
  mvm_exe_cmd_struct exe;
  mvm_prg_swdp_cmd_struct prg_swdp;
  mvm_exe_swdp_cmd_struct exe_swdp;
  logic [IMC_COLUMN-1:0] [25:0] iau_out_matrix = {AXI_STREAM_IAU_DATA_WIDTH{1'b0}};
  logic [AXI_STREAM_IAU_DATA_WIDTH -1 : 0] iau_data;
  bit [63:0][0:25] iau_sign_extends_data;
    
  // AI Core MVM RAL Modl
  MVM_RAL mvm_regmodel;

  /***************************************************************************************
  					Covergroups
  ***************************************************************************************/
  /**AXI transactions covergroups**/
  covergroup mvm_axi4_lp_trans_cg with function sample(mvm_prg_cmd_struct prg, mvm_exe_instr_struct qcmd, mvm_exe_cmd_header_struct exe_header, mvm_exe_cmd_struct exe, mvm_prg_swdp_cmd_struct prg_swdp, mvm_exe_swdp_cmd_struct exe_swdp);
    option.per_instance = 1'b1;
    option.name         = "mvm_axi4_lp_trans_cg";

    cp_prg_a_s : coverpoint(prg.a_s) {
      bins prg_weight_sets[] = {[0 : 3]};
    }
    cp_prg_a_u_pw : coverpoint(prg.a_u_pw) {
      bins prg_row_offset[] = {[0 : 7]};
    }
    cp_prg_a_t_pw : coverpoint(prg.a_t_pw) {
      bins prg_column_offset[] = {[0 : 7]};
    }
    cp_prg_wb_u_pw : coverpoint(prg.wb_u_pw) {
      bins prg_row_size[] = {[0 : 7]};
    }
    cp_prg_wb_t_pw : coverpoint(prg.wb_t_pw) {
      bins prg_column_size[] = {[0 : 7]};
    }

    cp_qcmd_a_s : coverpoint(qcmd.a_s) {
      bins qcmd_weight_sets[] = {[0 : 3]};
    }
    cp_qcmd_a_u_pw : coverpoint(qcmd.a_u_pw) {
      bins qcmd_row_offset[] = {[0 : 7]};
    }
    cp_qcmd_a_t_pw : coverpoint(qcmd.a_t_pw) {
      bins qcmd_column_offset[] = {[0 : 7]};
    }
    cp_qcmd_wb_u_pw : coverpoint(qcmd.wb_u_pw) {
      bins qcmd_row_size[] = {[0 : 7]};
    }
    cp_qcmd_wb_t_pw : coverpoint(qcmd.wb_t_pw) {
      bins qcmd_column_size[] = {[0 : 7]};
    }
    cp_exe_header : coverpoint(exe_header.cmd_format) {
      bins exe_data_path   = {0};
      bins exe_data_bypass = {1};
    }
    cp_exe_loop_len : coverpoint(exe.loop_len) {
      bins exe_loop_len_small_bins[]  = {1,2,3,4,5};
      bins exe_loop_len_medium_bins[] = {122,123,124};
      bins exe_loop_len_large_bins[]  = {251,252,253,254,255};
      bins exe_loop_len_bins          = {[6:10],[11:50],[51:100],[100:121],[125:150],[151:200],[201:250]};
    }
    cp_exe_loop_ptr : coverpoint(exe.loop_ptr) {
      bins exe_loop_ptr[] = {[1 : 255]};
    }
    cp_exe_loop_iter : coverpoint(exe.loop_iter) {
      bins exe_loop_iter_short = {[0 : 5]};
      bins exe_loop_iter_long = {[6 : $]};
    }
    
  endgroup : mvm_axi4_lp_trans_cg

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
    axi4_lp_2_func_cov_export        = new("axi4_lp_2_func_cov_export", this);
    axis_ifdw_2_func_cov_export      = new("axis_ifdw_2_func_cov_export", this);
    axis_ifd0_2_func_cov_export      = new("axis_ifd0_2_func_cov_export", this);
    axis_ifd2_2_func_cov_export      = new("axis_ifd2_2_func_cov_export", this);     
    axi4_iau_data_export             = new("axi4_iau_data_export", this);
    mvm_axi4_lp_trans_cg             = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

  virtual function void write_axi4_lp_rcv_func_cov_pkt(input svt_axi_transaction axi4_lp_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXI4 LP Report %s", axi4_lp_pkt.sprint()), UVM_HIGH);

    if(axi4_lp_pkt.addr >= MVMEXE_CSR_START_ADDR && axi4_lp_pkt.addr <= MVMEXE_CSR_END_ADDR) begin
    end
    else if(axi4_lp_pkt.addr >= MVMPRG_CSR_START_ADDR && axi4_lp_pkt.addr <= MVMPRG_CSR_END_ADDR ) begin
    end
    else if(axi4_lp_pkt.addr >= MVM_EXE_CMDB_START_ADDR && axi4_lp_pkt.addr <= MVM_EXE_CMDB_END_ADDR ) begin
      exe_header = axi4_lp_pkt.data[0];
      exe        = axi4_lp_pkt.data[1];
      uvm_report_info(get_type_name(), $psprintf("Func cov: Configured the EXE_HEADER = %p,MVM_EXE_CMDB = %p", exe_header, exe), UVM_HIGH);
    end
    else if(axi4_lp_pkt.addr >= MVM_EXE_SWDP_CMDB_START_ADDR && axi4_lp_pkt.addr <= MVM_EXE_SWDP_CMDB_END_ADDR ) begin
      exe_swdp = axi4_lp_pkt.data[0];
    end
    else if(axi4_lp_pkt.addr >= MVM_EXE_INSTR_START_ADDR && axi4_lp_pkt.addr <= MVM_EXE_INSTR_END_ADDR ) begin
      qcmd = axi4_lp_pkt.data[0];
      uvm_report_info(get_type_name(), $psprintf("Func cov: Configured the MVM_EXE_INSTR = %p", qcmd), UVM_HIGH);
    end
    else if(axi4_lp_pkt.addr >= MVM_PRG_CMDB_START_ADDR && axi4_lp_pkt.addr <= MVM_PRG_CMDB_END_ADDR ) begin
      prg = axi4_lp_pkt.data[1];
      uvm_report_info(get_type_name(), $psprintf("Func cov: Configured the MVM_PRG_CMDB = %p", prg), UVM_HIGH);
    end
    else if(axi4_lp_pkt.addr >= MVM_PRG_SWDP_CMDB_START_ADDR && axi4_lp_pkt.addr <= MVM_PRG_SWDP_CMDB_END_ADDR ) begin
      prg_swdp = axi4_lp_pkt.data[0];
    end
    mvm_axi4_lp_trans_cg.sample(prg, qcmd, exe_header,exe, prg_swdp,exe_swdp);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXI4 LP Report process_lp_packet function %s", axi4_lp_pkt.sprint()), UVM_DEBUG);
  endfunction : write_axi4_lp_rcv_func_cov_pkt

  virtual function void write_axis_ifdw_rcv_func_cov_pkt(input svt_axi_transaction axis_ifdw_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXIS IFDW Report %s", axis_ifdw_pkt.sprint()), UVM_HIGH);
  endfunction : write_axis_ifdw_rcv_func_cov_pkt

  virtual function void write_axis_ifd0_rcv_func_cov_pkt(input svt_axi_transaction axis_ifd0_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXIS IFD0 Report %s", axis_ifd0_pkt.sprint()), UVM_HIGH);
  endfunction : write_axis_ifd0_rcv_func_cov_pkt
   
 virtual function void write_axis_ifd2_rcv_func_cov_pkt(input svt_axi_transaction axis_ifd2_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXIS IFD2 Report %s", axis_ifd2_pkt.sprint()), UVM_HIGH);
  endfunction : write_axis_ifd2_rcv_func_cov_pkt
   

  virtual function void write_axi4_iau_data(input svt_axi_transaction axi4_iau_pkt);
    uvm_report_info(get_type_name(), $psprintf("Func cov: received packet from AXI4 IAU Report %s", axi4_iau_pkt.sprint()), UVM_HIGH);
  endfunction : write_axi4_iau_data

endclass
`endif
