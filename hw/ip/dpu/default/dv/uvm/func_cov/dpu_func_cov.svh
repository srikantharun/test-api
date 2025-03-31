
`ifndef DPU_COVERAGE_SV
`define DPU_COVERAGE_SV

//data stream covergroup used in ref_model, because you need to evaluate
//the program length, number of iterations, which instruction of which data type, all of that is done in ref_model
covergroup cvg_in_data with function sample (src_t src, opcode_e op,func_e func, bit [47:0] dt, int mask_value, int mask_size, bit [1:0] offset_broadcast, bit [1:0] loop_select, bit pword32);
  option.per_instance = 1'b1;
  option.name         = "cvg_in_data";

  cp_unary_func : coverpoint func iff (op == OPC_UNARY) {
    bins nop     = {FUNC_NOP};
    bins mvcl    = {FUNC_MVCL};
    bins mvch    = {FUNC_MVCH};
    bins clmv    = {FUNC_CLMV};
    bins chmv    = {FUNC_CHMV};
    bins clmvcl  = {FUNC_CLMVCL};
    bins clmvch  = {FUNC_CLMVCH};
    bins chmvcl  = {FUNC_CHMVCL};
    bins chmvch  = {FUNC_CHMVCH};
    bins mv64    = {FUNC_MV64};
    bins mvcl64  = {FUNC_MVCL64};
    bins mvch64  = {FUNC_MVCH64};
    bins mvlut64 = {FUNC_MVLUT64};
    bins neg     = {FUNC_NEG};
    bins recip   = {FUNC_RECIP};
    bins rsqrt   = {FUNC_RSQRT};
    bins sqrt    = {FUNC_SQRT};
    bins sin     = {FUNC_SIN};
    bins cos     = {FUNC_COS};
    bins log2    = {FUNC_LOG2};
    bins exp2    = {FUNC_EXP2};
    bins maxr    = {FUNC_MAXR};
    bins minr    = {FUNC_MINR};
    bins sumr    = {FUNC_SUMR};
  }
  
  cp_unary_mv : coverpoint op iff (op == OPC_MV);

  cp_binary_lut : coverpoint func iff (op == OPC_LUT) {
    bins lut   = {FUNC_LUT};
    bins dlut  = {FUNC_DLUT};
    bins cllut = {FUNC_CLLUT};
    bins chlut = {FUNC_CHLUT};
  }
 
  cp_binary_rfs : coverpoint func iff (op == OPC_RFS) {
    bins neg   = {FUNC_NEG};
    bins recip = {FUNC_RECIP};
    bins rsqrt = {FUNC_RSQRT};
    bins sqrt  = {FUNC_SQRT};
    bins sin   = {FUNC_SIN};
    bins cos   = {FUNC_COS};
    bins log2  = {FUNC_LOG2};
    bins exp2  = {FUNC_EXP2};
    bins maxr  = {FUNC_MAXR};
    bins minr  = {FUNC_MINR};
    bins sumr  = {FUNC_SUMR};
    bins lut   = {FUNC_LUT};
    bins dlut  = {FUNC_DLUT};
    bins cllut = {FUNC_CLLUT};
    bins chlut = {FUNC_CHLUT};
    bins mv    = {FUNC_MV};
    bins mul   = {FUNC_MUL};
    bins add   = {FUNC_ADD};
    bins sub   = {FUNC_SUB};
    bins max   = {FUNC_MAX};
    bins min   = {FUNC_MIN};
    bins prelu = {FUNC_PRELU};
    bins cmadd = {FUNC_CMADD};
  }

  cp_binary_off_broad : coverpoint op iff (op inside {[OPC_MUL : OPC_CMADD]}) {
    bins mul   = {OPC_MUL};
    bins add   = {OPC_ADD};
    bins sub   = {OPC_SUB};
    bins max   = {OPC_MAX};
    bins min   = {OPC_MIN};
    bins prelu = {OPC_PRELU};
    bins cmadd = {OPC_CMADD};
    bins madd  = {OPC_MADD};
  }

  cp_ternary_op : coverpoint op iff (op inside {[OPC_MADD : OPC_MADD_RFS]}){
    bins madd     = {OPC_MADD};
    bins madd_rfs = {OPC_MADD_RFS};
  }      

  //TODO: implement specific custom pseudo commands
  cp_pseudo_op : coverpoint op iff (op inside {OPC_PSEUDO}) {
    bins pseudo = {OPC_PSEUDO};
  }      

  cp_mv_mask_value : coverpoint mask_value iff (op == OPC_MV) {
    bins const_zero    = {7'h0};
    bins const_one     = {7'h1};
    bins const_negzero = {7'h2};
    bins const_negone  = {7'h3};
    bins const_inf     = {7'h4};
    bins const_neginf  = {7'h5};
    bins const_pi      = {7'h6};
    bins const_2pi     = {7'h7};
  }

  cp_mask_size_pword64 : coverpoint mask_size iff (pword32 == 0 && op inside {[OPC_UNARY : OPC_MV]}) {
    bins bottom_most        = {63};
    bins top_most           = {-64};
    bins zero               = {0};
    bins mid_zero_bottom[2] = {[1:62]};
    bins mid_zero_top[2]    = {[-63:-1]};
  }

  cp_mask_size_pword32 : coverpoint mask_size iff (pword32 == 1 && op inside {[OPC_UNARY : OPC_MV]}) {
    bins bottom_most        = {31};
    bins top_most           = {-32};
    bins zero               = {0};
    bins mid_zero_bottom[2] = {[1:30]};
    bins mid_zero_top[2]    = {[-31:-1]};
  }

  cp_offset : coverpoint loop_select iff (offset_broadcast == 1 && op inside {[OPC_MUL : OPC_CMADD]}){
    bins loop_main     =  {0};
    bins loop_nested_0 =  {1};
    bins loop_nested_1 =  {2};
  }  

  cp_broadcast : coverpoint loop_select iff (offset_broadcast == 3 && op inside {[OPC_MUL : OPC_CMADD]}){
    bins loop_main     =  {0};
    bins loop_nested_0 =  {1};
    bins loop_nested_1 =  {2};
  }  

  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //data types
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  cp_data_int8 : coverpoint dt iff (src == i1 && !pword32) {
    bins random[4] = {[1 : 255]};
  }

  cp_data_int16 : coverpoint dt iff (src inside {i1_i16, pi1_i16}) {
    bins random[4] = {[1 : 65535]};
  }

  cp_data_int32 : coverpoint dt iff (src == i0 && !pword32) {
    bins random[4] = {[1 : 32'hFFFF_FFFF]};
  }

  cp_data_int48 : coverpoint dt iff (src inside {i0_i48, pi0_i48}) {
    bins random[4] = {[1 : 48'hFFFF_FFFF_FFFF]};
  }

  cp_data_int16_pword32 : coverpoint dt iff (src == i1 && pword32) {
    bins random[4] = {[1 : 65535]};
  }

  cp_data_int48_pword32 : coverpoint dt iff (src == i0 && pword32) {
    bins random[4] = {[1 : 48'hFFFF_FFFF_FFFF]};
  }


  cp_data_i0_f16 : coverpoint dt iff (src inside {i0_f16, pi0_f16}) {
    bins pos_nan          = {['h7C01: 'h7FFF]};
    bins neg_nan          = {['hFC01: 'hFCFF]};
    bins inf              = {'h7F00};
    bins neg_inf          = {'hFF00};
    bins neg_zero         = {'h8000};
    bins pos_normal[4]    = {['h400:'h7BFF]};
    bins neg_normal[4]    = {['h8400:'hFBFF]};
    bins pos_subnormal[4] = {['h1:'h3FF]};
    bins neg_subnormal[4] = {['h8001:'h83FF]};
  }

  cp_data_i0_f24 : coverpoint dt iff (src inside {i0_f24, pi0_f24}) {
    bins pos_nan          = {['h7F8001: 'h7FFFFF]};
    bins neg_nan          = {['hFF8001: 'hFFFFFF]};
    bins inf              = {'h7F8000};
    bins neg_inf          = {'hFF8000};
    bins neg_zero         = {'h800000};
    bins pos_normal[4]    = {['h8000:'h7F7FFF]};
    bins neg_normal[4]    = {['h808000:'hFF7FFF]};
    bins pos_subnormal[4] = {['h1:'h7FFF]};
    bins neg_subnormal[4] = {['h800001:'h807FFF]};
  }

  cp_data_i0_f32 : coverpoint dt iff (src inside {i0_f32, pi0_f32}) {
    bins pos_nan          = {['h7F80_0001 : 'h7FFF_FFFF]};
    bins neg_nan          = {['hFF80_0001 : 'hFFFF_FFFF]};
    bins inf              = {'h7F80_0000};
    bins neg_inf          = {'hFF80_0000};
    bins neg_zero         = {'h8000_0000};
    bins pos_normal[4]    = {['h80_0000:'h7F7F_FFFF]};
    bins neg_normal[4]    = {['h8080_0000:'hFF7F_FFFF]};
    bins pos_subnormal[4] = {['h1:'h7F_FFFF]};
    bins neg_subnormal[4] = {['h8000_0001:'h807F_FFFF]};
  }

  cp_data_i0_bp : coverpoint dt iff (src == i0_bp) {
    bins random[4] = {[1 : 32'hFFFF_FFFF]};
  }

  cp_data_i1_f16 : coverpoint dt iff (src inside {i1_f16, pi1_f16}) {
    bins pos_nan          = {['h7C01: 'h7CFF]};
    bins neg_nan          = {['hFC01: 'hFCFF]};
    bins inf              = {'h7F00};
    bins neg_inf          = {'hFF00};
    bins neg_zero         = {'h8000};
    bins pos_normal[4]    = {['h400:'h7BFF]};
    bins neg_normal[4]    = {['h8400:'hFBFF]};
    bins pos_subnormal[4] = {['h1:'h3FF]};
    bins neg_subnormal[4] = {['h8001:'h83FF]};
  }

  cp_data_i1_f24 : coverpoint dt iff (src inside {i1_f24, pi1_f24}) {
    bins pos_nan          = {['h7F8001: 'h7FFFFF]};
    bins neg_nan          = {['hFF8001: 'hFFFFFF]};
    bins inf              = {'h7F8000};
    bins neg_inf          = {'hFF8000};
    bins neg_zero         = {'h800000};
    bins pos_normal[4]    = {['h8000:'h7F7FFF]};
    bins neg_normal[4]    = {['h808000:'hFF7FFF]};
    bins pos_subnormal[4] = {['h1:'h7FFF]};
    bins neg_subnormal[4] = {['h800001:'h807FFF]};
  }

  cp_data_i1_f32 : coverpoint dt iff (src inside {i1_f32, pi1_f32}) {
    bins pos_nan          = {['h7F80_0001 : 'h7FFF_FFFF]};
    bins neg_nan          = {['hFF80_0001 : 'hFFFF_FFFF]};
    bins inf              = {'h7F80_0000};
    bins neg_inf          = {'hFF80_0000};
    bins neg_zero         = {'h8000_0000};
    bins pos_normal[4]    = {['h80_0000:'h7F7F_FFFF]};
    bins neg_normal[4]    = {['h8080_0000:'hFF7F_FFFF]};
    bins pos_subnormal[4] = {['h1:'h7F_FFFF]};
    bins neg_subnormal[4] = {['h8000_0001:'h807F_FFFF]};
  }

  cp_data_i1_bp : coverpoint dt iff (src == i1_bp) {
    bins random[4] = {[1 : 255]};
  }

endgroup


covergroup cvg_out_data with function sample (dst_t dst, opcode_e op, bit pword32, bit [31:0] dt);
  option.per_instance = 1'b1;
  option.name         = "cvg_out_data";

  cp_data_int8 : coverpoint dt iff ((dst == o || dst == l) && !pword32) {
    bins random[4] = {[1 : 255]};
  }

  cp_data_int16 : coverpoint dt iff ((dst == o_i16 || dst == l_i16) && !pword32) {
    bins random[4] = {[1 : 65535]};
  }

  cp_data_int16_pword32 : coverpoint dt iff ((dst == o || dst == l) && pword32) {
    bins random[4] = {[1 : 65535]};
  }

  cp_data_f16 : coverpoint dt iff (dst == o_f16 || dst == l_f16) {
    bins pos_nan          = {['h7C01: 'h7CFF]};
    bins neg_nan          = {['hFC01: 'hFCFF]};
    bins inf              = {'h7F00};
    bins neg_inf          = {'hFF00};
    bins neg_zero         = {'h8000};
    bins pos_normal[4]    = {['h400:'h7BFF]};
    bins neg_normal[4]    = {['h8400:'hFBFF]};
    bins pos_subnormal[4] = {['h1:'h3FF]};
    bins neg_subnormal[4] = {['h8001:'h83FF]};
  }

  cp_data_f24 : coverpoint dt iff (dst == o_f24 || dst == l_f24) { 
    bins pos_nan          = {['h7F8001: 'h7FFFFF]};
    bins neg_nan          = {['hFF8001: 'hFFFFFF]};
    bins inf              = {'h7F8000};
    bins neg_inf          = {'hFF8000};
    bins neg_zero         = {'h800000};
    bins pos_normal[4]    = {['h8000:'h7F7FFF]};
    bins neg_normal[4]    = {['h808000:'hFF7FFF]};
    bins pos_subnormal[4] = {['h1:'h7FFF]};
    bins neg_subnormal[4] = {['h800001:'h807FFF]};
  }

  cp_data_f32 : coverpoint dt iff (dst == o_f32 || dst == l_f32) {
    bins pos_nan          = {['h7F80_0001 : 'h7FFF_FFFF]};
    bins neg_nan          = {['hFF80_0001 : 'hFFFF_FFFF]};
    bins inf              = {'h7F80_0000};
    bins neg_inf          = {'hFF80_0000};
    bins neg_zero         = {'h8000_0000};
    bins pos_normal[4]    = {['h80_0000:'h7F7F_FFFF]};
    bins neg_normal[4]    = {['h8080_0000:'hFF7F_FFFF]};
    bins pos_subnormal[4] = {['h1:'h7F_FFFF]};
    bins neg_subnormal[4] = {['h8000_0001:'h807F_FFFF]};
  }

  cp_data_bp : coverpoint dt iff (dst == o_bp || dst == l_bp) {
    bins random[4] = {[1 : 255]};
  }

endgroup

//generic covergroup to cover all the interrupts
covergroup cvg_dpu_irq (string cg_name) with function sample(bit irq);
  option.per_instance = 1'b1;
  option.name = cg_name;

  cp_irq : coverpoint irq {
    bins no_irq = {0};
    bins irq    = {1};
  }
endgroup : cvg_dpu_irq

class dpu_func_cov extends uvm_component;
  `uvm_component_utils(dpu_func_cov)

  svt_axi_transaction cfg_item;
  token_agent_seq_item tok_mon_item;

  uvm_tlm_analysis_fifo #(svt_axi_transaction) taf_mon_cfg;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok;

  dpu_pkg::dpu_dp_cmd_t instr;
  dp_ctrl_reg_t dp_ctrl_reg;
  dpu_irq_reg_t irq_en_reg;
  dpu_irq_reg_t irq_status_reg;
  bit in_irq_en;
  bit out_irq_en;
  bit exec_en;
  bit i0_int_sgn = 1;
  bit i1_int_sgn = 1;
  bit out_int_sgn = 1;
  int cmd_cnt = 0;
  bit header_received;
  dpu_cmd_header_t header;
  dpu_irq_bit_pos_t irq_pos;

  cvg_dpu_irq cvg_dpu_irq[string];

  DPU_RAL regmodel;
  // Covergroup for dpu instructions
  covergroup cvg_dpu_instr;
    option.per_instance = 1'b1;
    option.name = "cvg_dpu_instr";
    // Coverpoints for src0
    cp_src0: coverpoint instr.src0 {
      bins acc0_7            = {[a0 : a7]};
      bins b_c_reg0_63       = {[b_c0 : b_c63]};
      bins i0_stream[6]      = {[i0 : i0_f24]};
      bins i1_stream[6]      = {[i1 : i1_f24]};
      bins peek_i0_stream[6] = {[pi0 : pi0_f24]};
      bins peek_i1_stream[6] = {[pi1 : pi1_f24]};
    }
    // Coverpoints for src1
    cp_src1: coverpoint instr.src1 {
      bins acc0_7            = {[a0 : a7]};
      bins b_c_reg0_63       = {[b_c0 : b_c63]};
      bins i0_stream[6]      = {[i0 : i0_f24]};
      bins i1_stream[6]      = {[i1 : i1_f24]};
      bins peek_i0_stream[6] = {[pi0 : pi0_f24]};
      bins peek_i1_stream[6] = {[pi1 : pi1_f24]};
    }
    // Coverpoints for src2
    cp_src2: coverpoint instr.src2 {
      bins acc0_7            = {[a0 : a7]};
      bins b_c_reg0_63       = {[b_c0 : b_c63]};
      bins i0_stream[6]      = {[i0 : i0_f24]};
      bins i1_stream[6]      = {[i1 : i1_f24]};
      bins peek_i0_stream[6] = {[pi0 : pi0_f24]};
      bins peek_i1_stream[6] = {[pi1 : pi1_f24]};
    }
    // Coverpoints for destination
    cp_dst: coverpoint instr.dst {
      bins acc0_7          = {[dst_a0 : dst_a7]};
      bins b_c_reg0_63     = {[dst_b_c0 : dst_b_c63]};
      bins out_stream[6]   = {[o : o_f24]};
      bins out_l_stream[6] = {[l : l_f24]};
    }


    //cover if input and output integer data are treated as signed/unsigned
    cp_i0_int_sgn: coverpoint i0_int_sgn iff (instr.src0 == i0 ||
                                              instr.src1 == i0 ||
                                              instr.src2 == i0 ) {
      bins i0_int_signed_off = {0}; bins i0_int_signed_on = {1};
    }

    cp_i1_int_sgn: coverpoint i1_int_sgn iff (instr.src0 == i1  ||
                                              instr.src1 == i1  ||
                                              instr.src2 == i1 ) {
      bins i1_int_signed_off = {0}; bins i1_int_signed_on = {1};
    }

    cp_out_int_sgn: coverpoint out_int_sgn iff (instr.dst inside {o, l} ) {
      bins out_int_signed_off = {0}; bins out_int_signed_on = {1};
    }


  endgroup : cvg_dpu_instr


  covergroup cvg_dpu_tok with function sample(token_agent_seq_item a_trans);
    option.per_instance = 1'b1;
    option.name         = "cvg_dpu_tok";

    cp_type : coverpoint (a_trans.m_type_enm) {
      bins cons = {1};
      bins prod = {2};
    }

    cp_prod_delay : coverpoint (a_trans.m_bv_delay) iff (a_trans.m_type_enm == 2) {
      bins delay[3] = {[0:9]};
    }
  endgroup


  // This function initializes an instance of the class with the given name and parent.
  function new(string name, uvm_component parent);
    super.new(name, parent);
    cvg_dpu_instr = new();
    cvg_dpu_tok   = new();

    for (int i = 0; i < irq_pos.num(); i++) begin
      cvg_dpu_irq[irq_pos.name()] = new ($sformatf("cvg_dpu_irq_%s", irq_pos.name()));
      irq_pos = irq_pos.next();
    end
  endfunction


  // This function is called during the build phase of the UVM environment.
  // It creates necessary objects and components.
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg_item          = new("cfg_item");
    taf_mon_cfg       = new("taf_mon_cfg", this);
    taf_mon_tok       = new("taf_mon_tok", this);
  endfunction : build_phase
  // This task is called during the run phase of the UVM environment.
  // It contains multiple forever loops that continuously sample data.
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      // Sample cfg data and decode the address.
      forever begin
        taf_mon_cfg.get(cfg_item);
        for (int i = 0; i < cfg_item.data.size(); i++) begin
          decode_addr(cfg_item.addr, cfg_item.data[i]);
        end
      end

      forever begin
        taf_mon_tok.get(tok_mon_item);
        //sample token covergroup
        cvg_dpu_tok.sample(tok_mon_item);
      end

    join
  endtask : run_phase


  task decode_addr(bit [27:0] addr, bit_dw_t data);
    `uvm_info("dpu_mdl", $sformatf("Decoding addr: %0h, data: %0h", addr, data), UVM_HIGH)
    //dpu_csr
    if (addr == regmodel.dp_ctrl.get_address()) 
      dp_ctrl_reg = data;
    else if (addr == regmodel.irq_en.get_address())
      irq_en_reg = data;
    else if (addr == regmodel.irq_status.get_address()) begin
      irq_status_reg = data;
      irq_pos = dpu_irq_bit_pos_t'(0);
      for (int i = 0; i < irq_pos.num(); i++) begin
        if (irq_en_reg[irq_pos])
          cvg_dpu_irq[irq_pos.name()].sample(irq_status_reg[irq_pos]);
        irq_pos.next();
      end
    end
    else if (addr inside {[DPU_PRG_ADDR_ST:DPU_PRG_ADDR_END]}) begin
      instr = data;
      cvg_dpu_instr.sample();
    end
    else if (addr inside {[DPU_CMD_ADDR_ST : DPU_CMD_ADDR_END]}) begin
      header = data;
      //HEADER + COMMAND
//      if (header_received)
//        decode_cmd(data);
//      else begin
//        header_received = 1;
//        decode_header(data);
//      end
    end
  endtask : decode_addr


  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_full_name(), $sformatf(
              "cvg_dpu_instr: %.2f%% \ncvg_dpu_tok: %.2f%%",
               cvg_dpu_instr.get_coverage(),
               cvg_dpu_tok.get_coverage()
               ), UVM_LOW)
  endfunction : report_phase


endclass

`endif
