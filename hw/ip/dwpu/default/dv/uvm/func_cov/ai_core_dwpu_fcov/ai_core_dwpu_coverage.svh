`ifndef AI_CORE_DWPU_COVERAGE_SV
`define AI_CORE_DWPU_COVERAGE_SV


covergroup ai_core_dwpu_image_reg_cg (string cg_name) with function sample(bit [I_SEL_WIDTH-1:0] i_sel);
  option.per_instance = 1'b1;
  option.name         = cg_name;
  cp_image_reg : coverpoint i_sel {
    bins absorbing_element = {0};
    bins input_data        = {1};
    bins sp_regs[2]        = {[2:126]};
  }
endgroup

covergroup ai_core_dwpu_weight_reg_cg (string cg_name) with function sample(bit [W_SEL_WIDTH-1:0] w_sel);
  option.per_instance = 1'b1;
  option.name         = cg_name;
  cp_weight_reg : coverpoint w_sel {
    bins weight_buffer[4] = {[0:63]};
  }
endgroup

class ai_core_dwpu_coverage extends uvm_component;
  `uvm_component_utils(ai_core_dwpu_coverage)

  // AI Core DWPU RAL Model
  DWPU_RAL regmodel;

  svt_axi_transaction cfg_item;
  svt_axi_transaction cfg_item_aux;
  svt_axi_transaction in_data_item;
  svt_axi_transaction out_data_item;
  ai_core_dwpu_seq_item dwpu_item;
  token_agent_seq_item tok_mon_item;

  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_cfg;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_data;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_data_out;
  uvm_tlm_analysis_fifo#(ai_core_dwpu_seq_item) taf_mdl_dwpu;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok;

  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb cmd2sample;
  bit [DWPU_CMD_MEM_WIDTH-1:0] aux_cmd;
  dwpu_dp_command_t instr;
  // declare variables that are used in the decode of the instructions and commands
  bit weight_sign = 1;
  bit image_sign  = 1;
  bit skip_illegal_prog;
  int instr_cnt;
  int cmd_cnt;
  dwpu_cmd_header_t header2sample;
  bit header_received;
  int instr_pos;
  int prev_instr_pos;
  int prev_last_push = -1;
  bit last_push__on_pos_diff_from_last_instr;

  //declare variables that are related with interrupts
  dwpu_irq_t irq_type;
  //declare variables that related with AXI configuration transaction
  int num_of_cmds_on_same_burst;
  //declare variables that are related with command decoding
  int cmd_num_rows;

  ai_core_dwpu_image_reg_cg  ai_core_dwpu_image_reg_cg[NUM_OPERANDS];
  ai_core_dwpu_weight_reg_cg ai_core_dwpu_weight_reg_cg[NUM_OPERANDS];

  covergroup ai_core_dwpu_data_in_cg with function sample(bit [DWPU_IN_WORD_DW-1:0] data);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_data_in_cg";
    cp_data : coverpoint data {
      bins min = {0};
      bins between = {[1:254]};
      bins max = {255};
    }
  endgroup

  covergroup ai_core_dwpu_cmd_cg;
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_cmd_cg";

    cp_skip_illegal_prog : coverpoint (skip_illegal_prog) {
      bins skip_disabled = {0};
      bins skip_enabled  = {1};
    }

    cp_format : coverpoint (header2sample.format);

    cp_format_transitions : coverpoint (header2sample.format) {
      bins transitions [] = ([aic_dp_cmd_gen_pkg::LoopsM1N0:aic_dp_cmd_gen_pkg::Bypass] => [aic_dp_cmd_gen_pkg::LoopsM1N0:aic_dp_cmd_gen_pkg::Bypass]);
    }
  endgroup

  /** ai_core_dwpu_instr_cg is the covergroup that will aggregate the information regarding instruction that was requested to be run on DWPU */
  covergroup ai_core_dwpu_instr_cg with function sample(dwpu_dp_command_t instr);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_instr_cg";

    cp_op_exe : coverpoint (instr.op_desc.op_exe) {
      bins inactive = {0};
      bins active = {1};
    }
    cp_shift_sp : coverpoint (instr.op_desc.shift_sp) {
      bins false = {0};
      bins true = {1};
    }
    cp_shift_wb : coverpoint (instr.op_desc.shift_wb) {
      bins false = {0};
      bins true = {1};
    }
    cp_opcode : coverpoint (instr.op_desc.opcode);

    cp_weight_sign : coverpoint weight_sign {
      bins signed_off = {0};
      bins signed_on  = {1};
    }

    cp_image_sign : coverpoint image_sign {
      bins signed_off = {0};
      bins signed_on  = {1};
    }

    cp_last_push : coverpoint instr.op_desc.last_push;

    cp_i_sel0 : coverpoint (instr.i_sel[0]) {
      bins absorbing_element = {0};
      bins input_data        = {1};
      bins sp_regs[2]        = {[2:126]};
    }

    cp_last_push__on_pos_diff_from_last_instr : coverpoint last_push__on_pos_diff_from_last_instr;

    cc_op_exe__shift_sp__shif_wb__opcode_i_sel0__last_push : cross cp_op_exe, cp_shift_sp, cp_shift_wb, cp_opcode, cp_i_sel0, cp_last_push;
    cc_opcode__weight_sign__image_sign : cross cp_opcode, cp_weight_sign, cp_image_sign;
  endgroup : ai_core_dwpu_instr_cg

  /** ai_core_dwpu_cmd_axi_info_cg is the covergroup that will aggregate the information regarding command from DWPU */
  covergroup ai_core_dwpu_cmd_axi_info_cg with function sample(int burst_length);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_cmd_axi_info_cg";

    cp_burst_length : coverpoint (burst_length) {
      bins length_1_to_max_of_fifo[5] = {[1: aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH*3]}; //3 was the value defined here https://git.axelera.ai/prod/europa/-/issues/1890
    }

    cp_num_of_cmds_on_same_burst : coverpoint num_of_cmds_on_same_burst {
      bins one = {1};
      bins two_or_more = {[2 : aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH]};
    }

  endgroup : ai_core_dwpu_cmd_axi_info_cg

  /** ai_core_dwpu_prg_axi_info_cg is the covergroup that will aggregate the information regarding program that was will be run on DWPU */
  covergroup ai_core_dwpu_prg_axi_info_cg with function sample(svt_axi_transaction trans);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_prg_axi_info_cg";

    cp_xact_type : coverpoint (trans.xact_type) {
      bins wr = {svt_axi_transaction::WRITE};
      bins rd = {svt_axi_transaction::READ};
      bins wr_rd = ({svt_axi_transaction::WRITE} => {svt_axi_transaction::READ});
      bins rd_wr = ({svt_axi_transaction::READ} => {svt_axi_transaction::WRITE});
    }

    cp_addr : coverpoint(trans.addr) {
      bins min = {DWPU_IMEM_ST_ADDR};
      bins midle_accessible[10] = {[DWPU_IMEM_ST_ADDR: (DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AIC_LT_AXI_DATA_WIDTH)/8) - 8)]};
      bins midle_not_accessible[10] = {[DWPU_IMEM_ST_ADDR+((INSTR_MEM_DEPTH*DWPU_INSTR_NUM_ROWS*AIC_LT_AXI_DATA_WIDTH)/8): (DWPU_IMEM_END_ADDR - 15)]};
      bins max = {DWPU_IMEM_END_ADDR-7};
    }

    cp_burst_length : coverpoint (trans.burst_length) {
      bins min_to_max[8] = {[1:255]};
      bins max = {256};
    }
  endgroup : ai_core_dwpu_prg_axi_info_cg

  /** ai_core_dwpu_loop_info_cg is the covergroup that will aggregate the information regarding command that was requested to be run on DWPU */
  covergroup ai_core_dwpu_loop_info_cg with function sample();
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_loop_info_cg";

    cp_has_main_0 : coverpoint (cmd2sample.main_valid(0)) {
      bins false = {0};
      bins true = {1};
    }
    cp_has_main_1 : coverpoint (cmd2sample.main_valid(1)) {
      bins false = {0};
      bins true = {1};
    }
    cp_has_main_2 : coverpoint (cmd2sample.main_valid(2)) {
      bins false = {0};
      bins true = {1};
    }
    cp_has_nested_0 : coverpoint (cmd2sample.nested_valid(0)) {
      bins false = {0};
      bins true = {1};
    }
    cp_has_nested_1 : coverpoint (cmd2sample.nested_valid(1)) {
      bins false = {0};
      bins true = {1};
    }
    cp_co_nested_loops : coverpoint (cmd2sample.co_nested()) {
      bins false = {0};
      bins true = {1};
    }
    cp_parallel_loops : coverpoint (cmd2sample.is_parallel()) {
      bins false = {0};
      bins true = {1};
    }
    cc_co_nested_parallel_loops : cross cp_co_nested_loops, cp_parallel_loops;

  endgroup : ai_core_dwpu_loop_info_cg

  /** ai_core_dwpu_irq_cg is the covergroup that will aggregate the information regarding interruptions that were triggered on DWPU */
  covergroup ai_core_dwpu_irq_cg with function sample();
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_irq_cg";

    cp_irq : coverpoint irq_type;

  endgroup : ai_core_dwpu_irq_cg

  /** ai_core_dwpu_tok_cg is the covergroup that will aggregate the information regarding token consumed on DWPU */
  covergroup ai_core_dwpu_tok_cg with function sample(token_agent_seq_item trans);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_tok_cg";

    cp_delay : coverpoint (trans.m_bv_delay) {
      bins delay[10] = {[0:9]};
    }
    cp_type : coverpoint (trans.m_type_enm) {
      bins cons = {1};
      bins prod = {2};
    }

    cc_delay_type : cross cp_delay, cp_type;
  endgroup : ai_core_dwpu_tok_cg

  /** ai_core_dwpu_axis_in_cg is the covergroup that will aggregate the information regarding AXIS input stream on DWPU */
  covergroup ai_core_dwpu_axis_in_cg with function sample(svt_axi_transaction trans, int pos);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_axis_in_cg";

    cp_delay : coverpoint (trans.tvalid_delay[pos]) {
      bins delay[10] = {[0:16]};
    }
  endgroup : ai_core_dwpu_axis_in_cg

  /** ai_core_dwpu_axis_out_cg is the covergroup that will aggregate the information regarding AXIS output stream on DWPU */
  covergroup ai_core_dwpu_axis_out_cg with function sample(svt_axi_transaction trans, int pos);
    option.per_instance = 1'b1;
    option.name         = "ai_core_dwpu_axis_out_cg";

    cp_delay : coverpoint (trans.tready_delay[pos]) {
      bins delay[10] = {[0:1000]};
    }
  endgroup : ai_core_dwpu_axis_out_cg

  function new(string name, uvm_component parent);
    super.new(name,parent);
    ai_core_dwpu_cmd_cg   = new();
    ai_core_dwpu_cmd_axi_info_cg = new();
    ai_core_dwpu_prg_axi_info_cg = new();
    ai_core_dwpu_loop_info_cg = new();
    ai_core_dwpu_instr_cg = new();
    ai_core_dwpu_irq_cg = new();
    ai_core_dwpu_tok_cg = new();
    ai_core_dwpu_axis_in_cg = new();
    ai_core_dwpu_axis_out_cg = new();
    foreach ( ai_core_dwpu_image_reg_cg[i]  ) ai_core_dwpu_image_reg_cg[i]  = new($sformatf("ai_core_dwpu_image_reg_cg[%0d]",i)) ;
    foreach ( ai_core_dwpu_weight_reg_cg[i] ) ai_core_dwpu_weight_reg_cg[i] = new($sformatf("ai_core_dwpu_weight_reg_cg[%0d]",i)) ;
    ai_core_dwpu_data_in_cg = new();

  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg_item         = svt_axi_transaction::type_id::create("cfg_item");
    cfg_item_aux     = svt_axi_transaction::type_id::create("cfg_item_aux");
    in_data_item     = svt_axi_transaction::type_id::create("in_data_item");
    out_data_item    = svt_axi_transaction::type_id::create("out_data_item");
    taf_mon_cfg      = new("taf_mon_cfg", this);
    taf_mon_data     = new("taf_mon_data", this);
    taf_mon_data_out = new("taf_mon_data_out", this);
    taf_mdl_dwpu     = new("taf_mdl_dwpu", this);
    taf_mon_tok      = new("taf_mon_tok", this);
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      forever begin
        taf_mon_cfg.get(cfg_item_aux);
        cfg_item.do_copy(cfg_item_aux);
        //reset command counter;
        num_of_cmds_on_same_burst = 0;
        //decode every word
        foreach (cfg_item.data[i]) begin
          decode_addr(cfg_item, i);
          if (cfg_item.burst_type != svt_axi_transaction::FIXED)
            cfg_item.addr+=8;
        end
      end
      forever begin
        taf_mon_data.get(in_data_item);
        sample_in_data(in_data_item);
      end
      forever begin
        taf_mon_data_out.get(out_data_item);
        sample_out_data(out_data_item);
      end
      forever begin
        taf_mdl_dwpu.get(dwpu_item);
        if(dwpu_item.irq_o) irq_type = dwpu_item.irq_type;

        //sample irq covergroup
        ai_core_dwpu_irq_cg.sample();
      end
      forever begin
        taf_mon_tok.get(tok_mon_item);
        //sample token covergroup
        ai_core_dwpu_tok_cg.sample(tok_mon_item);
      end
    join
  endtask : run_phase

  function void decode_header_cmd (bit [AIC_LT_AXI_DATA_WIDTH-1:0] data);
    /** save data into header2sample that will be used to collect coverage */
    header2sample = data;

    if (header2sample.format == aic_dp_cmd_gen_pkg::Bypass) begin
      ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb empty_cmd = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb::type_id::create("empty_cmd");
      cmd2sample=empty_cmd;
      // since the bypass command is only the header, means that the next command will start again with the header. So reset header_received variable.
      header_received = 0;
      //sample command with nothing on it
      ai_core_dwpu_cmd_cg.sample();
    end

    cmd_num_rows = ai_core_dwpu_utils::get_cmd_num_rows(header2sample.format);

    /** Increment counter that saves the amount of commands on a single burst */
    num_of_cmds_on_same_burst++;

  endfunction : decode_header_cmd

  function void decode_cmd (bit [AIC_LT_AXI_DATA_WIDTH-1:0] data);
    aux_cmd[AIC_LT_AXI_DATA_WIDTH * cmd_cnt++ +: AIC_LT_AXI_DATA_WIDTH] = data;

    if (cmd_cnt == cmd_num_rows) begin
      cmd2sample = ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_utils::get_full_cmd_from_alternative_cmd(aux_cmd, header2sample.format);

      /** assign global variables that specify the different regions of program */
      `uvm_info("dwpu_cov", $sformatf("loop_info: %s", cmd2sample.sprint()), UVM_HIGH)

      ai_core_dwpu_loop_info_cg.sample();
      /**reset counter that saves the number of words */
      cmd_cnt = 0;
      header_received = 0;
      `uvm_info("dwpu_cov", $sformatf("cmd: %0p", cmd2sample), UVM_HIGH)
    end
  endfunction : decode_cmd


  function void decode_addr(svt_axi_transaction trans, int pos);
    bit [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] l_addr;
    bit [AIC_LT_AXI_DATA_WIDTH-1:0] l_data;
    /** udpate local variables address and data */
    l_addr= trans.addr;
    l_data = trans.data[pos];
    `uvm_info("dwpu_cov", $sformatf("Decoding addr: %0h, data: %0h", l_addr, l_data), UVM_HIGH)

    //dwpu_csr
    if (l_addr == regmodel.dp_ctrl.get_address()) begin
      weight_sign       = l_data[0];
      image_sign        = l_data[1];
      skip_illegal_prog = l_data[2];
    end else if (l_addr inside {[DWPU_IMEM_ST_ADDR : DWPU_IMEM_END_ADDR]}) begin
      /** if it is the first position of the transaction and it is an instruction then call sample of ai_core_dwpu_prg_axi_info_cg */
      if(pos==0) begin
        ai_core_dwpu_prg_axi_info_cg.sample(trans);
      end
      if (trans.xact_type == svt_axi_transaction::WRITE) begin
        //cmdgen
        instr[AIC_LT_AXI_DATA_WIDTH * instr_cnt++ +: AIC_LT_AXI_DATA_WIDTH] = l_data;
        if (instr_cnt == DWPU_INSTR_NUM_ROWS) begin
          //remove the base address from program memory
          instr_cnt = 0;
          `uvm_info("dwpu_cov", $sformatf("instr: %p", instr), UVM_HIGH)
          //find if the last_push signalization is done on an instruction different from the last of the program
          instr_pos = (l_addr - DWPU_IMEM_ST_ADDR) / DWPU_INSTR_BYTES;
          last_push__on_pos_diff_from_last_instr = (prev_last_push == -1) ? 0 : ((prev_last_push == 1) && (instr_pos == prev_instr_pos+1)) ? 1 : 0;
          prev_last_push = instr.op_desc.last_push;
          prev_instr_pos = instr_pos;
          //call covergroups sampling
          ai_core_dwpu_instr_cg.sample(instr);
          foreach ( ai_core_dwpu_image_reg_cg[i]  ) ai_core_dwpu_image_reg_cg[i].sample(instr.i_sel[i]);
          foreach ( ai_core_dwpu_weight_reg_cg[i] ) ai_core_dwpu_weight_reg_cg[i].sample(instr.w_sel[i]);
        end
      end
    end else if (l_addr inside {[DWPU_CMD_ST_ADDR : DWPU_CMD_END_ADDR]}) begin
      if (trans.xact_type == svt_axi_transaction::WRITE) begin
        //HEADER + COMMAND
        if (header_received) begin
          decode_cmd(l_data);
          ai_core_dwpu_cmd_cg.sample();
        end else begin
          header_received = 1;
          decode_header_cmd(l_data);
        end
        /** after decoding the whole command call the sampling regarding all axi information */
        if(pos == cfg_item.data.size()-1) begin
          ai_core_dwpu_cmd_axi_info_cg.sample(trans.burst_length);
        end
      end
    end
  endfunction : decode_addr

  //covers only data of channel 0
  function void sample_in_data(svt_axi_transaction trans);
    foreach (trans.tdata[i]) begin
      ai_core_dwpu_data_in_cg.sample(trans.tdata[i][DWPU_IN_WORD_DW-1:0]);
      ai_core_dwpu_axis_in_cg.sample(trans, i);
    end
  endfunction

  function void sample_out_data(svt_axi_transaction trans);
    foreach (trans.tready_delay[i]) begin
      ai_core_dwpu_axis_out_cg.sample(trans, i);
    end
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_full_name(), $sformatf(
      "ai_core_dwpu_instr_cg: %.2f%% \nai_core_dwpu_cmd_cg: %.2f%%",
      ai_core_dwpu_instr_cg.get_coverage(), ai_core_dwpu_cmd_cg.get_coverage()
    ), UVM_LOW)
  endfunction : report_phase

endclass

`endif
