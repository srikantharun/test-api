`ifndef IAU_COVERAGE_SV
`define IAU_COVERAGE_SV

class iau_func_cov extends uvm_component;
  `uvm_component_utils(iau_func_cov)

  svt_axi_transaction cfg_item;
  token_agent_seq_item tok_mon_item;

  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_cfg;
  uvm_tlm_analysis_fifo#(svt_axi_transaction) taf_mon_data;
  uvm_tlm_analysis_fifo#(token_agent_seq_item) taf_mon_tok;

  IAU_RAL regmodel;
  iau_pkg::iau_cmd_t cmd;
  iau_common_pkg::iau_dp_cmd_t instr;
  bit header_received;
  bit signed_op = 1;
  bit sat_op;
  iau_cmd_header_t header;

  covergroup cvg_iau_op;
    option.per_instance = 1'b1;
    option.name         = "cvg_iau_op";
/*    cp_op : coverpoint header.cmd_format {
      bins bypass = {CMD_FORMAT_BYP};
      bins exe    = {CMD_FORMAT_EXE};
      bins bypass_to_exe = (CMD_FORMAT_BYP => CMD_FORMAT_EXE);
      bins exe_to_bypass = (CMD_FORMAT_EXE => CMD_FORMAT_BYP);
    }
    */
  endgroup

  covergroup cvg_iau_cmd;
    option.per_instance = 1'b1;
    option.name         = "cvg_iau_cmd";
/*
    //loopstart gh review
    cp_start_addr : coverpoint cmd.loop_start {
      bins between_0_max[2] = {[0:iau_pkg::IAU_PRG_MEM_DEPTH-2]};
      bins max     = {iau_pkg::IAU_PRG_MEM_DEPTH-1};
    }

    cp_loop_len : coverpoint cmd.loop_len {
      bins one = {1};
      bins between_2_200[2] = {[2:200]};
    }

    cp_loop_iter : coverpoint cmd.loop_iter {
      bins one = {1};
      bins between_2_100[2] = {[2:100]};
    }

    cr_loop_cmd : cross cp_loop_len, cp_loop_iter {
      ignore_bins ign_len_iter_1 = binsof(cp_loop_len.one) || binsof(cp_loop_iter.one);
    }
*/
  endgroup

  covergroup cvg_iau_instr;
    option.per_instance = 1'b1;
    option.name         = "cvg_iau_instr";

    cp_src0 : coverpoint instr.src0 {
      bins reg0   = {0};
      bins reg1_6 = {[1:6]};
      bins reg7   = {7};
      wildcard bins pop = {4'b1???};
    }

    cp_src1 : coverpoint instr.src1 {
      bins reg0   = {0};
      bins reg1_6 = {[1:6]};
      bins reg7   = {7};
      wildcard bins pop = {4'b1???};
    }

    cp_dst : coverpoint instr.dst {
      bins reg0   = {0};
      bins reg1_6 = {[1:6]};
      bins reg7   = {7};
      wildcard bins push = {4'b1??0};
      wildcard bins push_last = {4'b1??1};
    }

    cp_rfs : coverpoint instr.rfs {
      bins rfs_off = {0};
      bins rfs_on  = {1};
    }

    cp_op : coverpoint instr.opcode {
      bins op_nop      = {OP_NOP};
      bins op_mv       = {OP_MV};
      bins op_max      = {OP_MAX};
      bins op_min      = {OP_MIN};
      bins op_add      = {OP_ADD};
    }

    cp_op_transition: coverpoint instr.opcode {bins trans_mv_to_all = (OP_MV => OP_MAX,OP_MIN,OP_ADD);
      bins trans_add_to_all = (OP_ADD => OP_MV,OP_MAX,OP_MIN);
      bins trans_max_to_all = (OP_MAX => OP_MV,OP_MIN,OP_ADD);
      bins trans_min_to_all = (OP_MIN => OP_MV,OP_MAX,OP_ADD);
    }

    cp_signed : coverpoint signed_op {
      bins signed_off = {0};
      bins signed_on  = {1};
    }

    cp_saturation : coverpoint sat_op {
      bins sat_off = {0};
      bins sat_on  = {1};
    }

    cp_src0_less : coverpoint instr.src0 {
      bins regs = {[0:7]};
      wildcard bins pop = {4'b1???};
    }

    cp_src1_less : coverpoint instr.src1 {
      bins regs = {[0:7]};
      wildcard bins pop = {4'b1???};
    }

    cp_dst_less : coverpoint instr.dst {
      bins regs = {[0:7]};
      wildcard bins push_or_push_tlast = {4'b1???};
    }

    cr_single_source_instructions : cross cp_op, cp_src0_less, cp_dst_less {
      ignore_bins op_ign = !binsof(cp_op) intersect {OP_MV}; //mv
    }

    cr_dual_source_instructions : cross cp_op, cp_src0_less, cp_src1_less, cp_dst_less {
      ignore_bins op_ign = !binsof(cp_op) intersect {[OP_MAX:OP_ADD]}; //add,max,min
    }

    cr_signed_sat_dual_source_instructions : cross cp_op, cp_signed, cp_saturation {
      ignore_bins op_ign = !binsof(cp_op) intersect {[OP_MAX:OP_ADD]}; //add,max,min
    }

    cr_instructions_rfs_on : cross cp_op, cp_dst_less iff (instr.rfs == 1) {
      ignore_bins op_ign = binsof(cp_op) intersect {OP_NOP};
      ignore_bins mv_ign = binsof(cp_op) intersect {OP_MV} && !binsof(cp_dst_less) intersect {[0:7]}; 
    }

  endgroup

  covergroup cvg_iau_tok with function sample(token_agent_seq_item a_trans);
    option.per_instance = 1'b1;
    option.name         = "cvg_iau_tok";

    cp_type : coverpoint (a_trans.m_type_enm) {
      bins cons = {1};
      bins prod = {2};
    }

    cr_prod_delay : coverpoint (a_trans.m_bv_delay) iff (a_trans.m_type_enm == 2) {
      bins delay[6] = {[0:9]};
    }

  endgroup

  function new(string name, uvm_component parent);
    super.new(name,parent);
    cvg_iau_op    = new();
    cvg_iau_cmd   = new();
    cvg_iau_instr = new();
    cvg_iau_tok   = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg_item      = new("cfg_item");
    taf_mon_cfg   = new("taf_mon_cfg", this);
    taf_mon_data   = new("taf_mon_data", this);
    taf_mon_tok   = new("taf_mon_tok", this);
  endfunction : build_phase


  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      forever begin
        svt_axi_transaction item = new;;
        taf_mon_cfg.get(item);
        cfg_item.do_copy(item);

        if (cfg_item.addr inside {[IAU_CMD_BLOCK_ADDR_ST:IAU_CMD_BLOCK_ADDR_END]}) begin
          foreach (cfg_item.data[i]) begin
            int num_valid_writes = $countones(cfg_item.wstrb[i]) / 2;
            for (int j = 0; j < num_valid_writes; j++) begin
              decode_addr(cfg_item.addr, cfg_item.data[i][(j*16)+:16]);
              if (cfg_item.burst_type != svt_axi_transaction::FIXED)
                cfg_item.addr+=2;
            end
          end //foreach data
        end //if addr
        else begin
          foreach (cfg_item.data[i]) begin
            decode_addr(cfg_item.addr, cfg_item.data[i]);
            if (cfg_item.burst_type != svt_axi_transaction::FIXED)
              cfg_item.addr+=8;
          end
        end
      end
      forever begin
        taf_mon_tok.get(tok_mon_item);
        //sample token covergroup
        `uvm_info(get_name, $sformatf("token_item covered: %s", tok_mon_item.convert2string), UVM_HIGH)
        cvg_iau_tok.sample(tok_mon_item);
      end
    join
  endtask : run_phase

  function void decode_addr(bit [27:0] addr, bit_dw_t data);
    if (addr == regmodel.dp_ctrl.get_address()) begin
      signed_op = data[0];
      sat_op    = data[1];
    end else if (addr inside {[IAU_DPCMD_ADDR_ST : IAU_DPCMD_ADDR_END]}) begin
      instr = data;
      cvg_iau_instr.sample();
    end
    /*else if (addr inside {['h1000:'h1FFF]}) begin
      if (header_received) begin
          cmd = data;
          cvg_iau_cmd.sample();
          header_received = 0;
      end
      else begin
        header = data;
        cvg_iau_op.sample();
        //bypass cmd only needs the header to start execution
        if (header.cmd_format != iau_common_pkg::CMD_OP_BYP)
          header_received = 1;
      end
    end*/
  endfunction : decode_addr

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info(get_full_name(), $sformatf(
      "cvg_iau_instr: %.2f%% \ncvg_iau_cmd: %.2f%%",
      cvg_iau_instr.get_coverage(), cvg_iau_cmd.get_coverage()
    ), UVM_LOW)
  endfunction : report_phase


endclass

`endif


