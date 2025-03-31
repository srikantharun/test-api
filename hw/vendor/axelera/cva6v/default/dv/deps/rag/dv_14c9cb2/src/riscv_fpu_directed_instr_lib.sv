// Stress the numeric corner cases of floating point arithmetic operations
// Preloads FPR with random values including special ones (NaN, Inf)
// Generates arithmetic I, M, F instructions
// Adds random FPU related "events"
class riscv_fpu_arithmetic_stream extends riscv_directed_instr_stream;

  typedef enum logic {
    DISABLED = 0,
    ENABLED = 1
  } fpu_state_t;

  typedef enum logic {
    HAS_TARGET_LABEL = 0,
    NEEDS_TARGET_LABEL = 1
  } jump_branch_state_t;

  // LD/ST setup
  int max_data_page_id;
  bit load_store_shared_memory;
  mem_region_t data_page[$];
  rand int unsigned  data_page_id;
  rand int max_load_store_offset;
  rand int base;
  int  offset;
  int  addr;
  rand riscv_reg_t addr_reg;
  // regs setup
  int unsigned num_of_avail_regs = 6;
  int unsigned num_of_avail_fp_regs = 9;
  // instr setup
  rand int unsigned num_of_instr;
  riscv_instr_group_t exclude_groups[] = {RV32C, RV64C, RV32D, RV64D};
  riscv_instr_name_t exclude_instr[] = {};
  // events weights
  int ldst_instr_weight = 5;
  int fcsr_read_weight = 4;
  int fcsr_change_rm_weight = 3;
  int forward_jump_weight = 3;
  int forward_branch_weight = 3;
  int switch_fpu_state_weight = 3;
  int inject_nop_weight = 1; // Test FPU forwading

  // internal logic
  bit seen_fpu_instr = 0;
  rand bit set_illegal_frm_value;
  rand bit [2:0] illegal_frm_value;

  // FPU init weights
  rand int infinity_weight;
  rand int largest_weight;
  rand int zero_weight;
  rand int nan_weight;
  rand int normal_weight;
  rand int subnormal_weight;

  `uvm_object_utils(riscv_fpu_arithmetic_stream)
  `uvm_object_new

  constraint avail_regs_c {
    unique {avail_regs};
    foreach(avail_regs[i]) {
      !(avail_regs[i] inside {cfg.reserved_regs});
      !(avail_regs[i] inside {cfg.gpr}); // don't touch trap handler regs or it will fail
      avail_regs[i] != ZERO;
    }
  }

  constraint avail_fp_regs_c {
    unique {avail_fp_regs};
  }

  constraint num_of_instr_c {
    num_of_instr inside {[20:40]};
  }

  constraint a_dist_c {
    set_illegal_frm_value dist { 0 := 96, 1 := 4}; // 4% baseline chance across all scenarios
  }

  constraint fpu_init_weights_c {
    infinity_weight inside {[0:1]};
    largest_weight inside {[0:1]};
    zero_weight inside {[0:1]};
    nan_weight inside {[0:3]};
    normal_weight inside {[3:8]};
    subnormal_weight inside {[0:3]};
  }

  constraint fpu_init_weights_at_least_one_nonzero_c {
    infinity_weight
    || largest_weight
    || zero_weight
    || nan_weight
    || normal_weight
    || subnormal_weight;
  }

  // LD/ST specific logic
  constraint addr_reg_c {
    if (!cfg.no_data_page) {
      !(addr_reg inside {cfg.reserved_regs});
      !(addr_reg inside {cfg.gpr});
      !(addr_reg inside {avail_regs});
      addr_reg != ZERO;
    }
  }

  constraint addr_c {
    if (!cfg.no_data_page) {
      solve data_page_id before max_load_store_offset;
      solve max_load_store_offset before base;
      data_page_id < max_data_page_id;
      foreach (data_page[i]) {
        if (i == data_page_id) {
          max_load_store_offset == data_page[i].size_in_bytes;
        }
      }
      base inside {[0 : max_load_store_offset-1]};
    }
  }

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    avail_fp_regs = new[num_of_avail_fp_regs];
    if (!cfg.no_data_page) begin
      data_page = cfg.mem_region;
      max_data_page_id = data_page.size();
      reserved_rd = new[1];
    end
    super.pre_randomize();
  endfunction: pre_randomize

  virtual function void setup_mem_addr_w_la_instr(int id, int base = 0);
    riscv_pseudo_instr la_instr;
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.rd = reserved_rd[0];
    la_instr.imm_str = $sformatf(
      "%0s%0s+%0d", hart_prefix(hart), cfg.mem_region[id].name, base
    );
    instr_list.push_front(la_instr);
  endfunction: setup_mem_addr_w_la_instr

  virtual function void randomize_offset();
    int offset_, addr_;
    if (!std::randomize(offset_, addr_) with {
      soft offset_ inside {[-96:96]};
      addr_ == base + offset_;
      addr_ inside {[0 : max_load_store_offset - 1]};
      addr_ % 2 dist {
        0 := 80,
        1 := 20
      }; // misaligned ld/st are less likely
    }) begin
      `uvm_fatal(`gfn, "Cannot randomize load/store offset")
    end
    offset = offset_;
    addr = addr_;
  endfunction

  function riscv_instr get_ldst_instr();
    riscv_instr instr;
    randomize_offset();
    if (offset % 2 == 0) begin
      allowed_instr = {FLH, FSH};
    end else begin
      allowed_instr = {FLW, FSW, FLH, FSH};
    end
    instr = riscv_instr::get_load_store_instr(allowed_instr);
    instr.has_rs1 = 0;
    instr.has_imm = 0;
    randomize_gpr(instr);
    instr.rs1 = reserved_rd[0];
    instr.imm_str = $sformatf("%0d", $signed(offset));
    instr.process_load_store = 0;
    return instr;
  endfunction: get_ldst_instr

  // Adds enable / disable FPU instruction, switches fpu_state
  function void switch_fpu_state(ref fpu_state_t fpu_state, ref riscv_instr instr_list[$], riscv_reg_t avail_gpr);
    riscv_pseudo_instr li_fs_bits_instr;
    riscv_instr fpu_switch_instr;
    li_fs_bits_instr = riscv_common_functions::get_li_instr(.rd(avail_gpr), .imm_str("0x6000")); // mask for MSTATUS.FS bits (14:13)
    if (fpu_state == ENABLED) begin
      fpu_switch_instr = riscv_common_functions::get_fpu_disable_instr(.rs1(avail_gpr), .priv_mode(cfg.init_privileged_mode));
      fpu_state = DISABLED;
    end else begin
      fpu_switch_instr = riscv_common_functions::get_fpu_enable_instr(.rs1(avail_gpr), .priv_mode(cfg.init_privileged_mode));
      fpu_state = ENABLED;
    end
    instr_list.push_back(li_fs_bits_instr);
    instr_list.push_back(fpu_switch_instr);
  endfunction: switch_fpu_state

  function riscv_instr get_fcsr_read_instr();
    riscv_instr fcsr_read_instr;
    fcsr_read_instr = riscv_instr::get_instr(CSRRS);
    randomize_gpr(fcsr_read_instr);
    fcsr_read_instr.csr = FCSR;
    fcsr_read_instr.rs1 = ZERO; // makes it CSRR
    return fcsr_read_instr;
  endfunction: get_fcsr_read_instr

  function riscv_instr get_change_fcsr_rm_instr(bit [2:0] value);
    riscv_instr fcsr_rm_instr;
    fcsr_rm_instr = riscv_instr::get_instr(CSRRWI);
    randomize_gpr(fcsr_rm_instr);
    fcsr_rm_instr.csr = FRM;
    fcsr_rm_instr.rd = ZERO; // makes it CSRR
    fcsr_rm_instr.imm_str = $sformatf("0x%h", value);
    if (value > 3'b100) begin
      fcsr_rm_instr.comment = "illegal FRM value set";
    end
    return fcsr_rm_instr;
  endfunction: get_change_fcsr_rm_instr

  virtual function void init_fp_registers();
    // FP regs initalization
    for (int i = 0; i < num_of_avail_fp_regs; i++) begin
      instr_list.push_back(
        riscv_common_functions::get_li_instr(
          .rd(avail_regs[0]),
          .imm_str(
            $sformatf(
              "0x%0h", riscv_common_functions::get_rand_spf_value(
                .infinity_weight(infinity_weight),
                .largest_weight(largest_weight),
                .zero_weight(zero_weight),
                .nan_weight(nan_weight),
                .normal_weight(normal_weight),
                .subnormal_weight(subnormal_weight)
              )
            )
          )
        )
      );
      instr_list.push_back(
        riscv_common_functions::get_fmv_instr(
          .fd(avail_fp_regs[i]),
          .rs1(avail_regs[0])
        )
      );
    end
  endfunction : init_fp_registers

  function void post_randomize();
    fpu_state_t fpu_state = ENABLED;
    jump_branch_state_t jump_branch_state = HAS_TARGET_LABEL;

    if (!cfg.no_data_page) begin
      reserved_rd[0] = addr_reg; // avoids overwriting by arith instrs
      setup_mem_addr_w_la_instr(data_page_id, base);
    end
    init_fp_registers();

    // Add instructions and "events"
    for (int i = 0; i < num_of_instr; i++) begin
      riscv_instr instr;
      // Pool will consist of I, M and F
      instr = riscv_instr::get_rand_instr(
        .include_category({ARITHMETIC}),
        .exclude_category({LOAD, STORE}),
        .include_group({RV32F, RV64F, ZFH}),
        .exclude_instr(exclude_instr),
        .exclude_group(exclude_groups)
      );
      //`uvm_info(`gfn, $sformatf("fpu_instr %s ", instr.convert2string()), UVM_NONE)

      instr.set_rand_mode();
      instr.m_cfg = cfg; // pass the shared config, RVV complains otherwise
      randomize_gpr_no_dest_constr_unique_sources(instr);
      instr_list.push_back(instr);
      seen_fpu_instr = (instr.instr_type == FLOATING_POINT);

      // Add "events"
      // FCSR read to expose any e.g. rounding errors
      // changing FCSR rounding mode
      // forward jump
      // random forward branch
      // enable/disable FPU inbetween execution
      // inject NOP for testing forwarding (in longer ops like fused) in the FPU
      // chance to end forward jump / branch
      // chance to enable FPU
      randcase
        ldst_instr_weight: begin
          if (!cfg.no_data_page) begin
            instr_list.push_back(get_ldst_instr());
          end
        end
        fcsr_read_weight: instr_list.push_back(get_fcsr_read_instr());
        fcsr_change_rm_weight: begin
          if (set_illegal_frm_value) begin
            if (!std::randomize(illegal_frm_value) with {
                illegal_frm_value >= 3'b100; // incl 1 legal to test going b to correct value inbetween FPU instrs
            }) begin
              `uvm_fatal(`gfn, "Cannot randomize illegal fcsr frm!")
            end
            instr_list.push_back(get_change_fcsr_rm_instr(.value(illegal_frm_value)));
          end else begin
            if (!std::randomize(cfg.fcsr_rm) with {cfg.fcsr_rm != DYN;}) begin
              `uvm_fatal(`gfn, "Cannot randomize cfg.fcsr_rm!")
            end
            instr_list.push_back(get_change_fcsr_rm_instr(.value(cfg.fcsr_rm)));
          end
        end
        forward_jump_weight: begin
          instr_list.push_back(riscv_common_functions::get_forward_jump_instr());
          jump_branch_state = NEEDS_TARGET_LABEL;
        end
        forward_branch_weight: begin
          instr_list.push_back(riscv_common_functions::get_random_forward_branch_instr());
          jump_branch_state = NEEDS_TARGET_LABEL;
        end
        switch_fpu_state_weight: begin
          if(!cfg.init_privileged_mode == USER_MODE) begin // would trap in U
            switch_fpu_state(.fpu_state(fpu_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
            seen_fpu_instr = 0;
            if (jump_branch_state == NEEDS_TARGET_LABEL) begin
              fpu_state = DISABLED; // since we skip over this with jump
            end
          end
        end
        inject_nop_weight: begin
          instr_list.push_back(riscv_common_functions::get_nop_instr());
        end
        30: begin
          if (jump_branch_state == NEEDS_TARGET_LABEL && seen_fpu_instr) begin
            // add 1 more to not have b2b jump/branch
            instr = riscv_instr::get_rand_instr(
              .include_category({ARITHMETIC}),
              .exclude_category({LOAD, STORE}),
              .include_group({RV32F, RV64F, ZFH}),
              .exclude_group(exclude_groups)
            );

            instr.set_rand_mode();
            instr.m_cfg = cfg; // pass the shared config, RVV complains otherwise
            randomize_gpr_no_dest_constr_unique_sources(instr);
            instr_list.push_back(instr);

            instr_list[$].label = "1"; // end jump here
            instr_list[$].has_label = 1;
            jump_branch_state = HAS_TARGET_LABEL;
          end
        end
        30: begin
          if (fpu_state == DISABLED && seen_fpu_instr && jump_branch_state == HAS_TARGET_LABEL) begin
            switch_fpu_state(.fpu_state(fpu_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
            seen_fpu_instr = 0;
          end
        end
        20: ;
      endcase
    end

    // Final "Cleanup"
    // Create a target for the last jump forward
    if (jump_branch_state == NEEDS_TARGET_LABEL) begin
      riscv_instr nop_instr;
      nop_instr = riscv_instr::get_instr(NOP);
      nop_instr.label = "1";
      nop_instr.has_label = 1;
      instr_list.push_back(nop_instr);
      jump_branch_state = HAS_TARGET_LABEL;
    end
    // Re-enable the FPU
    if (fpu_state == DISABLED) begin
      switch_fpu_state(.fpu_state(fpu_state), .instr_list(instr_list), .avail_gpr(avail_regs[0]));
    end
    // Restore valid FRM
    if (set_illegal_frm_value) begin
      instr_list.push_back(get_change_fcsr_rm_instr(.value(cfg.fcsr_rm)));
    end
    // Clear FFLAGS
    instr_list.push_back(riscv_common_functions::get_clear_fflags_instr());

    // Parent - class extended code
    foreach(instr_list[i]) begin
      // don't mute the jump/branch labels
      if (instr_list[i].label == "1") begin
        instr_list[i].has_label = 1'b1;
      end
      else begin
        instr_list[i].has_label = 1'b0;
      end
      instr_list[i].atomic = 1'b1;
    end
    instr_list[0].comment = $sformatf("Start %0s", get_name());
    instr_list[$].comment = $sformatf("End %0s", get_name());
    if(label != "") begin
      instr_list[0].label = label;
      instr_list[0].has_label = 1'b1;
    end

    `uvm_info(get_type_name(), "post_randomize called!", UVM_FULL)
  endfunction

endclass : riscv_fpu_arithmetic_stream

class riscv_fpu_only_arithmetic_stream extends riscv_fpu_arithmetic_stream;

  `uvm_object_utils(riscv_fpu_only_arithmetic_stream)
  function new (string name="");
    super.new(name);
    inject_nop_weight = 2; // slightly increased odds
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV};
  endfunction : new

endclass : riscv_fpu_only_arithmetic_stream

class riscv_fpu_only_halfprecision_arithmetic_stream extends riscv_fpu_arithmetic_stream;

  `uvm_object_utils(riscv_fpu_only_halfprecision_arithmetic_stream)
  function new (string name="");
    super.new(name);
    inject_nop_weight = 2; // slightly increased odds
    exclude_groups = {RV32F, RV64F, RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV};
  endfunction : new

  virtual function void init_fp_registers();
    // FP regs initalization
    for (int i = 0; i < num_of_avail_fp_regs; i++) begin
      instr_list.push_back(
        riscv_common_functions::get_li_instr(
          .rd(avail_regs[0]),
          .imm_str(
            $sformatf(
              "0x%0h", riscv_common_functions::get_rand_hpf_value(
                .infinity_weight(infinity_weight),
                .largest_weight(largest_weight),
                .zero_weight(zero_weight),
                .nan_weight(nan_weight),
                .normal_weight(normal_weight),
                .subnormal_weight(subnormal_weight)
              )
            )
          )
        )
      );
      instr_list.push_back(
        riscv_common_functions::get_fmv_instr(
          .fd(avail_fp_regs[i]),
          .rs1(avail_regs[0]),
          .is_halfprecision(1)
        )
      );
    end
  endfunction : init_fp_registers

endclass : riscv_fpu_only_halfprecision_arithmetic_stream

class FloatingPointOperationPair;
  // Define IEEE-754 compliant 32-bit floating-point numbers
  bit is_halfprecision;
  rand bit [31:0] A;
  rand bit [31:0] B;
  rand bit [1:0] one_of_inputs_is_subnormal;
  rand bit [5:0] a_msb_zero_count;
  rand bit [5:0] b_msb_zero_count;

  bit [7:0] fp_bias;
  bit [7:0] max_exp;

  function new(bit is_halfprecision);
    this.is_halfprecision = is_halfprecision;
    if (this.is_halfprecision) begin
      fp_bias = 8'h0f;
      max_exp = 8'h1f;
    end else begin
      fp_bias = 8'h7f;
      max_exp = 8'hff;
    end
  endfunction

  // Constraint to meet specified conditions
  constraint one_of_inputs_is_subnormal_c {
    one_of_inputs_is_subnormal dist {
      0 := 90,
      1 := 5, // A subnormal
      2 := 5, // B subnormal
      3 := 0 // A & B subnormal covered in a separate class
    };
  }

  constraint valid_leading_zeroes_in_subnormal_c {
    if (is_halfprecision) {
      a_msb_zero_count inside {[0:5]};
      b_msb_zero_count inside {[0:5]};
    } else {
      a_msb_zero_count inside {[0:20]};
      b_msb_zero_count inside {[0:20]};
    }
  }

  constraint inputs_are_valid_fp_numbers_c {
    if (is_halfprecision) {
      A[31:16] == 0; // halfprecision
      B[31:16] == 0; // halfprecision
      if (one_of_inputs_is_subnormal == 1) {
        // subnormal + manitssa leading zeroes
        foreach(A[i]) { // Workaround of "Range must be bounded by constant expressions" compiler error
          if (i <= 14 && i > HALF_PRECISION_FRACTION_BITS-a_msb_zero_count) A[i] == 0;
        }
        B[HALF_PRECISION_FRACTION_BITS:0] > 0;
        &B[14:HALF_PRECISION_FRACTION_BITS] != 1;
      } else if (one_of_inputs_is_subnormal == 2) {
        A[HALF_PRECISION_FRACTION_BITS:0] > 0;
        &A[14:HALF_PRECISION_FRACTION_BITS] != 1;
        // subnormal + manitssa leading zeroes
        foreach(B[i]) { // workaround for "Range must be bounded by constant expressions" compiler error
          if (i <= 14 && i > HALF_PRECISION_FRACTION_BITS-b_msb_zero_count) B[i] == 0;
        }
      } else { // both normal
        A[HALF_PRECISION_FRACTION_BITS:0] > 0; // could be subnormal, but not zero
        &A[14:HALF_PRECISION_FRACTION_BITS] != 1; // not NAN, not inf
        B[HALF_PRECISION_FRACTION_BITS:0] > 0; // could be subnormal, but not zero
        &B[14:HALF_PRECISION_FRACTION_BITS] != 1; // not NAN, not inf
      }
    } else {
      if (one_of_inputs_is_subnormal == 1) {
        // subnormal + manitssa leading zeroes
        foreach(A[i]) { // Workaround of "Range must be bounded by constant expressions" compiler error
          if (i <= 30 && i > SINGLE_PRECISION_FRACTION_BITS-a_msb_zero_count) A[i] == 0;
        }
        B[SINGLE_PRECISION_FRACTION_BITS:0] > 0;
        &B[30:SINGLE_PRECISION_FRACTION_BITS] != 1;
      } else if (one_of_inputs_is_subnormal == 2) {
        A[SINGLE_PRECISION_FRACTION_BITS:0] > 0;
        &A[30:SINGLE_PRECISION_FRACTION_BITS] != 1;
        // subnormal + manitssa leading zeroes
        foreach(B[i]) { // workaround for "Range must be bounded by constant expressions" compiler error
          if (i <= 30 && i > SINGLE_PRECISION_FRACTION_BITS-b_msb_zero_count) B[i] == 0;
        }
      } else { // both normal
        A[SINGLE_PRECISION_FRACTION_BITS:0] > 0; // could be subnormal, but not zero
        &A[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NAN, not inf
        B[SINGLE_PRECISION_FRACTION_BITS:0] > 0; // could be subnormal, but not zero
        &B[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NAN, not inf
      }
    }
  }

  // higher chance for subnormal (controlled by constraint)
  // higher chance for leading zeros
  constraint solve_order_c {
    solve one_of_inputs_is_subnormal before A,B;
    solve a_msb_zero_count before A;
    solve b_msb_zero_count before B;
  }

  // in mul, we sum the actual (unbiased) exponents, not the bit representations
  // exp_x - b + exp_y - b = exp_x + exp_y - 2 b
  // + b (we add bias to go back to the stored bit repr) and this gives us the final:
  // exp_x + exp_y - b
  // subnormals has to be "shifted" by amount of leading zeros to perform the arithmetics
  // these are soft as some very small subnormals cant satisfy this
  constraint fmul_result_big {
    if (is_halfprecision) {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - fp_bias - a_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - fp_bias - b_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - fp_bias) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+16] :/ 5
        };
      }
    } else {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - fp_bias - a_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - fp_bias - b_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - fp_bias) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+16] :/ 5
        };
      }
    }
  }

  // original equation (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - fp_bias)
  // is being offset by fp_bias because bits cannot have negative values (theyre unsigned)!
  constraint fmul_result_small {
    if (is_halfprecision) {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - a_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - b_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS]) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      }
    } else {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - a_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - b_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS]) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      }
    }
  }

  // we have to subtract the actual (unbiased) exponents, not the bit representations
  // exp_x - b - (exp_y - b) = exp_x - exp_y + b (we add bias to go back to the stored bit repr)
  // final: exp_x - exp_y + b
  constraint fdiv_result_big {
    if (is_halfprecision) {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] - B[30:HALF_PRECISION_FRACTION_BITS] + fp_bias - a_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] - B[30:HALF_PRECISION_FRACTION_BITS] + fp_bias - b_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] - B[30:HALF_PRECISION_FRACTION_BITS] + fp_bias) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      }
    } else {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] - B[30:SINGLE_PRECISION_FRACTION_BITS] + fp_bias - a_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] - B[30:SINGLE_PRECISION_FRACTION_BITS] + fp_bias - b_msb_zero_count) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      } else {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] - B[30:SINGLE_PRECISION_FRACTION_BITS] + fp_bias) dist {
          [max_exp-16:max_exp-3] :/ 5,
          [max_exp-3:max_exp] :/ 10,
          [max_exp:max_exp+17] :/ 5
        };
      }
    }
  }

  // Same case as MulSmall, hence 2*fp_bias
  constraint fdiv_result_small {
    if (is_halfprecision) {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] - B[14:HALF_PRECISION_FRACTION_BITS] + 2*fp_bias - a_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] - B[14:HALF_PRECISION_FRACTION_BITS] + 2*fp_bias - b_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else {
        soft (A[14:HALF_PRECISION_FRACTION_BITS] + B[14:HALF_PRECISION_FRACTION_BITS] - 2*fp_bias) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      }
    } else {
      if (one_of_inputs_is_subnormal == 1) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] - B[30:SINGLE_PRECISION_FRACTION_BITS] + 2*fp_bias - a_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else if (one_of_inputs_is_subnormal == 2) {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] - B[30:SINGLE_PRECISION_FRACTION_BITS] + 2*fp_bias - b_msb_zero_count) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      } else {
        soft (A[30:SINGLE_PRECISION_FRACTION_BITS] + B[30:SINGLE_PRECISION_FRACTION_BITS] - 2*fp_bias) dist {
          [fp_bias-5:fp_bias-2] :/ 1,
          fp_bias-1 :/ 1,
          fp_bias :/ 2,
          [fp_bias+1:fp_bias+6] :/ 5,
          [fp_bias+6:fp_bias+17] :/ 4
        };
      }
    }
  }
endclass

// Classes part
// "Meta" class that will be inherited from, reenable constraints to target specific cases
class riscv_fpu_only_meta_arithmetic_stream extends riscv_fpu_only_arithmetic_stream;
  rand FloatingPointOperationPair fop_h;
  int is_halfprecision;

  constraint num_of_instr_c {
    num_of_instr inside {[4:7]};
  }

  `uvm_object_utils(riscv_fpu_only_meta_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 0;
    fop_h = new(is_halfprecision);
    fop_h.fmul_result_big.constraint_mode(0);
    fop_h.fmul_result_small.constraint_mode(0);
    fop_h.fdiv_result_big.constraint_mode(0);
    fop_h.fdiv_result_small.constraint_mode(0);
    num_of_avail_fp_regs = 2;
    ldst_instr_weight = 2;
    fcsr_read_weight = 2;
    fcsr_change_rm_weight = 1;
    forward_jump_weight = 1;
    forward_branch_weight = 1;
    switch_fpu_state_weight = 1;
    inject_nop_weight = 2; // slightly increased odds
  endfunction : new

  virtual function void init_fp_registers();
    // FP regs initalization
    `DV_CHECK_RANDOMIZE_FATAL(fop_h, "Randomization for special case of floating point arguments failed");
    instr_list.push_back(
      riscv_common_functions::get_li_instr(
        .rd(avail_regs[0]),
        .imm_str($sformatf("0x%0h", fop_h.A))
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_fmv_instr(
        .fd(avail_fp_regs[0]),
        .rs1(avail_regs[0]),
        .is_halfprecision(is_halfprecision)
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_li_instr(
        .rd(avail_regs[0]),
        .imm_str($sformatf("0x%0h", fop_h.B))
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_fmv_instr(
        .fd(avail_fp_regs[1]),
        .rs1(avail_regs[0]),
        .is_halfprecision(is_halfprecision)
      )
    );
  endfunction

endclass : riscv_fpu_only_meta_arithmetic_stream

class riscv_fpu_only_divsmall_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_divsmall_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h.fdiv_result_small.constraint_mode(1);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH}; // no halfprecision
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S,
      FSGNJ_S, FSGNJN_S, FSGNJX_S,
      FADD_S, FMADD_S, FNMADD_S, FMUL_S,
      FSUB_S, FMSUB_S, FNMSUB_S,
      FSQRT_S
    }; // hit fdiv
  endfunction : new

endclass : riscv_fpu_only_divsmall_arithmetic_stream

class riscv_fpu_only_halfprecision_divsmall_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_halfprecision_divsmall_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 1;
    fop_h = new(is_halfprecision);
    fop_h.fmul_result_big.constraint_mode(0);
    fop_h.fmul_result_small.constraint_mode(0);
    fop_h.fdiv_result_big.constraint_mode(0);
    fop_h.fdiv_result_small.constraint_mode(1);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, RV32F, RV64F}; // no single precision
    exclude_instr = {
      FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,
      FMV_H_X, FMV_X_H,
      FCLASS_H, FLE_H, FLT_H, FEQ_H, FMIN_H, FMAX_H,
      FSGNJ_H, FSGNJN_H, FSGNJX_H,
      FADD_H, FMADD_H, FNMADD_H, FMUL_H,
      FSUB_H, FMSUB_H, FNMSUB_H,
      FSQRT_H
    }; // hit fdiv
  endfunction : new

endclass : riscv_fpu_only_halfprecision_divsmall_arithmetic_stream

// Produce FDIV results on the boundary of the overflow
class riscv_fpu_only_divbig_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_divbig_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h.fdiv_result_big.constraint_mode(1);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH}; // no halfprecision
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S,
      FSGNJ_S, FSGNJN_S, FSGNJX_S,
      FADD_S, FMADD_S, FNMADD_S, FMUL_S,
      FSUB_S, FMSUB_S, FNMSUB_S,
      FSQRT_S
    }; // hit fdiv
  endfunction : new

endclass : riscv_fpu_only_divbig_arithmetic_stream

class riscv_fpu_only_halfprecision_divbig_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_halfprecision_divbig_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 1;
    fop_h = new(is_halfprecision);
    fop_h.fmul_result_big.constraint_mode(0);
    fop_h.fmul_result_small.constraint_mode(0);
    fop_h.fdiv_result_big.constraint_mode(1);
    fop_h.fdiv_result_small.constraint_mode(0);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, RV32F, RV64F}; // no single precision
    exclude_instr = {
      FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,
      FMV_H_X, FMV_X_H,
      FCLASS_H, FLE_H, FLT_H, FEQ_H, FMIN_H, FMAX_H,
      FSGNJ_H, FSGNJN_H, FSGNJX_H,
      FADD_H, FMADD_H, FNMADD_H, FMUL_H,
      FSUB_H, FMSUB_H, FNMSUB_H,
      FSQRT_H
    }; // hit fdiv
  endfunction : new

endclass : riscv_fpu_only_halfprecision_divbig_arithmetic_stream


// Try to produce FMUL results on the boundary of the denormal
class riscv_fpu_only_mulsmall_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_mulsmall_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h.fmul_result_small.constraint_mode(1);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH}; // no halfprecision
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S,
      FSGNJ_S, FSGNJN_S, FSGNJX_S,
      FADD_S, FNMADD_S, FMADD_S,
      FSUB_S, FMSUB_S, FNMSUB_S,
      FDIV_S, FSQRT_S
    }; // hit muls
  endfunction : new

endclass : riscv_fpu_only_mulsmall_arithmetic_stream

class riscv_fpu_only_halfprecision_mulsmall_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_halfprecision_mulsmall_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 1;
    fop_h = new(is_halfprecision);
    fop_h.fmul_result_big.constraint_mode(0);
    fop_h.fmul_result_small.constraint_mode(1);
    fop_h.fdiv_result_big.constraint_mode(0);
    fop_h.fdiv_result_small.constraint_mode(0);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, RV32F, RV64F}; // no single precision
    exclude_instr = {
      FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,
      FMV_H_X, FMV_X_H,
      FCLASS_H, FLE_H, FLT_H, FEQ_H, FMIN_H, FMAX_H,
      FSGNJ_H, FSGNJN_H, FSGNJX_H,
      FADD_H, FNMADD_H, FMADD_H,
      FSUB_H, FMSUB_H, FNMSUB_H,
      FDIV_H, FSQRT_H
    }; // hit muls
  endfunction : new

endclass : riscv_fpu_only_halfprecision_mulsmall_arithmetic_stream

// Try to produce FMUL results on the boundary of the overflow
class riscv_fpu_only_mulbig_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_mulbig_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h.fmul_result_big.constraint_mode(1);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH}; // no halfprecision
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S,
      FSGNJ_S, FSGNJN_S, FSGNJX_S,
      FADD_S, FNMADD_S, FMADD_S,
      FSUB_S, FMSUB_S, FNMSUB_S,
      FDIV_S, FSQRT_S
    }; // hit muls
  endfunction : new

endclass : riscv_fpu_only_mulbig_arithmetic_stream

class riscv_fpu_only_halfprecision_mulbig_arithmetic_stream extends riscv_fpu_only_meta_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_halfprecision_mulbig_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 1;
    fop_h = new(is_halfprecision);
    fop_h.fmul_result_big.constraint_mode(1);
    fop_h.fmul_result_small.constraint_mode(0);
    fop_h.fdiv_result_big.constraint_mode(0);
    fop_h.fdiv_result_small.constraint_mode(0);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, RV32F, RV64F}; // no single precision
    exclude_instr = {
      FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,
      FMV_H_X, FMV_X_H,
      FCLASS_H, FLE_H, FLT_H, FEQ_H, FMIN_H, FMAX_H,
      FSGNJ_H, FSGNJN_H, FSGNJX_H,
      FADD_H, FNMADD_H, FMADD_H,
      FSUB_H, FMSUB_H, FNMSUB_H,
      FDIV_H, FSQRT_H
    }; // hit muls
  endfunction : new

endclass : riscv_fpu_only_halfprecision_mulbig_arithmetic_stream

class FloatingPointSubnormalOperation;
  // Define IEEE-754 compliant 32-bit floating-point numbers
  // Covers cases when both numbers are subnormal
  bit is_halfprecision;

  rand bit [31:0] A;
  rand bit [31:0] B;

  bit [7:0] fp_bias;
  bit [7:0] max_exp;

  function new(bit is_halfprecision);
    this.is_halfprecision = is_halfprecision;
    if (this.is_halfprecision) begin
      fp_bias = 8'h0f;
      max_exp = 8'h1f;
    end else begin
      fp_bias = 8'h7f;
      max_exp = 8'hff;
    end
  endfunction

  // Constraint to meet specified conditions
  constraint inputs_are_fp_numbers {
    if (is_halfprecision) {
      A[31:16] == 0; // halfprecision
      A[HALF_PRECISION_FRACTION_BITS:0] > 0; // not zero
      |A[14:HALF_PRECISION_FRACTION_BITS] == 0; // subnormal

      B[31:16] == 0; // halfprecision
      B[HALF_PRECISION_FRACTION_BITS:0] > 0; // not zero
      |B[14:HALF_PRECISION_FRACTION_BITS] == 0; // subnormal
    } else {
      A[SINGLE_PRECISION_FRACTION_BITS:0] > 0; // not zero
      |A[30:SINGLE_PRECISION_FRACTION_BITS] == 0; // subnormal

      B[SINGLE_PRECISION_FRACTION_BITS:0] > 0; // not zero
      |B[30:SINGLE_PRECISION_FRACTION_BITS] == 0; // subnormal
    }
  }

endclass


class riscv_fpu_only_subnormal_arithmetic_stream extends riscv_fpu_only_arithmetic_stream;
  rand FloatingPointSubnormalOperation fop_h;
  int is_halfprecision;

  constraint num_of_instr_c {
    num_of_instr inside {[15:20]};
  }

  `uvm_object_utils(riscv_fpu_only_subnormal_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 0;
    fop_h = new(is_halfprecision);
    num_of_avail_fp_regs = 6;
    ldst_instr_weight = 2;
    fcsr_read_weight = 2;
    fcsr_change_rm_weight = 1;
    forward_jump_weight = 1;
    forward_branch_weight = 1;
    switch_fpu_state_weight = 1;
    inject_nop_weight = 2; // slightly increased odds
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH};
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W
    };
  endfunction : new

  virtual function void init_fp_registers();
    int cnt = 0;
    // FP regs initalization
    for (int i = 0; i < 3; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(fop_h, "Randomization for special case of floating point arguments failed");
      instr_list.push_back(
        riscv_common_functions::get_li_instr(
          .rd(avail_regs[0]),
          .imm_str($sformatf("0x%0h", fop_h.A))
        )
      );
      instr_list.push_back(
        riscv_common_functions::get_fmv_instr(
          .fd(avail_fp_regs[cnt]),
          .rs1(avail_regs[0]),
          .is_halfprecision(is_halfprecision)
        )
      );
      cnt++;
      instr_list.push_back(
        riscv_common_functions::get_li_instr(
          .rd(avail_regs[0]),
          .imm_str($sformatf("0x%0h", fop_h.B))
        )
      );
      instr_list.push_back(
        riscv_common_functions::get_fmv_instr(
          .fd(avail_fp_regs[cnt]),
          .rs1(avail_regs[0]),
          .is_halfprecision(is_halfprecision)
        )
      );
      cnt++;
    end
  endfunction

endclass : riscv_fpu_only_subnormal_arithmetic_stream

class riscv_fpu_only_halfprecision_subnormal_arithmetic_stream extends riscv_fpu_only_subnormal_arithmetic_stream;
  `uvm_object_utils(riscv_fpu_only_halfprecision_subnormal_arithmetic_stream)

  function new (string name="");
    super.new(name);
    is_halfprecision = 1; // for init_fp_registers
    fop_h = new(is_halfprecision);
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, RV32F, RV64F};
    exclude_instr = {
      FCVT_W_H, FCVT_WU_H, FCVT_H_W, FCVT_H_WU,
      FMV_H_X, FMV_X_H
    };
  endfunction : new

endclass : riscv_fpu_only_halfprecision_subnormal_arithmetic_stream

class FloatingPointOperationTriplet; //#(int high_bit_zero=SINGLE_PRECISION_FRACTION_BITS-6, int low_bit_zero=0);
  // Define IEEE-754 compliant 32-bit floating-point numbers
  rand bit [31:0] A;
  rand bit [31:0] B;
  rand bit [31:0] C;
  bit [31:0] high_bit_zero;
  bit [31:0] low_bit_zero;

  function new (bit [31:0] high_bit_zero=SINGLE_PRECISION_FRACTION_BITS-6, bit [31:0] low_bit_zero=0);
    this.high_bit_zero = high_bit_zero;
    this.low_bit_zero = low_bit_zero;
  endfunction

  // Constraint to meet specified conditions
  constraint operation_bits_constraints {
      // Approximate by constraining the exponent to be in the low range
      // (this will ensure only the leading bits are significant in the result)
      // All numbers are not a special case + they have fraction
      foreach(A[i]) { // Workaround of "Range must be bounded by constant expressions" compiler error
        if (i >= low_bit_zero && i <= high_bit_zero) A[i] == 0;
      }
      A[30:SINGLE_PRECISION_FRACTION_BITS] > 0; // not subnormal
      &A[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NAN
      A[SINGLE_PRECISION_FRACTION_BITS:0] != 0;
      //A[high_bit_zero:low_bit_zero] == 0;  // This constrains `A`'s mantissa to MSBs (lowers significant bit count)

      foreach(B[i]) { // Workaround of "Range must be bounded by constant expressions" compiler error
        if (i >= low_bit_zero && i <= high_bit_zero) B[i] == 0;
      }
      B[30:SINGLE_PRECISION_FRACTION_BITS] > 0; // not subnormal
      &B[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NAN
      B[SINGLE_PRECISION_FRACTION_BITS:0] != 0;
      //B[high_bit_zero:low_bit_zero] == 0;  // This constrains `B`'s mantissa to MSBs (lowers significant bit count)

      foreach(C[i]) { // Workaround of "Range must be bounded by constant expressions" compiler error
        if (i >= low_bit_zero && i <= high_bit_zero) C[i] == 0;
      }
      C[30:SINGLE_PRECISION_FRACTION_BITS] > 0; // not subnormal
      &C[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NAN
      C[SINGLE_PRECISION_FRACTION_BITS:0] != 0;
      //C[high_bit_zero:low_bit_zero] == 0;  // This constrains `C`'s mantissa to MSBs (lowers significant bit count)

      // Ensure opposite signs for A*B and C
      A[31] ^ B[31] != C[31];
      // Softer constraint than |A*B| < |C| due to randomization failures
      A[30:SINGLE_PRECISION_FRACTION_BITS] < C[30:SINGLE_PRECISION_FRACTION_BITS];
      B[30:SINGLE_PRECISION_FRACTION_BITS] < C[30:SINGLE_PRECISION_FRACTION_BITS];
  }

endclass

class riscv_fpu_only_ld_arithmetic_stream extends riscv_fpu_only_arithmetic_stream;
  // Low Significant Digits
  // Try to exercise FPU fault from one of Andes cores
  // For operation of A*B+C, if the signedness of A*B and C are the opposite of each other,
  // |A*B| < |C| and the number of valid significant digits is just 1 or 2 bits in the exact result

  constraint num_of_instr_c {
    num_of_instr inside {[15:25]};
  }

  rand FloatingPointOperationTriplet fop_h;

  `uvm_object_utils(riscv_fpu_only_ld_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h = new();
    num_of_avail_fp_regs = 3;
    ldst_instr_weight = 2;
    fcsr_read_weight = 2;
    fcsr_change_rm_weight = 1;
    forward_jump_weight = 1;
    forward_branch_weight = 1;
    switch_fpu_state_weight = 1;
    inject_nop_weight = 2; // slightly increased odds
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH};
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S
    }; // hit more fused ops
  endfunction : new

  virtual function void init_fp_registers();
    // FP regs initalization
    `DV_CHECK_RANDOMIZE_FATAL(fop_h, "Randomization for special case of floating point arguments failed");
    instr_list.push_back(
      riscv_common_functions::get_li_instr(
        .rd(avail_regs[0]),
        .imm_str($sformatf("0x%0h", fop_h.A))
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_fmv_instr(
        .fd(avail_fp_regs[0]),
        .rs1(avail_regs[0])
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_li_instr(
        .rd(avail_regs[0]),
        .imm_str($sformatf("0x%0h", fop_h.B))
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_fmv_instr(
        .fd(avail_fp_regs[1]),
        .rs1(avail_regs[0])
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_li_instr(
        .rd(avail_regs[0]),
        .imm_str($sformatf("0x%0h", fop_h.C))
      )
    );
    instr_list.push_back(
      riscv_common_functions::get_fmv_instr(
        .fd(avail_fp_regs[2]),
        .rs1(avail_regs[0])
      )
    );
  endfunction

endclass : riscv_fpu_only_ld_arithmetic_stream

  // High (lots of) Digits after the dot, mantissa MSBs set to 0
class riscv_fpu_only_hd_arithmetic_stream extends riscv_fpu_only_ld_arithmetic_stream;

  `uvm_object_utils(riscv_fpu_only_hd_arithmetic_stream)

  function new (string name="");
    super.new(name);
    fop_h = new(SINGLE_PRECISION_FRACTION_BITS, SINGLE_PRECISION_FRACTION_BITS-8);
    ldst_instr_weight = 2;
    fcsr_read_weight = 2;
    fcsr_change_rm_weight = 1;
    forward_jump_weight = 1;
    forward_branch_weight = 1;
    switch_fpu_state_weight = 1;
    inject_nop_weight = 2; // slightly increased odds
    exclude_groups = {RV32C, RV64C, RV32D, RV64D, RV32I, RV64I, RV32M, RV64M, RVV, ZFH};
    exclude_instr = {
      FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU,
      FCVT_L_S, FCVT_LU_S, FCVT_S_L, FCVT_S_LU,
      FMV_W_X, FMV_X_W,
      FCLASS_S, FLE_S, FLT_S, FEQ_S, FMIN_S, FMAX_S
    }; // hit more fused ops
  endfunction : new

endclass : riscv_fpu_only_hd_arithmetic_stream
