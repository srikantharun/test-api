class riscv_common_functions extends uvm_object;
  static function riscv_pseudo_instr get_li_instr(riscv_reg_t rd, string imm_str);
    riscv_pseudo_instr li_instr = new();
    li_instr.pseudo_instr_name = LI;
    li_instr.rd = rd;
    li_instr.imm_str = imm_str;
    return li_instr;
  endfunction: get_li_instr

  static function riscv_instr get_fmv_instr(riscv_fpr_t fd, riscv_reg_t rs1, bit is_halfprecision=0);
    riscv_instr fmv_instr;
    if (is_halfprecision) begin
      fmv_instr = riscv_instr::get_instr(FMV_H_X); // move the halfprec from gpr to fpr
    end else begin
      fmv_instr = riscv_instr::get_instr(FMV_W_X); // move the singleprec from gpr to fpr
    end
    fmv_instr.fd = fd;
    fmv_instr.rs1 = rs1;
    return fmv_instr;
  endfunction: get_fmv_instr

  static function riscv_instr get_fpu_disable_instr(riscv_reg_t rs1, privileged_mode_t priv_mode);
    riscv_instr fpu_disable_instr;
    fpu_disable_instr = riscv_instr::get_instr(CSRRC);
    fpu_disable_instr.csr = (priv_mode == MACHINE_MODE) ? MSTATUS : SSTATUS;
    fpu_disable_instr.rd = ZERO; // makes it CSRC
    fpu_disable_instr.rs1 = rs1;
    fpu_disable_instr.comment = "FPU disable";
    return fpu_disable_instr;
  endfunction: get_fpu_disable_instr

  static function riscv_instr get_fpu_enable_instr(riscv_reg_t rs1, privileged_mode_t priv_mode);
    riscv_instr fpu_enable_instr;
    fpu_enable_instr = riscv_instr::get_instr(CSRRS);
    fpu_enable_instr.csr = (priv_mode == MACHINE_MODE) ? MSTATUS : SSTATUS;
    fpu_enable_instr.rd = ZERO; // makes it CSRS
    fpu_enable_instr.rs1 = rs1;
    fpu_enable_instr.comment = "FPU enable";
    return fpu_enable_instr;
  endfunction: get_fpu_enable_instr

  static function riscv_instr get_dcache_disable_instr(riscv_reg_t rs1);
    riscv_instr dcache_disable_instr;
    dcache_disable_instr = riscv_instr::get_instr(CSRRC);
    dcache_disable_instr.csr = DCACHE;
    dcache_disable_instr.rd = ZERO; // makes it CSRC
    dcache_disable_instr.rs1 = rs1;
    return dcache_disable_instr;
  endfunction: get_dcache_disable_instr

  static function riscv_instr get_dcache_enable_instr(riscv_reg_t rs1);
    riscv_instr dcache_enable_instr;
    dcache_enable_instr = riscv_instr::get_instr(CSRRS);
    dcache_enable_instr.csr = DCACHE;
    dcache_enable_instr.rd = ZERO; // makes it CSRS
    dcache_enable_instr.rs1 = rs1;
    return dcache_enable_instr;
  endfunction: get_dcache_enable_instr

  static function riscv_instr get_forward_jump_instr();
    riscv_instr jump_instr;
    jump_instr = riscv_instr::get_instr(JAL);
    jump_instr.rd = ZERO; // make it J
    jump_instr.imm_str = "1f";
    return jump_instr;
  endfunction: get_forward_jump_instr

  static function riscv_instr get_clear_fflags_instr();
    riscv_instr clear_fflags_instr;
    clear_fflags_instr = riscv_instr::get_instr(CSRRCI);
    clear_fflags_instr.csr = FFLAGS;
    clear_fflags_instr.rd = ZERO; // makes it CSRCI
    clear_fflags_instr.imm_str = "0x1f";
    return clear_fflags_instr;
  endfunction: get_clear_fflags_instr

  static function riscv_instr get_nop_instr();
    riscv_instr nop_instr;
    nop_instr = riscv_instr::get_instr(NOP);
    return nop_instr;
  endfunction: get_nop_instr

  static function riscv_instr get_random_forward_branch_instr();
    riscv_instr branch_instr;
    branch_instr = riscv_instr::get_rand_instr(.include_category({BRANCH}));
    `DV_CHECK_RANDOMIZE_FATAL(branch_instr, ,"riscv_common_functions")
    branch_instr.imm_str = "1f";
    branch_instr.branch_assigned = 1'b1;
    branch_instr.has_label = 1'b1;
    return branch_instr;
  endfunction: get_random_forward_branch_instr

  // get a random half precision floating value
  static function bit [15:0] get_rand_hpf_value(
    int infinity_weight     = 1,       // Default weight for infinity
    int largest_weight      = 1,       // Default weight for largest value
    int zero_weight         = 1,       // Default weight for zero
    int nan_weight          = 1,       // Default weight for NaN
    int normal_weight       = 1,       // Default weight for normal values
    int subnormal_weight    = 1        // Default weight for subnormal values
  );
      bit [15:0] value;

      randcase
          // Infinity
          infinity_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {16'h7C00, 16'hFC00};,
            ,
            "riscv_common_functions"
          )
          // largest
          largest_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {16'h7BFF, 16'hFBFF};,
            ,
            "riscv_common_functions"
          )
          // zero
          zero_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {16'h0000, 16'h8000};,
            ,
            "riscv_common_functions"
          )
          // NaN
          nan_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              &value[14:HALF_PRECISION_FRACTION_BITS] == 1; // max exponent
              value[HALF_PRECISION_FRACTION_BITS-1:0] > 0; // nonzero mantissa
            }, ,
            "riscv_common_functions"
          )
          // normal
          normal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              value[14:HALF_PRECISION_FRACTION_BITS] > 0; // not zero or denorm or inf
              &value[14:HALF_PRECISION_FRACTION_BITS] != 1; // not NaN or inf
            }, ,
            "riscv_common_functions"
          )
          // subnormal
          subnormal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              value[14:HALF_PRECISION_FRACTION_BITS] == 0; // exp zero
              value[HALF_PRECISION_FRACTION_BITS-1:0] > 0; // nonzero mantissa
            }, ,
            "riscv_common_functions"
          )
      endcase
      return value;
  endfunction

  // get a random single precision floating value
  static function bit [XLEN-1:0] get_rand_spf_value(
    int infinity_weight     = 1,       // Default weight for infinity
    int largest_weight      = 1,       // Default weight for largest value
    int zero_weight         = 1,       // Default weight for zero
    int nan_weight          = 1,       // Default weight for NaN
    int normal_weight       = 1,       // Default weight for normal values
    int subnormal_weight    = 1        // Default weight for subnormal values
  );
      bit [31:0] value;

      randcase
          // Infinity
          infinity_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {32'h7f80_0000, 32'hff80_0000};,
            ,
            "riscv_common_functions"
          )
          // largest
          largest_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {32'h7f7f_ffff, 32'hff7f_ffff};,
            ,
            "riscv_common_functions"
          )
          // zero
          zero_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            value inside {32'h0000_0000, 32'h8000_0000};,
            ,
            "riscv_common_functions"
          )
          // NaN
          nan_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              &value[30:SINGLE_PRECISION_FRACTION_BITS] == 1; // max exponent
              value[SINGLE_PRECISION_FRACTION_BITS-1:0] > 0; // nonzero mantissa
            }, ,
            "riscv_common_functions"
          )
          // normal
          normal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              value[30:SINGLE_PRECISION_FRACTION_BITS] > 0; // not zero or denorm or inf
              &value[30:SINGLE_PRECISION_FRACTION_BITS] != 1; // not NaN or inf
            }, ,
            "riscv_common_functions"
          )
          // subnormal
          subnormal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
            value,
            {
              value[30:SINGLE_PRECISION_FRACTION_BITS] == 0; // exp zero
              value[SINGLE_PRECISION_FRACTION_BITS-1:0] > 0; // nonzero mantissa
            }, ,
            "riscv_common_functions"
          )
      endcase
      return value;
  endfunction

  // get a random double precision floating value
  static function bit [XLEN-1:0] get_rand_dpf_value(
    int infinity_weight = 1,       // Default weight for infinity
    int largest_weight  = 1,       // Default weight for largest value
    int zero_weight     = 1,       // Default weight for zero
    int nan_weight      = 1,       // Default weight for NaN
    int normal_weight   = 1,       // Default weight for normal values
    int subnormal_weight = 1       // Default weight for subnormal values
  );
    bit [63:0] value;

    randcase
      // infinity
      infinity_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7ff0_0000_0000_0000, 64'hfff0_0000_0000_0000};, , "riscv_common_functions")
      // largest
      largest_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7fef_ffff_ffff_ffff, 64'hffef_ffff_ffff_ffff};, , "riscv_common_functions")
      // zero
      zero_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h0000_0000_0000_0000, 64'h8000_0000_0000_0000};, , "riscv_common_functions")
      // NaN
      nan_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value inside {64'h7ff0_0000_0000_0001, 64'h7ff8_0000_0000_0000};, , "riscv_common_functions")
      // normal
      normal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value[62:DOUBLE_PRECISION_FRACTION_BITS] > 0;, , "riscv_common_functions")
      // subnormal
      subnormal_weight: `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(value,
             value[62:DOUBLE_PRECISION_FRACTION_BITS] == 0;, , "riscv_common_functions")
    endcase
    return value;
  endfunction

//endpackage
endclass
