
set SPEC_NAME DPV_wrapper
set SPEC_FILE iau_pixel_dp.cpp

set IMPL_NAME iau_pixel_dp

set CLK i_clk
set RSTN i_rst_n

set COV 1

proc global_assumes {} {
  map_by_name -inputs -specphase 1 -implphase 1 -exclude "spec.instr_src_stream spec.instr_src_acc_reg impl.instr_src_stream impl.instr_src_acc_reg"
  assume instr_src_stream_0 = spec.instr_src_stream[0](1) == impl.instr_src_stream[0](1)
  assume instr_src_stream_1 = spec.instr_src_stream[1](1) == impl.instr_src_stream[1](1)
  assume instr_src_acc_reg_0 = spec.instr_src_acc_reg[0](1) == impl.instr_src_acc_reg[0](1)
  assume instr_src_acc_reg_1 = spec.instr_src_acc_reg[1](1) == impl.instr_src_acc_reg[1](1)
  #-split "spec.instr_src_stream spec.instr_src_acc_reg"

  for {set i 0} {$i < 8} {incr i} {
    assume reg_${i} = impl.acc_reg_q(1)[${i}] == spec.acc(1)[${i}];
  }

  assume opcode = spec.instr_opcode(1) < 5;
  assume dst = spec.instr_dst_acc_reg(1) < 8;
  assume src0 = spec.instr_src_acc_reg[0](1) < 8;
  assume src1 = spec.instr_src_acc_reg[1](1) < 8;

  assume instr_dst_used = (spec.instr_opcode(1) == 0) |-> (spec.instr_dst_used(1) == 0);

  assume vector_mode = (spec.vector_mode(1) == 0); # no int16 support just yet
}

proc ual {} {
  global_assumes

  for {set i 0} {$i < 8} {incr i} {
    lemma check_regs_${i} = (impl.acc_reg_q[${i}](3) == spec.acc[${i}](3));
  }

  lemma out_tdata = (impl.instr_dst_stream(1) && impl.exe_instr(1) && impl.instr_dst_used(1)) |-> (impl.o_pixel_data(3) == spec.o_pixel_data(1));

}

proc proc_run_preparation {} {
  # Select specific solve scripts
  # set_hector_multiple_solve_scripts_list [list orch_sat_bb]

  set_user_assumes_lemmas_procedure "ual"
  #set_hector_case_splitting_procedure "case_split"

  solveNB iau_pixel_dp -ual ual
  #-script orch_sat_bb

  proofwait iau_pixel_dp

}
