
# Set the following variables

# Change the following variable if you change the template
set SPEC_NAME DPV_wrapper

# File of the model
set SPEC_FILE imc_bank.cpp

# Name for the implementation
set IMPL_NAME <name>

set CLK i_clk
set RSTN i_rst_n


proc global_assumes {} {
  # Specify the assumes of you block
  # you can map by name the inputs of the spec and the impl
  # you can split them if the inputs are MDA 
  # -split "spec.in_tdata_i impl.in_tdata_i spec.in_tdata_o impl.in_tdata_o"
  map_by_name -inputs -specphase 1 -implphase 1
  
  # Loops can be used to connect map internal signals/regs
  # global PWORD
  # for {set i 0} {$i < 8} {incr i} {
  #   for {set j 0} {$j < ${PWORD}} {incr j} {
  #     assume reg_${i}_${j} = impl.acc_reg_q(1)[${i}][${j}] == spec.acc(1)[${i}][${j}];
  #   }
  # }

  # Use assume to constraint input signals
  # assume dpcmd_tvalid_i = impl.dpcmd_tvalid_i(1) == 1;
  # assume fix_opcode = spec.dpcmd_tdata_i.opcode(1) < 5;

}

proc ual {} {
  global_assumes

  # Use lemma to create the check between impl and spec
  # DPV uses phases instead of clocks. 1 clock cycles means 2 phases, rising and falling phases
  # Like assumes, you can use loops to generate the lemmas (similar to assert in SVA)
  # global PWORD
  # for {set i 0} {$i < 8} {incr i} {
  #   for {set j 0} {$j < ${PWORD}} {incr j} {
  #       lemma check_regs_${i}_${j} = impl.acc_reg_q(3)[${i}][${j}] == spec.acc(3)[${i}][${j}];
  #   }
  # }

}

proc proc_run_preparation {} {
  # Select specific solve scripts
  # set_hector_multiple_solve_scripts_list [list orch_sat_bb]

  set_user_assumes_lemmas_procedure "ual"
  #set_hector_case_splitting_procedure "case_split"

  # Give a name to the proof 
  # you can use a specific orchestration for the proof with:
  # -script orch_sat_bb
  solveNB <name> -ual ual
  proofwait <name>

}
