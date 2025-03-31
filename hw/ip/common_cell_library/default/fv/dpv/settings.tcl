
# Set the following variables

# Change the following variable if you change the template
set SPEC_NAME DPV_wrapper

# File of the model
set SPEC_FILE lfsr.cpp

# Name for the implementation
set IMPL_NAME cc_cnt_lfsr

set CLK i_clk
set RSTN i_rst_n


proc global_assumes {} {
  map_by_name -inputs -specphase 1 -implphase 1

  assume seed = spec.seed(1) == impl.state_o(1);

  assume clear = impl.clear_i(1) == 0;
  assume enable = impl.enable_i(1) == 1;
  assume taps = impl.taps_i(1) == ((1 << 0) | (1 << 1) | (1 << 3) | (1 << 12));
  assume mask_select = spec.mask_select_i(1) < 3;

  assume flip_enable = -always (spec.flip_enable_i(1) == impl.flip_enable_i);
  assume stable_mask_select = -always (spec.mask_select_i(1) == impl.mask_select_i);
  assume stable_mask_and = -always (spec.mask_and_i(1) == impl.mask_and_i);
  assume stable_mask_or = -always (spec.mask_or_i(1) == impl.mask_or_i);

}

proc ual {} {
  global_assumes
  lemma result = impl.state_o(3) == spec.state_o(1)
  lemma data_o = impl.data_o(2) == spec.data_o(1)

}

proc proc_run_preparation {} {
  # Select specific solve scripts
  # set_hector_multiple_solve_scripts_list [list orch_sat_bb]

  set_user_assumes_lemmas_procedure "ual"
  #set_hector_case_splitting_procedure "case_split"

  # Give a name to the proof 
  # you can use a specific orchestration for the proof with:
  # -script orch_sat_bb
  solveNB lfsr -ual ual
  proofwait lfsr

}
