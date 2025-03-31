`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_COV_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_COV_SVH

`define _loop_cov_(T,I) \
    cp_``T``_``I``_start : coverpoint cmdb.``T``_``I``.start iff (cmdb.``T``_valid(``I``)) {                                 \
      bins lo[]   = {[0:2]};                                                                                                 \
      bins hi[]   = {[`AIC_DP_CMD_GEN_COMMAND_DEPTH-2:`AIC_DP_CMD_GEN_COMMAND_DEPTH-1]};                                         \
      bins others = {[3:`AIC_DP_CMD_GEN_COMMAND_DEPTH-3]};                                                                     \
    }                                                                                                                        \
    cp_``T``_``I``_length : coverpoint cmdb.``T``_``I``.length iff (cmdb.``T``_valid(``I``)) {                               \
       bins lo[]   = {[1:3]};                                                                                                \
       bins hi[]   = {[`AIC_DP_CMD_GEN_COMMAND_DEPTH-2:`AIC_DP_CMD_GEN_COMMAND_DEPTH-1]};                                        \
       bins others = {[3:`AIC_DP_CMD_GEN_COMMAND_DEPTH-3]};                                                                    \
    }                                                                                                                        \
    cp_``T``_``I``_iteration : coverpoint cmdb.``T``_``I``.iteration iff (cmdb.``T``_valid(``I``)) {                         \
       bins lo[]   = {[24'h1:24'h3]};                                                                                        \
       bins hi[]   = {[24'hfffffd:24'hffffff]};                                                                              \
       bins others = {[24'h3:24'hfffffc]};                                                                                   \
    }                                                                                                                        \
    cp_``T``_``I``_length_x_iteration : cross cp_``T``_``I``_length, cp_``T``_``I``_iteration iff (cmdb.``T``_valid(``I``));

class ai_core_dp_cmd_gen_cmdb_cov extends uvm_subscriber #(ai_core_dp_cmd_gen_cmdb);

  ai_core_dp_cmd_gen_cmdb           cmdb;
  ai_core_dp_cmd_gen_cmdb           cmdbQ[$];
  virtual dp_cmd_gen_cmdb_if        cmdb_vif;

  `uvm_component_utils(ai_core_dp_cmd_gen_cmdb_cov)

  uvm_analysis_port#(ai_core_dp_cmd_gen_cmdb) ap;

  // Covergroups
  covergroup basic_cg;
    option.per_instance = 1'b1;
    option.name         = "basic_cg";

    // Basic format coverage
    cp_format            : coverpoint cmdb.get_format();
    cp_prev_format       : coverpoint cmdbQ[1].get_format() iff (cmdbQ.size() >= 2);
    cp_format0_x_format1 : cross cp_format, cp_prev_format  iff (cmdbQ.size() >= 2); 
    
    // Basic extra coverage
    cp_extra  : coverpoint cmdb.extra {
      bins extra[8]     = {[0:$]};
    }

    // Basic loop coverage
    `_loop_cov_(main,0)
    `_loop_cov_(main,1)
    `_loop_cov_(main,2)
    `_loop_cov_(nested,0)
    `_loop_cov_(nested,1)

    // Parallel or nested
    cp_parallel : coverpoint cmdb.is_parallel() iff (cmdb.co_nested());

    // Distance between nested loops
    cp_nested_delta : coverpoint (cmdb.get_start(1'b0, 1) - cmdb.get_end(1'b0, 0)) iff (cmdb.co_nested()) {
      bins lo[]   = {[0:2]};
      bins others = {[3:$]};
    }

    // Interesting edge corner cases
    // main and nested_0 have same start (shoot through)
    cp_simultaneous_main_and_nested_0_start     : coverpoint (cmdb.get_start(1'b1, cmdb.nested_0_map_main) == cmdb.get_start(1'b0, 0)) iff (cmdb.nested_valid(0));

    // nested_0 and nested_1 have same start (shoot through)
    cp_simultaneous_nested_0_and_nested_1_start : coverpoint (cmdb.get_start(1'b0, 0) == cmdb.get_start(1'b0, 1)) iff (cmdb.co_nested());

    // main, nested_0 and nested_1 all have same start (double shoot through)
    cp_simultaneous_main_nested_0_and_nested_1_start : coverpoint cmdb.nested_0_map_main iff ((cmdb.get_start(1'b1, cmdb.nested_0_map_main) == cmdb.get_start(1'b0, 0)) && (cmdb.get_start(1'b1, cmdb.nested_0_map_main) == cmdb.get_start(1'b0, 1)) && cmdb.co_nested()) {
      bins map[] = {[0:2]};
    }

     // main and nested_0 have same end (shoot through)
    cp_simultaneous_main_and_nested_0_end     : coverpoint (cmdb.get_end(1'b1, cmdb.nested_0_map_main) == cmdb.get_end(1'b0, 0)) iff (cmdb.nested_valid(0));

    // nested_0 and nested_1 have same end (shoot through)
    cp_simultaneous_nested_0_and_nested_1_end : coverpoint (cmdb.get_end(1'b0, 0) == cmdb.get_end(1'b0, 1)) iff (cmdb.co_nested());

    // main, nested_0 and nested_1 all have same end (double shoot through)
    cp_simultaneous_main_nested_0_and_nested_1_end : coverpoint cmdb.nested_0_map_main iff ((cmdb.get_end(1'b1, cmdb.nested_0_map_main) == cmdb.get_start(1'b0, 0)) && (cmdb.get_start(1'b1, cmdb.nested_0_map_main) == cmdb.get_end(1'b0, 1)) && cmdb.co_nested()) {
      bins map[] = {[0:2]};
    }   

    // Temporal Coverage
    // Number of cycles between valid, ready and done
    cp_ready_delay : coverpoint (cmdb.ready_cycle - cmdb.valid_cycle) {
      bins lo[]    = {[0:2]};
      bins others  = {[3:$]};
    }
    
    cp_done_delay : coverpoint (cmdb.done_cycle - cmdb.ready_cycle) {
      bins lo[]   = {[1:3]};
      bins others = {[3:$]};
    } 

  endgroup

  covergroup error_cg;
    option.per_instance = 1'b1;
    option.name         = "error_cg";

    // Errors
    cp_error_illegal_format    : coverpoint cmdb.errors.illegal_format;
    cp_error_empty_program     : coverpoint cmdb.errors.empty_program;
    cp_error_main_0_length     : coverpoint cmdb.errors.main_0_length;
    cp_error_main_1_length     : coverpoint cmdb.errors.main_1_length;
    cp_error_main_2_length     : coverpoint cmdb.errors.main_2_length;
    cp_error_nested_0_length   : coverpoint cmdb.errors.nested_0_length;
    cp_error_nested_1_length   : coverpoint cmdb.errors.nested_1_length;
    cp_error_nested_0_mapping  : coverpoint cmdb.errors.nested_0_mapping;
    cp_error_nested_1_mapping  : coverpoint cmdb.errors.nested_1_mapping;
    cp_error_nested_0_segfault : coverpoint cmdb.errors.nested_0_segfault;
    cp_error_nested_1_segfault : coverpoint cmdb.errors.nested_1_segfault;
    cp_error_nested_order      : coverpoint cmdb.errors.nested_order;
    cp_error_nested_nesting    : coverpoint cmdb.errors.nested_nesting;
    cp_error_nested_overlap    : coverpoint cmdb.errors.nested_overlap;

    cp_error_sequence          : coverpoint {|cmdbQ[2].errors, |cmdbQ[1].errors, |cmdbQ[0].errors} iff (cmdbQ.size() == 3);
  endgroup

  function new (string name, uvm_component parent);
    super.new (name, parent);
    basic_cg = new();
    error_cg = new();
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db #(virtual dp_cmd_gen_cmdb_if)::get(this, "", "cmdb_vif", cmdb_vif)); 
  endfunction : build_phase

  function void write(input ai_core_dp_cmd_gen_cmdb t);
    this.cmdb = t;

    // Keep history of last 3 cmdbs
    this.cmdbQ.push_front(t);
    if (this.cmdbQ.size() > 3)
      void'(this.cmdbQ.pop_back());

    if (this.cmdb.errors == '0)
      basic_cg.sample();
    
    error_cg.sample();

  endfunction : write
endclass : ai_core_dp_cmd_gen_cmdb_cov

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_COV_SVH
