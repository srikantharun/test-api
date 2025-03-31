`ifndef AI_CORE_DP_CMD_GEN_UTILS_SVH
`define AI_CORE_DP_CMD_GEN_UTILS_SVH

class ai_core_dp_cmd_gen_utils extends uvm_component;
  `uvm_component_utils(ai_core_dp_cmd_gen_utils)

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

  endfunction : build_phase

  static function ai_core_dp_cmd_gen_cmdb get_full_cmd_from_alternative_cmd (bit [$bits(aic_dp_cmd_gen_pkg::cmdb_cmd_t)-1:0] cmd, aic_dp_cmd_gen_pkg::cmd_format_e cmd_format);
    /** create command to send to model and set common variables */
    ai_core_dp_cmd_gen_cmdb full_cmd = ai_core_dp_cmd_gen_cmdb::type_id::create("full_cmd");
    full_cmd.format = cmd_format;
    full_cmd.valid = 1;
    //cast the current aux_cmd to the correspondent format
    case (cmd_format)
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        cmdb_cmd_m1n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.main_0 = aux_cmd.main_0;
        full_cmd.extra  = aux_cmd.extra;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        cmdb_cmd_m1n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main  = aux_cmd.nested_0_map_main;
        full_cmd.nested_0           = aux_cmd.nested_0;
        full_cmd.extra              = aux_cmd.extra;
        full_cmd.main_0             = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        cmdb_cmd_m1n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main  = aux_cmd.nested_1_map_main;
        full_cmd.nested_1           = aux_cmd.nested_1;
        full_cmd.nested_0_map_main  = aux_cmd.nested_0_map_main;
        full_cmd.nested_0           = aux_cmd.nested_0;
        full_cmd.extra              = aux_cmd.extra;
        full_cmd.main_0             = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        cmdb_cmd_m2n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_1      = aux_cmd.main_1;
        full_cmd.extra       = aux_cmd.extra;
        full_cmd.main_0      = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        cmdb_cmd_m2n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main;
        full_cmd.nested_0            = aux_cmd.nested_0;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra;
        full_cmd.main_0              = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        cmdb_cmd_m2n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main   = aux_cmd.nested_1_map_main ;
        full_cmd.nested_1            = aux_cmd.nested_1 ;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main ;
        full_cmd.nested_0            = aux_cmd.nested_0 ;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra ;
        full_cmd.main_0              = aux_cmd.main_0 ;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        cmdb_cmd_m3n0_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_2      = aux_cmd.main_2;
        full_cmd.reserved_0  = aux_cmd.reserved_0;
        full_cmd.main_1      = aux_cmd.main_1;
        full_cmd.extra       = aux_cmd.extra;
        full_cmd.main_0      = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        cmdb_cmd_m3n1_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main;
        full_cmd.nested_0            = aux_cmd.nested_0;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_2              = aux_cmd.main_2;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra;
        full_cmd.main_0              = aux_cmd.main_0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        cmdb_cmd_m3n2_t aux_cmd;
        aux_cmd = cmd;
        full_cmd.nested_1_map_main   = aux_cmd.nested_1_map_main ;
        full_cmd.nested_1            = aux_cmd.nested_1 ;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main ;
        full_cmd.nested_0            = aux_cmd.nested_0 ;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_2              = aux_cmd.main_2;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra ;
        full_cmd.main_0              = aux_cmd.main_0 ;
      end
      default : begin
        //by default use m3n2
        cmdb_cmd_m3n2_t aux_cmd;
        $info($sformatf("Command format %0d not implemented", cmd_format));
        aux_cmd = cmd;
        full_cmd.nested_1_map_main   = aux_cmd.nested_1_map_main ;
        full_cmd.nested_1            = aux_cmd.nested_1 ;
        full_cmd.nested_0_map_main   = aux_cmd.nested_0_map_main ;
        full_cmd.nested_0            = aux_cmd.nested_0 ;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_2              = aux_cmd.main_2;
        full_cmd.reserved_0          = aux_cmd.reserved_0;
        full_cmd.main_1              = aux_cmd.main_1;
        full_cmd.extra               = aux_cmd.extra ;
        full_cmd.main_0              = aux_cmd.main_0 ;
      end
    endcase
    return full_cmd;

  endfunction : get_full_cmd_from_alternative_cmd


endclass : ai_core_dp_cmd_gen_utils
`endif
