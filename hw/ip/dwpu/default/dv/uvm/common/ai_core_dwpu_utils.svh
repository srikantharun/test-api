`ifndef AI_CORE_DWPU_UTILS_SVH
`define AI_CORE_DWPU_UTILS_SVH

class ai_core_dwpu_utils extends uvm_component;
  `uvm_component_utils(ai_core_dwpu_utils)

  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

  endfunction : build_phase


  static function bit get_read_input (dwpu_dp_command_t a_instr);
    //get input data stream
    get_read_input = 0;
    foreach (a_instr.i_sel[i]) begin
      if ((a_instr.i_sel[i] == 1) && (a_instr.op_desc.op_exe)) get_read_input = 1;
    end
    get_read_input = get_read_input || a_instr.op_desc.shift_sp|| a_instr.op_desc.shift_wb;

  endfunction : get_read_input

  static function int get_cmd_num_rows (aic_dp_cmd_gen_pkg::cmd_format_e cmd_format);
    /** update get_cmd_num_rows variable depending on the format type */
    case (cmd_format)
      aic_dp_cmd_gen_pkg::Bypass : begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_BYPASS;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N0: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M1N0;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N1: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M1N1;
      end
      aic_dp_cmd_gen_pkg::LoopsM1N2: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M1N2;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N0: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M2N0;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N1: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M2N1;
      end
      aic_dp_cmd_gen_pkg::LoopsM2N2: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M2N2;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N0: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M3N0;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N1: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M3N1;
      end
      aic_dp_cmd_gen_pkg::LoopsM3N2: begin
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M3N2;
      end
      default: begin
        $info($sformatf("%s format not implemented yet",cmd_format.name()));
        //by default the M1N2 command format is used
        get_cmd_num_rows = DWPU_CMD_NUM_ROWS_M1N2;
      end
    endcase

    return get_cmd_num_rows;
  endfunction : get_cmd_num_rows


  static function  pack_instr2data (dwpu_dp_command_t a_instr, ref bit [AIC_LT_AXI_DATA_WIDTH-1:0] a_data_da[]);
    int l_size = DWPU_INSTR_NUM_ROWS;
    int l_init_size = a_data_da.size();
    a_data_da = new[l_size+a_data_da.size()] (a_data_da);
    for(int i= 0; i<l_size; i++) begin
      a_data_da[i+l_init_size] = a_instr[(i) * AIC_LT_AXI_DATA_WIDTH +: AIC_LT_AXI_DATA_WIDTH];
    end
  endfunction : pack_instr2data

endclass : ai_core_dwpu_utils
`endif
