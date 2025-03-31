/**
 * Sequence that is responsible to randomize and write the command into DWPU
 */
class ai_core_dwpu_cmd_sequence extends svt_axi_master_base_sequence;

  /** pointer to cmd information */
  ai_core_dp_cmd_gen_uvm_pkg::ai_core_dp_cmd_gen_cmdb   cmd_info;

  rand dwpu_cmd_header_t header;
  rand bit enable_tokens;

  constraint c_soft_tokens {
    soft enable_tokens == 1'b0; //by default tokens are disabled
  }

  constraint c_sanity_header {

    if(enable_tokens == 1'b0) {
      header.token_cons == 1'b0;
      header.token_prod == 1'b0;
    }
    else {
      header.token_cons inside {[0:1]};
      header.token_prod inside {[0:3]}; //token prod has the trace valid signal on the highest bit
    }

    header.h_config     == 0;
    header.rsvd_format  == 0;
    header.rsvd         == 0;
    header.triggers     == 0;
  }

  `uvm_object_utils(ai_core_dwpu_cmd_sequence)

  function new(string name = "ai_core_dwpu_cmd_sequence");
    super.new(name);
  endfunction

  extern function void post_randomize();
  extern virtual function string convert2string();
  extern task body();
  extern function void get_packed_data_from_cmd(ref axi_lp_data_t a_data_da[]);
  extern task send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[]);

endclass : ai_core_dwpu_cmd_sequence

function void ai_core_dwpu_cmd_sequence::post_randomize();
  `uvm_info("post_randomize", $sformatf("Command: \n%s", convert2string()), UVM_HIGH)
endfunction : post_randomize

function string ai_core_dwpu_cmd_sequence::convert2string();
  string s = super.convert2string();
  s = {s, $sformatf("\n---------------------------------------------") };
  s = {s, $sformatf("\n name                :   %s"   , get_name()            ) };
  s = {s, $sformatf("\n ID                  :   0x%0x", get_inst_id()         ) };
  s = {s, $sformatf("\n header"                                               ) };
  s = {s, $sformatf("\n   config            :   %0s"  , header.h_config       ) };
  s = {s, $sformatf("\n   rsvd_format       :   %0s"  , header.rsvd_format    ) };
  s = {s, $sformatf("\n   format            :   %0s"  , header.format.name()  ) };
  s = {s, $sformatf("\n   token_cons        :   %0d"  , header.token_cons     ) };
  s = {s, $sformatf("\n   token_prod        :   %0d"  , header.token_prod     ) };
  s = {s, $sformatf("\n   rsvd              :   %0d"  , header.rsvd           ) };
  s = {s, $sformatf("\n   triggers          :   %0d"  , header.triggers       ) };
  s = {s, $sformatf("\n%s", cmd_info.sprint())};
  return s;
endfunction : convert2string

task ai_core_dwpu_cmd_sequence::body();

  svt_configuration get_cfg;
  bit status;
  axi_lp_data_t l_data_from_cmd[];


  /** Obtain a handle to the port configuration */
  p_sequencer.get_cfg(get_cfg);
  if (!$cast(cfg, get_cfg)) begin
    `uvm_fatal("body", "Unable to $cast the configuration to a svt_axi_port_configuration class");
  end

  //get array of data from command
  get_packed_data_from_cmd(l_data_from_cmd);

  //TODO redo this print
  //`uvm_info("body", $sformatf("writing cmd: %p", cmd), UVM_HIGH)
  foreach(l_data_from_cmd[i]) `uvm_info("body", $sformatf("writing data[%0d]: 0x%0x", i, l_data_from_cmd[i]), UVM_HIGH)
  send_write(DWPU_CMD_ST_ADDR, l_data_from_cmd);
endtask : body

function void ai_core_dwpu_cmd_sequence::get_packed_data_from_cmd(ref axi_lp_data_t a_data_da[]);
  int l_offset = a_data_da.size();
  int num_rows;
  `uvm_info("get_packed_data_from_cmd", $sformatf("Start packing cmd into array of data"), UVM_HIGH)
  /** Depending on the command format, copy the necessary variables to the command that will be sent */
  case (header.format)
    aic_dp_cmd_gen_pkg::Bypass : begin
      a_data_da = new[l_offset + (DWPU_CMD_NUM_ROWS_BYPASS+1)] (a_data_da);
      a_data_da[l_offset+0] = header;
    end
    aic_dp_cmd_gen_pkg::LoopsM1N0: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m1n0_t cmd;
      cmd.main_0 = cmd_info.main_0;
      cmd.extra  = cmd_info.extra;
      num_rows = DWPU_CMD_NUM_ROWS_M1N0;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM1N1: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m1n1_t cmd;
      cmd.nested_0_map_main  = cmd_info.nested_0_map_main;
      cmd.nested_0           = cmd_info.nested_0;
      cmd.extra              = cmd_info.extra;
      cmd.main_0             = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M1N1;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM1N2: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m1n2_t cmd;
      cmd.nested_1_map_main  = cmd_info.nested_1_map_main;
      cmd.nested_1           = cmd_info.nested_1;
      cmd.nested_0_map_main  = cmd_info.nested_0_map_main;
      cmd.nested_0           = cmd_info.nested_0;
      cmd.extra              = cmd_info.extra;
      cmd.main_0             = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M1N2;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM2N0: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m2n0_t cmd;
      cmd.reserved_0  = cmd_info.reserved_0;
      cmd.main_1      = cmd_info.main_1;
      cmd.extra       = cmd_info.extra;
      cmd.main_0      = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M2N0;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM2N1: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m2n1_t cmd;
      cmd.nested_0_map_main   = cmd_info.nested_0_map_main;
      cmd.nested_0            = cmd_info.nested_0;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_1              = cmd_info.main_1;
      cmd.extra               = cmd_info.extra;
      cmd.main_0              = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M2N1;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM2N2: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m2n2_t cmd;
      cmd.nested_1_map_main   = cmd_info.nested_1_map_main ;
      cmd.nested_1            = cmd_info.nested_1 ;
      cmd.nested_0_map_main   = cmd_info.nested_0_map_main ;
      cmd.nested_0            = cmd_info.nested_0 ;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_1              = cmd_info.main_1;
      cmd.extra               = cmd_info.extra ;
      cmd.main_0              = cmd_info.main_0 ;
      num_rows = DWPU_CMD_NUM_ROWS_M2N2;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM3N0: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m3n0_t cmd;
      cmd.reserved_0  = cmd_info.reserved_0;
      cmd.main_2      = cmd_info.main_2;
      cmd.reserved_0  = cmd_info.reserved_0;
      cmd.main_1      = cmd_info.main_1;
      cmd.extra       = cmd_info.extra;
      cmd.main_0      = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M3N0;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM3N1: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m3n1_t cmd;
      cmd.nested_0_map_main   = cmd_info.nested_0_map_main;
      cmd.nested_0            = cmd_info.nested_0;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_2              = cmd_info.main_2;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_1              = cmd_info.main_1;
      cmd.extra               = cmd_info.extra;
      cmd.main_0              = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M3N1;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    aic_dp_cmd_gen_pkg::LoopsM3N2: begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m3n2_t cmd;
      cmd.nested_1_map_main   = cmd_info.nested_1_map_main ;
      cmd.nested_1            = cmd_info.nested_1 ;
      cmd.nested_0_map_main   = cmd_info.nested_0_map_main ;
      cmd.nested_0            = cmd_info.nested_0 ;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_2              = cmd_info.main_2;
      cmd.reserved_0          = cmd_info.reserved_0;
      cmd.main_1              = cmd_info.main_1;
      cmd.extra               = cmd_info.extra ;
      cmd.main_0              = cmd_info.main_0 ;
      num_rows = DWPU_CMD_NUM_ROWS_M3N2;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
    default : begin
      ai_core_dp_cmd_gen_uvm_pkg::cmdb_cmd_m1n2_t cmd;
      `uvm_warning(get_name, $sformatf("%0d format not implemented yet",header.format));
      //to make sure the command goes to the DUT if the format is not implemented, by default we build a M1N2 command
      cmd.nested_1_map_main  = cmd_info.nested_1_map_main;
      cmd.nested_1           = cmd_info.nested_1;
      cmd.nested_0_map_main  = cmd_info.nested_0_map_main;
      cmd.nested_0           = cmd_info.nested_0;
      cmd.extra              = cmd_info.extra;
      cmd.main_0             = cmd_info.main_0;
      num_rows = DWPU_CMD_NUM_ROWS_M1N2;
      a_data_da = new[l_offset + (num_rows+1)] (a_data_da);
      for(int i = 0; i<=num_rows; i++) begin
        if(i==0)  a_data_da[l_offset+i] = header;
        else      a_data_da[l_offset+i] = cmd[(i-1) * AXI_LT_DATA_WIDTH +: AXI_LT_DATA_WIDTH];
      end
    end
  endcase
endfunction : get_packed_data_from_cmd


task ai_core_dwpu_cmd_sequence::send_write(axi_lp_addr_t a_addr, axi_lp_data_t a_data_da[]);
  axi_master_write_split_sequence write_seq;

  foreach (a_data_da[i])`uvm_info("send_write", $sformatf("Sending data[%0d] = 0x%0x", i, a_data_da[i]), UVM_HIGH)
  /** create sequence from type axi_master_write_sequence */
  `uvm_create(write_seq)
  //randomize transaction
  if(!write_seq.randomize() with {
    incr_addr_between_bursts == 0; //into the command fifo we don't want to increment the address between bursts. Always write to the base address of CMD fifo
    cfg_addr        == a_addr;
    cfg_data.size == a_data_da.size;
    foreach(cfg_data[i]) {
      cfg_data[i] == a_data_da[i];
    }
  }) `uvm_fatal(get_name, "write_tran randomization error!");

  //start sequence
  write_seq.start(m_sequencer);
  `uvm_info("send_write", $sformatf("Finish the sending of write sequence"), UVM_HIGH)

endtask : send_write

