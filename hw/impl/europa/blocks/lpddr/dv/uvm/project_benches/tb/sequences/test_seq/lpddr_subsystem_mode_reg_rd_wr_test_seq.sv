//------------------------------------------------------------------------------
// Project     : Axelera lpddr Subsystem
// File Name   : lpddr_subsystem_msi_generation_test_seq.sv
// Unit Name   : lpddr_subsystem_msi_generation_test_seq
//------------------------------------------------------------------------------
// Description : This file contains the base virtual sequence for the lpddr
//               Subsystem Verification Environment.
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST_SEQ 
`define LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST_SEQ 

class lpddr_subsystem_mode_reg_rd_wr_test_seq extends lpddr_subsystem_base_virtual_seq;

  `uvm_object_utils(lpddr_subsystem_mode_reg_rd_wr_test_seq)

  lpddr_subsystem_init_seq init_seq;

  uvm_status_e status;
  randc bit [1:0] mr_rank;
  randc bit [3:0] mr_addr;
  randc bit [17:0] mr_data;
  rand bit mr_type, mrr_done_clr, mrr_done;

  //Constarints
  constraint mr_type_cons         {mr_type inside {0,1};}
  constraint mrr_done_clr_cons    {mrr_done_clr inside {0,1};}
  constraint mrr_done_cons        {mrr_done inside {0,1};}

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments      : string name - Name of the object.
  // Description    : Constructor for fpga base scoreboard class objects.
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr_subsystem_mode_reg_rd_wr_test_seq");
    super.new(name);
  endfunction : new

  //-------------------------------------------------------------------------
  // Function       : generate_random_configuration_values
  // Arguments      : None
  // Description    : This method used to randomize APB Registers for WCK Clocking.
  //-------------------------------------------------------------------------
  virtual task generate_random_configuration_values();
    if(!this.randomize()) begin
			$fatal("Randomization Failed");
		end
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_rank",mr_rank}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_addr",mr_addr}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL1,'{'{"mr_data",mr_data}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_type",mr_type}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mrr_done_clr",mrr_done_clr}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRSTAT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRSTAT,'{'{"mrr_done",mrr_done}}));
  endtask: generate_random_configuration_values

  //-------------------------------------------------------------------------
  // Function       : body
  // Arguments      : None
  // Description    : 
  //-------------------------------------------------------------------------
  virtual task body();
    super.body();

    fork
    drive_global_rst_n();
    drive_ao_rst_n();
    join
    #10us;

    `uvm_do(init_seq);
    #100us;
    repeat(10) begin
      generate_random_configuration_values();
    end
  endtask : body

endclass
`endif //LPDDR_SUBSYSTEM_MODE_REG_RD_WR_TEST_SEQ
