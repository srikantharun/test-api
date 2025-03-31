//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq.sv
// Unit Name   : lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq
//--------------------------------------------------------------------------------------

class lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq extends lpddr_subsystem_base_virtual_seq;

  `uvm_object_utils(lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq)

  lpddr_subsystem_axi_scheduler_seq scheduler_seq;

  axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;
  
  uvm_status_e status;
  randc bit [31:0] wr_data[];
  randc bit [31:0] wr_data_for_dbi[];
  rand bit dbi_en, dm_en;
  rand bit wck_on, ws_off_en, wck_suspend_en;
  randc bit [7:0] dfi_twck_en_rd, dfi_twck_en_wr, dfi_twck_en_fs, dfi_twck_dis;
  randc bit [7:0] dfi_twck_fast_toggle, dfi_twck_toggle, dfi_twck_toggle_cs, dfi_twck_toggle_post;
  real test_scenario;

  //Constarints
  //constraint size_cons         {wr_data.size() == $urandom;
  //                              wr_data_for_dbi.size() == $urandom;}
  //constraint data_dbi_cons     {foreach (wr_data_for_dbi[i]) $countones(wr_data_for_dbi[i]) > 4;}
  //constraint data_cons         {foreach (wr_data[i]) $countones(wr_data[i]) <= 4;}
  constraint dbi_en_cons         {dbi_en inside {0,1};}
  constraint dm_en_cons          {dm_en inside {0,1};}
  constraint wck_on_cons         {wck_on inside {0,1};}
  constraint ws_off_en_cons      {ws_off_en inside {0,1};}
  constraint wck_suspend_en_cons {wck_suspend_en inside {0,1};}

  //-------------------------------------------------------------------------
  // Function       : new
  // Arguments      : string name - Name of the object.
  // Description    : Constructor for fpga base scoreboard class objects.
  //-------------------------------------------------------------------------
  function new (string name = "lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq");
    super.new(name);
		scheduler_seq = lpddr_subsystem_axi_scheduler_seq::type_id::create("scheduler_seq");
  endfunction : new

  //-------------------------------------------------------------------------
  // Function       : generate_random_apb_configuration_values
  // Arguments      : None
  // Description    : This method used to randomize APB Registers.
  //-------------------------------------------------------------------------
  virtual task generate_random_apb_configuration_values();
    if(!this.randomize()) begin
			$fatal("Randomization Failed");
		end
    randcase
      1 : begin
            `uvm_do_on_with(axi_rd_xtnh, p_sequencer.axi_sqr,{read_or_write   == AXI4_TRANS_READ;})
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"rd_dbi_en",dbi_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",dm_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"rd_dbi_en",dbi_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",dm_en}}));
          end
      1 : begin
            `uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr,{read_or_write   == AXI4_TRANS_WRITE;
                                                              foreach(wdata_words[i]){wdata_words[i] == ($countones(wr_data[i]) <= 4);}})
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"wr_dbi_en",dbi_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",dm_en}}));
            `uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr,{foreach(wdata_words[i]){wdata_words[i] == ($countones(wr_data_for_dbi[i]) > 4);}})
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"wr_dbi_en",dbi_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",dm_en}}));
          end
    endcase
  endtask: generate_random_apb_configuration_values

  //-------------------------------------------------------------------------
  // Function       : generate_random_wck_clocking_configuration_values
  // Arguments      : None
  // Description    : This method used to randomize APB Registers for WCK Clocking.
  //-------------------------------------------------------------------------
  virtual task generate_random_wck_clocking_configuration_values();
    if(!this.randomize()) begin
			$fatal("Randomization Failed");
		end
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4,'{'{"wck_on",wck_on}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4,'{'{"ws_off_en",ws_off_en}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4,'{'{"wck_suspend_en",wck_suspend_en}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4,'{'{"dfi_twck_en_rd",dfi_twck_en_rd}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4,'{'{"dfi_twck_en_wr",dfi_twck_en_wr}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4,'{'{"dfi_twck_en_fs",dfi_twck_en_fs}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4,'{'{"dfi_twck_dis",dfi_twck_dis}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5,'{'{"dfi_twck_fast_toggle",dfi_twck_fast_toggle}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5,'{'{"dfi_twck_toggle",dfi_twck_toggle}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5,'{'{"dfi_twck_toggle_cs",dfi_twck_toggle_cs}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5,'{'{"dfi_twck_toggle_post",dfi_twck_toggle_post}}));
  endtask: generate_random_wck_clocking_configuration_values

  //-------------------------------------------------------------------------
  // Function       : body
  // Arguments      : None
  // Description    : 
  //-------------------------------------------------------------------------
  virtual task body();
    super.body();
  
      case(test_scenario)

				//Scenario for 1.4: Databus Inversion Test
				1 : begin
              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"phy_dbi_mode",0}}));
              repeat(10) begin
                $display("entering in body");
  			        generate_random_apb_configuration_values(); 
              end
            end
        //Scenario for 2.3: LPDDR5 WCK Clocking Test
			  2 : begin
              reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.TMGCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.TMGCFG,'{'{"frequency_ratio",1}}));
              repeat(10) begin
                generate_random_wck_clocking_configuration_values();
              end
		   	    end
	    endcase
  endtask : body
endclass : lpddr_subsystem_data_bus_inversion_wck_clocking_test_seq
