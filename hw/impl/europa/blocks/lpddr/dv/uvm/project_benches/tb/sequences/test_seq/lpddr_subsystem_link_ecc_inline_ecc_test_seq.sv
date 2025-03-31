//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_link_ecc_inline_ecc_test_seq.sv
// Unit Name   : lpddr_subsystem_link_ecc_inline_ecc_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_link_ecc_inline_ecc_test_seq
//--------------------------------------------------------------------------------------

class lpddr_subsystem_link_ecc_inline_ecc_test_seq extends lpddr_subsystem_base_virtual_seq;

  `uvm_object_utils(lpddr_subsystem_link_ecc_inline_ecc_test_seq)

  lpddr_subsystem_axi_scheduler_seq scheduler_seq;

  axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;
  
  uvm_status_e status;
  randc bit [12:0] scrub_interval;
	randc bit [6:0] powerdown_to_x32;
	randc bit [9:0] selfref_to_x32;
	randc bit [31:0] sbr_address_start_mask_0, sbr_address_range_mask_0;
	randc bit [7:0]  sbr_address_start_mask_1, sbr_address_range_mask_1;
  rand bit scrub_during_lowpower;
	rand bit scrub_busy, scrub_done;
	rand bit powerdown_en, selfref_en, selfref_sw;
  real test_scenario;

  //Constarints
  constraint scrub_lowpower_cons {scrub_during_lowpower inside {0,1};}
  constraint scrub_busy_cons     {scrub_busy inside {0,1};}
  constraint scrub_done_cons     {scrub_done inside {0,1};}
  constraint powerdown_en_cons   {powerdown_en inside {0,1};}
  constraint selfref_en_cons     {selfref_en inside {0,1};}
  constraint selfref_sw_cons     {selfref_sw inside {0,1};}

  //-------------------------------------------------------------------------
  // Function       : new
  // Arguments      : string name - Name of the object.
  // Description    : Constructor for fpga base scoreboard class objects.
  //-------------------------------------------------------------------------
  function new (string name = "lpddr_subsystem_link_ecc_inline_ecc_test_seq");
    super.new(name);
		scheduler_seq = lpddr_subsystem_axi_scheduler_seq::type_id::create("scheduler_seq");
  endfunction : new

  //-------------------------------------------------------------------------
  // Function       : generate_random_configuration_values
  // Arguments      : None
  // Description    : This method used to randomize APB Registers.
  //-------------------------------------------------------------------------
  virtual task generate_random_configuration_values();
    if(!this.randomize()) begin
			$fatal("Randomization Failed");
		end
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG,'{'{"powerdown_to_x32",powerdown_to_x32}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG,'{'{"selfref_to_x32",selfref_to_x32}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART0,'{'{"sbr_address_start_mask_0",sbr_address_start_mask_0}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART1,'{'{"sbr_address_start_mask_1",sbr_address_start_mask_1}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE0,'{'{"sbr_address_range_mask_0",sbr_address_range_mask_0}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE1,'{'{"sbr_address_range_mask_1",sbr_address_range_mask_1}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT,'{'{"scrub_busy",scrub_busy}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT,'{'{"scrub_done",scrub_done}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_during_lowpower",scrub_during_lowpower}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",powerdown_en}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",selfref_en}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",selfref_sw}}));
    randcase
      1 : begin
            reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_interval",0}}));
          end
      1 : begin
            reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_interval",scrub_interval}}));
          end
      1 : begin
            reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_interval",powerdown_to_x32}}));
          end
      1 : begin
            reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_interval",selfref_to_x32}}));
          end
    endcase
  endtask: generate_random_configuration_values

  //-------------------------------------------------------------------------
  // Function       : body
  // Arguments      : None
  // Description    : 
  //-------------------------------------------------------------------------
  virtual task body();
    super.body();
  
      //case(test_scenario)

			//	//Scenario for 7.1: Link ECC Test
			//	1 : begin
      //      end
      //  //Scenario for 7.3: Inline ECC Test
			//  2 : begin
      //        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_wr",0}}));
		  // 	    end
      //  //Scenario for 7.4 Scrubber Status Test
      //  3 : begin
              reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_en",0}}));
              #10us; //Delay added between scrub_en value change
              reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_en",1}}));
              repeat(10) begin
                generate_random_configuration_values();
              end
		  // 	    end
	    //endcase
  endtask : body
endclass : lpddr_subsystem_link_ecc_inline_ecc_test_seq
