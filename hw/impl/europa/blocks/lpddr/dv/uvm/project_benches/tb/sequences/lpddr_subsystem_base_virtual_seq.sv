//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_base_virtual_seq.sv
// Unit Name   : lpddr_subsystem_base_virtual_seq
//------------------------------------------------------------------------------
// Description : This file contains the base virtual sequence for the LPDDR
//               Subsystem Verification Environment.
//------------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_BASE_VIRTUAL_SEQ_SVH
`define LPDDR_SUBSYSTEM_BASE_VIRTUAL_SEQ_SVH

`define GET_FIELD(REG_NAME,FIELD_NAME) field = REG_NAME.get_field_by_name(FIELD_NAME);
typedef struct {string name;bit [31:0] value;} field_t;
typedef class lpddr_subsystem_virtual_sequencer;
class lpddr_subsystem_base_virtual_seq extends uvm_sequence;

  `uvm_object_utils(lpddr_subsystem_base_virtual_seq)

  `uvm_declare_p_sequencer(lpddr_subsystem_virtual_sequencer);

  virtual subsystem_signal_intf m_io_vif;
  lpddr_subsystem_env_configuration         m_env_cfg;
  lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block reg_model;

  mvc_sequencer apb_master_0_sqr;
  mvc_sequencer apb_master_1_sqr;
  //mvc_sequencer axi4_master_0_sqr;

	//variable used to divide your procedure in different scenarios
  protected int test_scenario=1;

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //----------------------------------------------------------------------------
  function new ( string name = "lpddr_subsystem_base_virtual_seq");
    super.new(name);
    if(!uvm_config_db#(lpddr_subsystem_env_configuration)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",m_env_cfg)) begin
      `uvm_fatal("Config Error", "uvm_config_db #(lpddr_subsystem_env_configuration)::get() cannot find bfm config class handle")
    end
    if(!uvm_config_db#(virtual subsystem_signal_intf)::get(null,"UVMF_VIRTUAL_INTERFACES", "top_signals_intf",m_io_vif) && (m_io_vif == null)) begin
      `uvm_fatal("Config Error", "uvm_config_db #(subsystem_signal_intf)::get() cannot find interface  class handle for top_signals_intf")
    end

    if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"apb_master_0", apb_master_0_sqr) ) begin
      `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'apb_master_0'" )
    end
    if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"apb_master_1", apb_master_1_sqr) ) begin
      `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'apb_master_1'" )
    end
    //if ( !uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,"axi4_master_0", axi4_master_0_sqr) ) begin
    //  `uvm_error("Config Error" , "uvm_config_db #( mvc_sequencer )::get cannot find resource 'axi4_master_0'" )
    //end

    if(!uvm_config_db#(lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block)::get(null,"","reg_model",reg_model))
`uvm_error("lpddr_subsystem_apb_reg_block","reg model not found")

		get_test_scenario(test_scenario);

  endfunction : new

	//-------------------------------------------------------------------------------------------
	//Method 			: get_test_scenario
	//Arguement		: scn (ref): test_scneario variable  
	//Description	: this function gets the command line arguement and stores it
	//							in the variable "test_scenario"
	//-------------------------------------------------------------------------------------------	
	function void get_test_scenario(ref int scn);
     void'($value$plusargs("TEST_SCENARIO=%d",scn));
  endfunction:get_test_scenario

  //----------------------------------------------------------------------------
  // Task Name     : pre_body
  //----------------------------------------------------------------------------
  virtual task pre_body();
    uvm_phase starting_phase = get_starting_phase();

   `uvm_info(get_type_name(),"Entering sequence ...",UVM_LOW)

   if(starting_phase != null) begin
     uvm_phase run_phase = uvm_domain::get_common_domain().find(uvm_run_phase::get());

     `uvm_info(get_type_name(),$psprintf("%s pre_body() raising %0s objection.", get_sequence_path(), starting_phase.get_name()),UVM_NONE);
     starting_phase.raise_objection(this);

     `uvm_info(get_type_name(),$psprintf("%s pre_body() raising %0s objection.", get_sequence_path(), run_phase.get_name()),UVM_NONE);
     run_phase.raise_objection(this);
   end
  endtask : pre_body

  //----------------------------------------------------------------------------
  // Task Name     : body
  //----------------------------------------------------------------------------
  virtual task body();
  endtask : body

  //----------------------------------------------------------------------------
  // Task Name     : post_body
  //----------------------------------------------------------------------------
  virtual task post_body();
    uvm_phase starting_phase = get_starting_phase();

   if(starting_phase != null) begin
     uvm_phase run_phase = uvm_domain::get_common_domain().find(uvm_run_phase::get());

     `uvm_info(get_type_name(),$psprintf("%s pre_body() dropping %0s objection.", get_sequence_path(), starting_phase.get_name()),UVM_NONE);
     starting_phase.drop_objection(this);

     `uvm_info(get_type_name(),$psprintf("%s pre_body() dropping %0s objection.", get_sequence_path(), run_phase.get_name()),UVM_NONE);
     run_phase.drop_objection(this);
   end

   `uvm_info(get_type_name(),"Exiting sequence ...",UVM_LOW)
  endtask : post_body

  //----------------------------------------------------------------------------
  // Task Name   : drive_ao_rst_n
  // Arguments   : int duration_ns;
  // Dsecription : This method asserts the ao reset signal which drives
  //               pctl block
  //----------------------------------------------------------------------------
  task drive_ao_rst_n ( int NO_OF_DFICLK = 64);
    m_io_vif.i_ao_rst_n = 1'b1;
    #($urandom_range(0,100)*1ps);
    m_io_vif.i_ao_rst_n = 1'b0;
    repeat(NO_OF_DFICLK)
      #(1.25*1ns);
    m_io_vif.i_ao_rst_n = 1'b1;
  endtask : drive_ao_rst_n

  //----------------------------------------------------------------------------
  // Task Name   : drive_global_rst_n
  // Arguments   : int duration_ns;
  // Dsecription : This method asserts the global reset signal which drives
  //               pctl block
  //----------------------------------------------------------------------------
  task drive_global_rst_n ( int NO_OF_DFICLK = 64);
    m_io_vif.i_global_rst_n = 1'b1;
    #($urandom_range(0,100)*1ps);
    m_io_vif.i_global_rst_n = 1'b0;
    repeat(NO_OF_DFICLK) 
      #(1.25*1ns);
    m_io_vif.i_global_rst_n = 1'b1;
  endtask : drive_global_rst_n

  // -------------------------------------------------------------------------
  // Description : This method is to write on registers via APB
  // Method Name generate_write_value
  // Argument : reg_name : Which register to perform write, 
  //            fields   : Which specific register field to write
  // -------------------------------------------------------------------------
  virtual function bit[31:0] generate_write_value(uvm_reg reg_name, field_t fields[]);
    bit [31:0]reg_value;
    reg_value = reg_name.get_mirrored_value(); 
    foreach(fields[idx])begin
      uvm_reg_field field;
      `GET_FIELD(reg_name,fields[idx].name)
      for(int i = field.get_lsb_pos(); i < (field.get_lsb_pos()+field.get_max_size()-1); i++)
              reg_value[i] = fields[idx].value[i-field.get_lsb_pos()];
    end
    return reg_value;
  endfunction : generate_write_value

  virtual task configure_static_reg_during_reset();
   `uvm_info("configure_static_reg_during_reset","This should be set from testcase level sequence as per need of specific testing",UVM_LOW)
  endtask : configure_static_reg_during_reset
	
	//-------------------------------------------------------------------------------------------
	//Method 			: write_qd_reg
	//Arguements	: 
	//Description	:
	//-------------------------------------------------------------------------------------------	
	virtual task write_qd_reg(qd_group_e grp_enum,uvm_reg reg_name, field_t fields[]);
// TODO Kunal: add;	group 4 checks
		uvm_status_e reg_status; 
		bit [31:0] reg_value;

		if(grp_enum == QD_GROUP_1)
			begin 
				//opctrl.dis_dq update
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1,'{'{"dis_dq",1'b1}}));
				//`uvm_info("KUNNU'S>> REG_WRITE",$sformatf("Register: OPCTRL1 | value: | status: %s",reg_status), UVM_HIGH)	
				if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write dis_dq properly")

				// wr/rd_data_pipeline_empty poll
				repeat(2)		//according to DDRCTL databook 14.2.2.1 note-1
					begin 
						fork: poll_data_pipeline 
							forever
								begin 
									reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCAM.read(reg_status,reg_value);
									if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read opctrl")
									if(reg_value[29:28] == 2'b11)	break; 
								end 
							begin 
								#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg OPCTRLCAM")
							end 
						join_any
						disable poll_data_pipeline;
					end 
			end // QD_GRP_1

		if(grp_enum == QD_GROUP_2)
			begin 
 				// enabling self refresh mode			
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));

				// check for automatic self ref
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(reg_status,reg_value);
				if((reg_value[2:0] != 3'b011) || (reg_value[5:4] != 2'b10)) `uvm_error("QDYN_REG_ERROR","Self-refresh not caused by software. PWRCTL.selfref_sw might not be set")
				
			end // QD_GRP_2

		if(grp_enum == QD_GROUP_3)
			begin
				// disabling port and reg poll
				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCTRL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCTRL,'{'{"port_en",1'b0}}));

				fork: poll_port_status
					#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg PSTAT")
					forever
						begin
							reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PSTAT.read(reg_status,reg_value);
							if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read pstat")
							if(reg_value == 0) break; 
						end
				join_any
				disable poll_port_status;

				// disabling scrubber and polling
				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_en",1'b0}}));

				fork: poll_scrub_status 
					#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg SBRSTAT.scrub_busy")
					forever
						begin 
							reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT.read(reg_status,reg_value);
							if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read SBRSTAT")
							if(reg_value[0] == 0) break;
						end 
				join_any 
				disable poll_scrub_status;

				// disabling HIF input traffic to the ctrl 
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1,'{'{"dis_hif",1'b1}}));

				// polling cam empty status 
				fork: poll_cam_empty_status
					#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg OPCTRLCAM")
					forever
						begin 
							reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCAM.read(reg_status,reg_value);
								if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read OPCTRLCAM")
							if((reg_value[26:25] == 2'b11) && (reg_value[29:28] == 2'b11)) break;
						end 
				join_any 
				disable poll_cam_empty_status;
			end // QD_GRP_3

		if(grp_enum == QD_GROUP_4)
			begin 
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR2.read(reg_status,reg_value);
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read SBRSTAT")
				`uvm_info("QDYN_GRP4_REG_WR",$sformatf("Target frequency: %0d ",reg_value[1:0]), UVM_DEBUG)				
				// target frequency
				if(reg_value[1:0] == 0 && (reg_name.get_parent == reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0))
					`uvm_error("QDYN_REG_ERROR","target frequency = 0; Cannot write register of this block")
				if(reg_value[1:0] == 1 && (reg_name.get_parent == reg_model.DWC_ddrctl_map_REGB_FREQ1_CH0))
					`uvm_error("QDYN_REG_ERROR","target frequency = 1; Cannot write register of this block")
				if(reg_value[1:0] == 2 && (reg_name.get_parent == reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0))
					`uvm_error("QDYN_REG_ERROR","target frequency = 2; Cannot write register of this block")
				if(reg_value[1:0] == 3 && (reg_name.get_parent == reg_model.DWC_ddrctl_map_REGB_FREQ3_CH0))
					`uvm_error("QDYN_REG_ERROR","target frequency = 3; Cannot write register of this block")
			end 
		
		// sw_done
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1'b0}}));
// TODO Kunal: modify? poll for sw_done? UMCTL2_OCCAP_EN is '0'. ref:DWC_ddrctl_lpddr54_lpddr5x_databook 14.2.2

		foreach(fields[i])
			begin 
				`uvm_info("REG_WRITE",$sformatf("register: %0p field: %s value: %0d",reg_name,fields[i].name,fields[i].value), UVM_HIGH)	
			end 
		
		//reg_write
		reg_name.write(reg_status,generate_write_value(reg_name, fields));
		
		// sw_done
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1'b1}}));

		fork: poll_sw_done
			#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg SWSTAT.sw_done_ack")
			forever
				begin 
					reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWSTAT.read(reg_status,reg_value);
						if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read SWSTAT.sw_done_ack")
					if(reg_value[0] == 1'b1) break;
				end 
		join_any
		disable poll_sw_done;

		if(grp_enum == QD_GROUP_1)
			begin 
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1,'{'{"dis_dq",1'b0}}));
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write dis_dq properly")
			end // QD_GRP_1

		if(grp_enum == QD_GROUP_2)
			begin 
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write selfref_sw properly")
				
				// polling operating mode
				fork: poll_operating_mode
					#100us `uvm_error("POLL_TIMEOUT","Poll fail: polling timed out for reg STAT.operating_mode")
					forever
						begin 
							reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(reg_status,reg_value);
								if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not read STAT.operating_mode")
							if(reg_value[2:0] == 3'b011  && reg_value[5:4] == 2'b10) break;
						end 
				join_any
				disable poll_operating_mode;
			end // QD_GRP_2

		if(grp_enum == QD_GROUP_3)
			begin 
// FIXME Kunal: should change uvm_not_ok to uvm_has_x as well 			
				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCTRL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCTRL,'{'{"port_en",1'b1}}));
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write PCTRL.port_en properly")
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1,'{'{"dis_hif",1'b0}}));
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write OPCTRL1.dis_hif properly")
				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_en",1'b1}}));
					if(reg_status == UVM_NOT_OK) `uvm_error("QDYN_REG_ERROR","could not write SBRCTL.scrub_en properly")
			end // QD_GRP_3
		
	endtask:write_qd_reg

	// -------------------------------------------------------------------------
  // Description : This method is to read the operating mode of LPDDR
  // Method Name : operating_mode
  // Argument    : 
  //            
  // -------------------------------------------------------------------------
  task lpddr_operating_mode(output lpddr_op_mode_e op_mode);
    bit[31:0] STAT_REG;
		uvm_status_e status;
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(status,STAT_REG);
    op_mode = lpddr_op_mode_e'(STAT_REG[2:0]);	
		`uvm_info("OP_MODE",$sformatf("OP_MODE = %s",op_mode.name()), UVM_LOW)
  endtask

	// -------------------------------------------------------------------------
  // Description : This method is to read the selfref_state of LPDDR
  // Method Name : lpddr_selfref_state
  // Argument    :  
  // -------------------------------------------------------------------------
  task lpddr_selfref_state(output selfref_state_e selfref_state);
    bit[31:0] STAT_REG;
		uvm_status_e status;
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(status,STAT_REG);
    selfref_state = selfref_state_e'(STAT_REG[14:12]);
		`uvm_info("SELFREF_STATE",$sformatf("selfref_state = %s",selfref_state.name()), UVM_LOW)
  endtask

	// -------------------------------------------------------------------------
  // Description : This method is to read the selfref_type of LPDDR
  // Method Name : lpddr_selfref_type
  // Argument    :  
  // -------------------------------------------------------------------------
  task lpddr_selfref_type(output selfref_type_e selfref_type);
    bit[31:0] STAT_REG;
		uvm_status_e status;
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(status,STAT_REG);
    selfref_type = selfref_type_e'(STAT_REG[5:4]);	
		`uvm_info("SELFREF_TYPE",$sformatf("selfref_type = %s",selfref_type.name()), UVM_LOW)
  endtask

endclass : lpddr_subsystem_base_virtual_seq

`endif //LPDDR_SUBSYSTEM_BASE_VIRTUAL_SEQ_SVH
