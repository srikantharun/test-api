//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_perf_signals_covergroup.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			: perf_signal_covergroup
//Parent			: uvm_component
//Description	: contains all the covergroups and sampling for performance
//							signals. to use; pass the correct string for your coverage
//-------------------------------------------------------------------------------------------
// TODO Kunal: modify; 	make a seperate file for this which includes as it
// 											includes other coverage as well(all test by kunal)
class perf_signal_covergroup#(string cov_name="") extends uvm_component;
	`uvm_component_param_utils(perf_signal_covergroup#(cov_name))

  //Virtual Interface
  virtual subsystem_signal_intf m_subsystem_vif;

	covergroup cg_perf_axi_input_traffic;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to axi input traffic";

		cp_perf_bank 								: coverpoint		m_subsystem_vif.perf_bank 							{option.comment="covers all the possible combination of perf_bank";}
		cp_perf_bg									:	coverpoint		m_subsystem_vif.perf_bg									{option.comment="covers all the possible combination of perf_bg";}
		cp_perf_dfi_rd_data_cycles	:	coverpoint		m_subsystem_vif.perf_dfi_rd_data_cycles {option.comment="covers all the possible combination of perf_dfi_rd_data_cycles";}
		cp_perf_dfi_wr_data_cycles	:	coverpoint		m_subsystem_vif.perf_dfi_wr_data_cycles {option.comment="covers all the possible combination of perf_dfi_wr_data_cycles";}
		cp_perf_hif_rd							:	coverpoint		m_subsystem_vif.perf_hif_rd 						{option.comment="covers all the possible combination of perf_hif_rd";}
		cp_perf_hif_rd_or_wr				:	coverpoint		m_subsystem_vif.perf_hif_rd_or_wr				{option.comment="covers all the possible combination of perf_hif_rd_or_wr";}
		cp_perf_hif_wr							:	coverpoint		m_subsystem_vif.perf_hif_wr 						{option.comment="covers all the possible combination of perf_hif_wr";}
		cp_perf_op_is_cas						:	coverpoint		m_subsystem_vif.perf_op_is_cas					{option.comment="covers all the possible combination of perf_op_is_cas";}
		cp_perf_rank								:	coverpoint    m_subsystem_vif.perf_rank 							{option.comment="covers all the possible combination of perf_rank";}
		cp_perf_hif_rmw 						:	coverpoint    m_subsystem_vif.perf_hif_rmw						{option.comment="covers all the possible combination of perf_hif_rmw";}

	endgroup: cg_perf_axi_input_traffic

	covergroup cg_addr_coll_handling;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to address collision and write combine test";

		cp_perf_write_combine					: coverpoint m_subsystem_vif.perf_write_combine					{option.comment="covers all the possible combination of perf_write_combine";}
		cp_perf_write_combine_noecc		: coverpoint m_subsystem_vif.perf_write_combine_noecc   {option.comment="covers all the possible combination of perf_write_combine_noecc";}
// FIXME Kunal: perf_write_combine written 2 times in vplan
		//cp_perf_write_combine					: coverpoint m_subsystem_vif.perf_write_combine       {option.comment="covers all the possible combination of perf_write_combine";}
		cp_perf_write_combine_wrecc		: coverpoint m_subsystem_vif.perf_write_combine_wrecc   {option.comment="covers all the possible combination of perf_write_combine_wrecc";}
		cp_perf_waw_hazard						: coverpoint m_subsystem_vif.perf_waw_hazard            {option.comment="covers all the possible combination of perf_waw_hazard";}
		cp_perf_wr_xact_when_critical	: coverpoint m_subsystem_vif.perf_wr_xact_when_critical {option.comment="covers all the possible combination of perf_wr_xact_when_critical";}

	endgroup: cg_addr_coll_handling

	covergroup cg_wr_to_rd_switching;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to write to read switching test";

		perf_op_is_activate                 	: coverpoint m_subsystem_vif.perf_op_is_activate                   	{option.comment="covers all the possible combination of perf_op_is_activate";}
		perf_op_is_rd                       	: coverpoint m_subsystem_vif.perf_op_is_rd                         	{option.comment="covers all the possible combination of perf_op_is_rd";} 
		perf_op_is_rd_activate              	: coverpoint m_subsystem_vif.perf_op_is_rd_activate                	{option.comment="covers all the possible combination of perf_op_is_rd_activate";}
		perf_op_is_rd_or_wr                 	: coverpoint m_subsystem_vif.perf_op_is_rd_or_wr                   	{option.comment="covers all the possible combination of perf_op_is_rd_or_wr";}
		perf_war_hazard                     	: coverpoint m_subsystem_vif.perf_war_hazard                       	{option.comment="covers all the possible combination of perf_war_hazard";}
		perf_visible_window_limit_reached_wr	: coverpoint m_subsystem_vif.perf_visible_window_limit_reached_wr  	{option.comment="covers all the possible combination of perf_visible_window_limit_reached_wr";}
		perf_visible_window_limit_reached_rd	: coverpoint m_subsystem_vif.perf_visible_window_limit_reached_rd  	{option.comment="covers all the possible combination ofperf_visible_window_limit_reached_rd";}
		perf_rdwr_transitions               	: coverpoint m_subsystem_vif.perf_rdwr_transitions  							 	{option.comment="covers all the possible combination ofperf_rdwr_transitions";}
		perf_raw_hazard                     	: coverpoint m_subsystem_vif.perf_raw_hazard											 	{option.comment="covers all the possible combination ofperf_raw_hazard";}
		perf_precharge_for_rdwr             	: coverpoint m_subsystem_vif.perf_precharge_for_rdwr							 	{option.comment="covers all the possible combination ofperf_precharge_for_rdwr";}
		perf_op_is_wr                       	: coverpoint m_subsystem_vif.perf_op_is_wr												 	{option.comment="covers all the possible combination ofperf_op_is_wr";}
		perf_hpr_xact_when_critical         	: coverpoint m_subsystem_vif.perf_hpr_xact_when_critical 					 	{option.comment="covers all the possible combination ofperf_hpr_xact_when_critical";}
	 	perf_hpr_req_with_nocredit          	: coverpoint m_subsystem_vif.perf_hpr_req_with_nocredit						 	{option.comment="covers all the possible combination ofperf_hpr_req_with_nocredit";}
		perf_lpr_xact_when_critical         	: coverpoint m_subsystem_vif.perf_lpr_xact_when_critical					 	{option.comment="covers all the possible combination ofperf_lpr_xact_when_critical";}
// TODO Kunal: remove; signal not present in ref manual but given in testplan                                	
		//perf_lpr_xact_when_nocredit         	: coverpoint m_subsystem_vif.perf_lpr_xact_when_nocredit				 	  {option.comment="covers all the possible combination ofperf_lpr_xact_when_nocredit";}
		perf_lpr_req_with_nocredit         		: coverpoint m_subsystem_vif.perf_lpr_req_with_nocredit							{option.comment="covers all the possible combination ofperf_lpr_xact_when_nocredit";}
		hpr_credit_cnt                      	: coverpoint m_subsystem_vif.hpr_credit_cnt												 	{option.comment="covers all the possible combination ofhpr_credit_cnt";}
		lpr_credit_cnt                      	: coverpoint m_subsystem_vif.lpr_credit_cnt												 	{option.comment="covers all the possible combination oflpr_credit_cnt";}
		wr_credit_cn                        	: coverpoint m_subsystem_vif.wr_credit_cnt												 	{option.comment="covers all the possible combination ofwr_credit_cnt";}

	endgroup:cg_wr_to_rd_switching 

	covergroup cg_lpddr5_masked_write;
		option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to lpddr5 masked write test";

		cp_perf_op_is_mwr	: coverpoint m_subsystem_vif.perf_op_is_mwr {option.comment="covers all the possible combination of perf_op_is_mwr";}
	endgroup: cg_lpddr5_masked_write

	covergroup cg_perf_selfref;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to axi input traffic";

    cp_perf_op_is_enter_selfref_rank0 : coverpoint m_subsystem_vif.perf_op_is_enter_selfref[0] {
		  bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
		}

		cp_perf_op_is_enter_selfref_rank1 : coverpoint m_subsystem_vif.perf_op_is_enter_selfref[1] {
		  bins cb_logic_0 = {1'b0};
      bins cb_logic_1 = {1'b1};
		}

		cp_perf_selfref_mode_rank0 : coverpoint m_subsystem_vif.perf_selfref_mode[0] {
		  bins cb_logic_0 = {1'b0};
		  bins cb_logic_1 = {1'b1};
		}
		
		cp_perf_selfref_mode_rank1 : coverpoint m_subsystem_vif.perf_selfref_mode[1] {
		  bins cb_logic_0 = {1'b0};
		  bins cb_logic_1 = {1'b1};
		}

		cp_perf_precharge_for_other : coverpoint m_subsystem_vif.perf_precharge_for_other {
		  bins cb_logic_1 = {1'b1};
		}

	endgroup

	covergroup cg_perf_precharge_powerdown;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to axi input traffic";

		cp_perf_op_is_enter_powerdown_rank0 :coverpoint  m_subsystem_vif.perf_op_is_enter_powerdown[0] {
						bins cb_logic_0 = {1'b0};
						bins cb_logic_1 = {1'b1};
		}

		cp_perf_op_is_enter_powerdown_rank1 : coverpoint  m_subsystem_vif.perf_op_is_enter_powerdown[1] {
						bins cb_logic_0 = {1'b0};
						bins cb_logic_1 = {1'b1};
		}

	endgroup

	covergroup cg_perf_deep_sleep;
	  option.per_instance = 1;
	  type_option.merge_instances = 0;
		option.comment="this covergroup covers all the performance signals related to axi input traffic";
    
		cp_perf_op_is_enter_dsm : coverpoint m_subsystem_vif.perf_op_is_enter_dsm{
		  bins cb_logic_0 = {1'b0};
		  bins cb_logic_1 = {1'b1};
		}

	endgroup


	function new(string name="perf_signal_covergroup",uvm_component parent=null);
		super.new(name,parent);
		//cg_perf_axi_input_traffic=new();
		//cg_addr_coll_handling=new();
		case(cov_name)
		"axi_input_traffic" 	: begin
															cg_perf_axi_input_traffic=new();
														end
		"addr_coll_test" 			: begin
														cg_addr_coll_handling=new();	
														end
		"masked_write_test"		: begin
														cg_lpddr5_masked_write=new(); 
														end
		"wr_to_rd_switching" 	: begin
															cg_wr_to_rd_switching=new(); 
														end
		"self_refresh"				: begin
						                cg_perf_selfref=new();
						              end
		"precharge_powerdown" : begin
						                 cg_perf_precharge_powerdown = new();
						                end
		"deep_sleep"          : begin
						                 cg_perf_deep_sleep=new();
						                end
		default : `uvm_error("PERF_SIGNAL_COVERAGE","correct string not provided for covergroup. provide correct name")
		endcase
	endfunction

	function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		// get the perf signals from subsystem intf
    if(!uvm_config_db#(virtual subsystem_signal_intf)::get(null,"UVMF_VIRTUAL_INTERFACES","top_signals_intf",m_subsystem_vif))
			begin
      	`uvm_error("Config Error","uvm_config_db #(subsystem_signal_intf)::get cannot find resource 'subsystem_signals'")
			end
	endfunction: build_phase

	virtual function void sample();
		case(cov_name)
		"axi_input_traffic" : begin
														`uvm_info("PERF_SIGNAL_COVERAGE",$sformatf("sampling perfomance signal for axi input handling test"), UVM_HIGH)
														cg_perf_axi_input_traffic.sample();
													end
		"addr_coll_test" 		: begin
														`uvm_info("PERF_SIGNAL_COVERAGE",$sformatf("sampling perfomance signal for address collision test"), UVM_HIGH)
														cg_addr_coll_handling.sample;	
													end
		"masked_write_test"	: begin
														`uvm_info("PERF_SIGNAL_COVERAGE",$sformatf("sampling perfomance signal for lpddr5 masked write test"), UVM_HIGH)
														cg_lpddr5_masked_write.sample();
													end
		"wr_to_rd_switching": begin
														cg_wr_to_rd_switching.sample(); 
													end
		"self_refresh"				: begin
						                cg_perf_selfref.sample();
						              end
		"precharge_powerdown" : begin
						                 cg_perf_precharge_powerdown.sample();
						                end
		"deep_sleep"          : begin
						                 cg_perf_deep_sleep.sample();
						                end
		default : `uvm_error("PERF_SIGNAL_COVERAGE","correct string not provided for covergroup. provide correct name")
		endcase
	endfunction: sample

endclass: perf_signal_covergroup
