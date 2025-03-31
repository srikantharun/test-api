//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_performance_test_seq.sv
// Unit Name   : lpddr_performance_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_performance_test_seq
//--------------------------------------------------------------------------------------
class lpddr_performance_test_seq extends lpddr_subsystem_base_virtual_seq;
				`uvm_object_utils(lpddr_performance_test_seq)

				//seq handle
				lpddr_subsystem_axi_scheduler_seq scheduler_seq;
				axi_trans_t axi_trans;
        randc bit[1:0] frequency_val;
				randc bit hwffc_mode_val;
				randc bit[1:0] hwffc_en_val;
				randc bit dis_srx_zqcl_hwffc_val
				randc bit[3:0]qos_val;
				bit same_qos;
				int num_of_wr_rw;
				constraint hwffc_en_c {hwffc_en_val inside [2'b00,2'b01,2'b11];}



				function new ( string name = "lpddr_performance_test_seq");
          super.new(name);
					scheduler_seq = lpddr_subsystem_axi_scheduler_seq::type_id::create("scheduler_seq");
					axi_trans = axi_trans_t::type_id::create("axi_trans");
        endfunction : new

        task body();
					super.body();
					if(!this.randomize()) begin
								$fatal("Randomization Failed");
					end
				  repeat(test_scenario_iteration)begin
						case(test_scenario)
//---------------------------------------------Fast Frequency Change Test-------------------------------------------------------------------------------------
						  1 : begin
							    //TODO : To check the width of target frequency
									//MSTR2.target_frequency is of Quasi-Dynamic grp 2
                  scheduler_seq.disable_axi_scheduler;
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));
									//TODO : wait for STAT.operating_mode = 3'b011
									//TODO : wait for STAT.selfref_type = 2'b01
								  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}})); 
							    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR2,'{'{"target_frequency",frequency_val}}));
								  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}})); 
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));
                  scheduler_seq.enable_axi_scheduler;


									//DFIMISC.dfi_frequency is of Quasi-Dynamic grp 1
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTL1,'{'{"dis_dq",1}}));
									//TODO : wait for OPCTRLCAM.wr_data_pipeline_empty = 1
									//TODO : wait for OPCTRLCAM.rd_data_pipeline_empty = 1
								  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}})); 
								  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_frequency",frequency_val}})); 
								  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}})); 
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTL1,'{'{"dis_dq",0}}));
									
									//TODO : Cover diff values of Timing register of diff frequency sets
									end

//------------------------------------------------ Hardware Fast Frequency Change Test ---------------------------------------------------------									
               2 : begin
							     //ZQCTL.dis_srx_zqcl_hwffc programming mode is quasi dynamic grp2,4
							      scheduler_seq.disable_axi_scheduler;
					    		  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));
									  //TODO : wait for STAT.operating_mode = 3'b011
									  //TODO : wait for STAT.selfref_type = 2'b01
								    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}})); 
							      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL2,'{'{"dis_srx_zqcl_hwffc",dis_srx_zqcl_hwffc_val}}));
								    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}})); 
					    		  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));
                    scheduler_seq.enable_axi_scheduler
							       //TODO :- HWFFC_MRBUF_CTRL0 not found in RAL
					         end

									 //Performance counter test
									 //TODO : Query for reg info
							 3 : begin
									 end

//------------------------------------------------ Throughput Test with same qos ---------------------------------------------------------									 
							 4 : begin

							       //DRAMSET1TMG24.bank_org programming mode is grp 1,2,4
							       scheduler_seq.disable_axi_scheduler;
					    		   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));
										 //TODO : wait for STAT.operating_mode = 3'b011
									   //TODO : wait for STAT.selfref_type = 2'b01
								     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}})); 
								     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG24.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG24,'{'{"bank_org",0}})); 
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}})); 
					    		   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));

                     //Minimum latency value in mode register
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"pp_pgmpst_en",0}})); 
										 
										 //Minimum timing for APB config reg for timing between commands
								     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}})); 

                     //Max time for all periodic maintenance timers

										 //Back to back read and write
										 fork
                       back_2_back_read_or_write(AXI4_TRANS_WRITE,10,1);
                       back_2_back_read_or_write(AXI4_TRANS_READ,10,1);
                     join

									 end		 

//------------------------------------------------ Throughput Test with diff qos -------------------------------------------------------------
							 5 : begin
									 end		 
						endcase
					end
				endtask

				task configure_static_reg_during_reset();
								if(test_scenario == 2)begin
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWFFCCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWFFCCTL,'{'{"hwffc_mode",hwffc_mode_val}}));
					    		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWFFCCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWFFCCTL,'{'{"hwffc_en",hwffc_en_val}}));
								end
				endtask

        //Method : back_2_back_read_or_write
				//Arguement : 
				//Descrption : This task is used to drive back to back read or write
				//with max burst length and size on diff addresses with same or diff
				//qos value
        virtual task back_2_back_read_or_write(axi4_rw_e rd_or_wr,int num_of_wr_rw,bit same_qos);
				  if(same_qos)begin
						`uvm_info("BACK_TO_BACK_SEQ",$sformatf("QOS value will be same",), UVM_LOW)
						assert(this.randomize(qos_val));
					  repeat(num_of_wr_rw)begin
						  `uvm_do_on_with(axi_trans, axi4_master_sqr, {	read_or_write == rd_or_wr;
		                                                          burst_length == 'hFF;
																											        size == AXI4_BYTES_32;
																											        qos == qos_val;})
						  `uvm_info("BACK_TO_BACK_SEQ",$sformatf("Write Transaction: ",axi_trans.sprint), UVM_LOW)
						end
          end
					else begin
						`uvm_info("BACK_TO_BACK_SEQ",$sformatf("QOS value will be different",), UVM_LOW)
						repeat(num_of_wr_rw)begin
						  assert(this.randomize(qos_val));
					    `uvm_do_on_with(axi_trans, axi4_master_sqr, {	read_or_write == rd_or_wr;
		                                                          burst_length == 'hFF;
																											        size == AXI4_BYTES_32;
																											        qos == qos_val;})
						  `uvm_info("BACK_TO_BACK_SEQ",$sformatf("Write Transaction: ",axi_trans.sprint), UVM_LOW)
						end
					end
	      endtask

endclass
