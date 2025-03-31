//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_low_power_test_seq.sv
// Unit Name   : lpddr_low_power_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_low_power_test_seq
//--------------------------------------------------------------------------------------

class lpddr_low_power_test_seq extends lpddr_subsystem_base_virtual_seq ;
				`uvm_object_utils(lpddr_low_power_test_seq)
				lpddr_subsystem_axi_scheduler_seq scheduler_seq;


        uvm_status_e status;
        bit[7:0]test_scenario_iteration = 2;
				lpddr_op_mode_e operating_mode;
				selfref_type_e selfref_type;
				selfref_state_e selfref_state;
				randc bit selfref_en_val;
				randc bit [9:0] selfref_timing;
				randc bit selfref_sw_val;
				randc bit stay_in_selfref;
				rand bit powerdown_en_val;
        randc bit [6:0] power_down_timing;
				randc bit dfi_lp_en_pd_val;
				randc bit dfi_lp_en_sr_val;
				randc bit[4:0] dfi_lp_wakeup_pd_val;
				randc bit[4:0] dfi_lp_wakeup_sr_val;
				randc bit hw_lp_en_val;
				randc bit dfi_lp_en_dsm;
				randc bit dfi_phymstr_en;
			  randc bit dsm_en_val;
			  randc bit [4:0] dfi_lp_wakeup_dsm_val;
			  randc bit [4:0] dfi_tlp_resp_val;
			  randc	bit [4:0] dfi_t_ctrl_delay_val;
				randc bit t_cksre_val;
				randc bit clk_disable_val;
			  randc bit clk_enable_val;
			  randc bit t_cksrx_val;	
				real delay ;
				constraint selfref_timing_c {selfref_timing > 0;}
				constraint powerdown_timing_c {power_down_timing > 0;}
				constraint dfi_lp_wakeup_pd_c {dfi_lp_wakeup_pd_val > 0;dfi_lp_wakeup_pd_val < 14;}
				constraint dfi_lp_wakeup_sr_c {dfi_lp_wakeup_sr_val > 0;dfi_lp_wakeup_sr_val < 14;}
				constraint dfi_lp_wakeup_dsm_c {dfi_lp_wakeup_dsm_val > 0;dfi_lp_wakeup_dsm_val < 14;}


				function new ( string name = "lpddr_low_power_test_seq");
          super.new(name);
								scheduler_seq = lpddr_subsystem_axi_scheduler_seq::type_id::create("scheduler_seq");
        endfunction : new

				virtual task body();
					`uvm_info("LOW_POWER_TEST_SEQ",$sformatf("Inside the body of LOW POWER TEST SEQ"), UVM_LOW)
				  super.body();

					repeat (test_scenario_iteration) begin
					  if(!this.randomize()) begin
								$fatal("Randomization Failed");
						end
            case(test_scenario)
//-----------------------------------------------------------------------self refresh sequence-------------------------------------------------------------------------------------------------------------

							//In this scenario DDCTL puts SDRAM into self refresh if the axi traffic remains idle for selfref_timing 
						   1 : begin
					          delay = ((selfref_timing*32) * 1.25) - 5;
										repeat(3)begin
			              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",selfref_en_val}}));//Dynamic
									   if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")	
				            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"selfref_to_x32",selfref_timing}}));//TODO : QUASI DYANMIC 4
									   if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRTMG.selfref_to_x32")

				            scheduler_seq.disable_axi_scheduler;//Disabling axi traffic 
				            #(delay*1ns);//Disabling traffic for this time
										lpddr_operating_mode(operating_mode);//Reading the operating mode of LPDDR
					          `uvm_info("OP_MODE",$sformatf("operating_mode = %s",operating_mode), UVM_LOW)
										if (selfref_en_val == 1) begin
										  wait(operating_mode == SELF_REFRESH);//Wating for SELF_REFRESH
										end

				            scheduler_seq.enable_axi_scheduler;//Enabling axi traffic 
                    #100ns;//Delay to observe
									  delay = delay +5;	
		                end								
						      end

						  //In this scenario it will immediately will go to selfrefresh as soon as axi traffic is idle 	 
					     2 : begin
					    			 delay = $urandom_range(50,100);
										 #100ns;
					          `uvm_info("TEST_SCENARIO",$sformatf("Entered Scenario",), UVM_LOW)
					    		   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));//DYNAMIC
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_sw")
										 #10ns;//Delay to write the value to this reg
				             scheduler_seq.disable_axi_scheduler;//Disabling AXI Traffic
										 #50ns;
							       lpddr_operating_mode(operating_mode);//Checking states after disabling traffic
                     lpddr_selfref_type(selfref_type);
										 lpddr_selfref_state(selfref_state);
                      //wait(selfref_type == OTHER_SELFREF);						
				             #(delay*1ns);
										 scheduler_seq.enable_axi_scheduler;//Enabling AXI Traffic
										 #50ns;
                     lpddr_operating_mode(operating_mode);//checking states after enabling traffic
                     lpddr_selfref_type(selfref_type);
										 lpddr_selfref_state(selfref_state);
										 #10ns;
					    		    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));
									      if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_sw")	
					    				#100ns;
					    		 end
           
					     	// In this scenario based on the value of stay_in_selfref it will allow or prohibit the transition to "self refresh power down mode"   	 
					     3 : begin
					     			 delay =  (selfref_timing * 1.25);
				              begin
					     					reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",selfref_en_val}}));//DYNAMIC	
									       if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
				                reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"selfref_to_x32",selfref_timing}}));//TODO : QUASI DYNAMIC 4
									       if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_to_x32")	
					     					reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"stay_in_selfref",stay_in_selfref}}));//DYNAMIC
									       if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRTMG.stay_in_selfref")	
					     					scheduler_seq.disable_axi_scheduler;//Disabling AXI Traffic
					     					#(delay*1ns);
                        lpddr_selfref_state(selfref_state);
					              `uvm_info("SELFREF_STATE",$sformatf("selfref_state = %s",selfref_state), UVM_LOW)
												if (!stay_in_selfref)begin
												  wait(selfref_state == SELFREF_POWERDOWN);
												end
					     					scheduler_seq.enable_axi_scheduler;//Enabling AXI Traffic
												#100ns;
					     			 end
					     		 end		


                //In this scenario we are enabling hw_lp_en when the system is
								//in SW SELFREF
							 4 : begin
									   delay = $urandom_range(50,100);
					    		   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_sw")
				             scheduler_seq.disable_axi_scheduler;//Disabling AXI Traffic
                      lpddr_selfref_type(selfref_type);
                      wait(selfref_type == OTHER_SELFREF);						
				              #(delay*1ns);
					    		   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL,'{'{"hw_lp_en",1}}));//dynamic
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_sw")
                   end											 

//--------------------- ------------------------------------------------------PRE-Charge Power Down-------------------------------------------------------------------------------------------------------------
                //In this scenario based on the axi traffic remains idle for
								//power down timing it will enter power_down state
               5 : begin
							       delay = ((power_down_timing*32) * 1.25) - 5;
										 repeat(3) begin
                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",powerdown_en_val}}));//dynamic
			     	           reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"powerdown_to_x32",power_down_timing}}));//TODO : Quasi dynamic 4
			     	           scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
			                 #(delay*1ns);
			     		         lpddr_operating_mode(operating_mode);
					             `uvm_info("OP_MODE",$sformatf("operating_mode = %s",operating_mode), UVM_LOW)
                       if(powerdown_en_val)begin
										     wait(operating_mode == POWER_DOWN);
										   end
			                 scheduler_seq.enable_axi_scheduler;//Enabling axi traffic
			     	           delay = delay + 5;
						         end
							     end
								

							 		//This scenario for self refresh entry and  axi transaction during power down state
			         6 : begin
			         			delay = ((power_down_timing*32) * 1.25);
			               reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",selfref_sw_val}}));	  
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_sw")
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",powerdown_en_val}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.powerdown_en")
			         	     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"powerdown_to_x32",power_down_timing}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRTMG.powerdown_to_x32")
			         			 scheduler_seq.disable_axi_scheduler;
			               #(delay*1ns);
										 lpddr_operating_mode(operating_mode);
					          `uvm_info("OP_MODE",$sformatf("operating_mode = %s",operating_mode), UVM_LOW)
                     if(powerdown_en_val)begin
										   wait(operating_mode == POWER_DOWN);
										 end
			               scheduler_seq.enable_axi_scheduler;//AXI Traffic in power down state
			         			 #100ns;
			             end
							 
							 7 : begin
											 //TODO : Need to remove this
									 end

//-----------------------------------------------------------------------DEEP SLEEP SEQ--------------------------------------------------------------------------------------------------------------------------
               //In this scenario if dsm_en is set and ddrctl is idle then it will immediately move to Deep sleep mode
               8 : begin
                     scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//Entry to deep sleep
                     lpddr_selfref_state(selfref_state);
										 wait(selfref_state == DEEP_SLEEP);
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",0}}));//Exit to deep sleep
                     lpddr_selfref_state(selfref_state);
					         end

							 //In this scenario the ddrctl put SDRAM in deep sleep state and then axi traffic will start in deep sleep state
							 9 : begin
										 #(delay*1ns);
                     scheduler_seq.disable_axi_scheduler;//disabling axi traffic
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",dsm_en_val}})); 
										 lpddr_selfref_state(selfref_state);
										 if(dsm_en_val)begin
										   wait(selfref_state == DEEP_SLEEP);end
										 scheduler_seq.enable_axi_scheduler;
										 lpddr_selfref_state(selfref_state);
									 end		 
							
							 //In this scenario ddrctl put SDRAM into deep sleep state on
							 //based of value of selfref_sw and if traffic is idle	 	 
							 10 : begin
											scheduler_seq.disable_axi_scheduler; 
			                reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",selfref_sw_val}}));	  
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//fixed value
										  lpddr_selfref_state(selfref_state);
									  end		 
							 
							 //In this scenario ddrctl put SDRAM into deep sleep state on
							 //based of value of selfref_en and if traffic is idle			
							 11 : begin
											scheduler_seq.disable_axi_scheduler; 
			                reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",selfref_en_val}}));	  
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//fixed value
										  lpddr_selfref_state(selfref_state);
								    end

								//In this scenario ddrctl put SDRAM into deep sleep state on
							 //based of value of hw_lp_en and if traffic is idle		
							 12 : begin
											scheduler_seq.disable_axi_scheduler; 
			                reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL,'{'{"hw_lp_en",hw_lp_en_val}}));	  
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//fixed value
										  lpddr_selfref_state(selfref_state);
								    end			 
							
							 //In this scenario we are covering the value 0 and 1 of dfi_phymstr_en when dsm_en is set to 1			
							 13 : begin
									 	 scheduler_seq.disable_axi_scheduler; 
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));
								    end			 

							 14 : begin
											 //In this scenario we are covering DFILPTMG0.dfi_lp_wakeup_dsm
                       scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//Entry to deep sleep
                       lpddr_selfref_state(selfref_state);
										   wait(selfref_state == DEEP_SLEEP);
								    end

						   15 : begin
											 //In this scenario we are covering DFILPTMG0.dfi_lp_wakeup_sr
					     			   delay =  (selfref_timing *32* 1.25);
                       scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
											 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",1}}));//DYNAMIC	
									      if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
				               reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"selfref_to_x32",selfref_timing}}));//TODO : QUASI DYNAMIC 4
									      if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_to_x32")
											 #(delay*1ns);
							         wait(operating_mode == SELF_REFRESH);
							      end


					     16 : begin
											 //In this scenario we are covering DFILPTMG0.dfi_lp_wakeup_pd
											 delay = ((power_down_timing*32) * 1.25);
                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",1}}));//dynamic
			     	           reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"powerdown_to_x32",power_down_timing}}));//TODO : Quasi dynamic 4
			     	           scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
			                 #(delay*1ns);
			     		         lpddr_operating_mode(operating_mode);
					             `uvm_info("OP_MODE",$sformatf("operating_mode = %s",operating_mode), UVM_LOW)
										   wait(operating_mode == POWER_DOWN);
						        end

				       17 : begin
											 //TODO : DFITMG1.dfi_lp_wakeup_data 
					          end						 

								//In this scenario we are covering diff values of dfi_tlp_resp //static		
							 18 : begin
											 //TODO : Doubt in dfi_lp_ctrl_req , dfi_lp_data_req
								    end			 
								
//------------------------------------------------------------------------------DFI DRAM CLK DISABLE ----------------------------------------------------------------------									 	
               //Deep Sleep Mode
               19 : begin
										  scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",1}}));//Entry to deep sleep
                      lpddr_selfref_state(selfref_state);
										  wait(selfref_state == DEEP_SLEEP);
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"en_dfi_dram_clk_disable",1}}));
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",dfi_t_ctrl_delay_val}}));
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksre",t_cksre_val}}));//QUASI DYNAMIC 2,4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_disable",clk_disable_val}}));//QUASI DYNAMIC 4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_enable",clk_enable_val}}));//QUASI DYNAMIC 4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksrx",t_cksrx_val}}));//QUASI DYNAMIC 2,4
							      end
							
							 //Normal Mode	
							 20 : begin
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"en_dfi_dram_clk_disable",1}}));
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",dfi_t_ctrl_delay_val}}));
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksre",t_cksre_val}}));//QUASI DYNAMIC 2,4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_disable",clk_disable_val}}));//QUASI DYNAMIC 4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_enable",clk_enable_val}}));//QUASI DYNAMIC 4
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksrx",t_cksrx_val}}));//QUASI DYNAMIC 2,4
									  end

							//Self refresh power down 
							21 : begin
											delay =  (selfref_timing * 1.25);
					     				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",1}}));//DYNAMIC	
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
				              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"selfref_to_x32",selfref_timing}}));//TODO : QUASI DYNAMIC 4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_to_x32")	
					     				reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"stay_in_selfref",1}}));//DYNAMIC
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRTMG.stay_in_selfref")	
					     				scheduler_seq.disable_axi_scheduler;//Disabling AXI Traffic
					     				#(delay*1ns);
                      lpddr_selfref_state(selfref_state);
											wait(selfref_state == SELFREF_POWERDOWN);
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"en_dfi_dram_clk_disable",1}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",dfi_t_ctrl_delay_val}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksre",t_cksre_val}}));//QUASI DYNAMIC 2,4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_disable",clk_disable_val}}));//QUASI DYNAMIC 4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_enable",clk_enable_val}}));//QUASI DYNAMIC 4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksrx",t_cksrx_val}}));//QUASI DYNAMIC 2,4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
									 end

					    //Power Down
							22 : begin
									   delay = ((power_down_timing*32) * 1.25);
                     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",powerdown_en_val}}));//dynamic
			     	         reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG,'{'{"powerdown_to_x32",power_down_timing}}));//TODO : Quasi dynamic 4
			     	         scheduler_seq.disable_axi_scheduler;//Disabling axi traffic
			               #(delay*1ns);
			     		       lpddr_operating_mode(operating_mode);
										 wait(operating_mode == POWER_DOWN);
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"en_dfi_dram_clk_disable",1}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",dfi_t_ctrl_delay_val}}));
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksre",t_cksre_val}}));//QUASI DYNAMIC 2,4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_disable",clk_disable_val}}));//QUASI DYNAMIC 4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_dram_clk_enable",clk_enable_val}}));//QUASI DYNAMIC 4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
                      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG5,'{'{"t_cksrx",t_cksrx_val}}));//QUASI DYNAMIC 2,4
									     if(status == UVM_NOT_OK) `uvm_error("ERROR","Could not write PWRCTL.selfref_en")
									 end

	        endcase
					end
        endtask


				task configure_static_reg_during_reset();
					 void'(randomize());
					 if (test_scenario == 5) begin//If dfi_lp_en_pd is set then controller will but PHY in low power mode through LOW power interface during powerdown entry/exit
             reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_en_pd",dfi_lp_en_pd_val}}));
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0,'{'{"dfi_lp_wakeup_pd",dfi_lp_wakeup_pd_val}}));
	         end
					 if (test_scenario == 2)begin //If dfi_lp_en_sr is set then controller will but PHY in low power mode through LOW power interfac during selfref entry/exit
             //reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_en_sr",dfi_lp_en_sr_val}}));
             //reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_wakeup_sr",dfi_lp_wakeup_sr_val}}));
					 end
					 if(test_scenario == 8)begin
             reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_en_dsm",dfi_lp_en_dsm}}));
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0,'{'{"dfi_lp_wakeup_sr",dfi_lp_wakeup_sr_val}}));
					 end
					 if(test_scenario == 13)begin
             reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR,'{'{"dfi_phymstr_en",dfi_phymstr_en}}));
					 end
					 if(test_scenario == 14)begin
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0,'{'{"dfi_lp_wakeup_dsm",dfi_lp_wakeup_dsm_val}}));
					 end
					 if(test_scenario == 15)begin
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0,'{'{"dfi_lp_wakeup_sr",dfi_lp_wakeup_sr_val}}));
					 end
					 if(test_scenario == 16)begin
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0,'{'{"dfi_lp_wakeup_pd",dfi_lp_wakeup_pd_val}}));
					 end
					 if(test_scenario == 18)begin
             reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG1,'{'{"dfi_tlp_resp",dfi_tlp_resp_val}}));
					 end

				endtask

endclass
