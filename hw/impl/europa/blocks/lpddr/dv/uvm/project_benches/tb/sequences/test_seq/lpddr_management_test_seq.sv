//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_management_test_seq.sv
// Unit Name   : lpddr_management_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_management_test_seq
//--------------------------------------------------------------------------------------
class lpddr_management_test_seq extends lpddr_subsystem_base_virtual_seq;
				`uvm_object_utils(lpddr_management_test_seq)
				lpddr_subsystem_axi_scheduler_seq scheduler_seq;

        uvm_status_e status;
				randc bit rfm_en_val;
				randc bit rfmsbc_val;
				randc bit[11:0] t_rfc_min_ab;
				randc bit [4:0]refresh_to_ab_val;
				randc bit[5:0]refresh_burst_val;
				randc bit opt_en_val;
				randc bit refresh_sel;
				randc bit t_refi_sel;
				randc bit[11:0] t_rfc_min_val;
				randc bit[5:0]refresh_to_x1_x32_val;
				randc bit[13:0]refi_x1_x32_val;//TODO - DOUBT IN NOTE OF THIS FIELD
				bit [31:0] refresh_busy;
				randc bit derate_enable_val;
				randc bit derate_mr4_dis;
				randc bit [31:0] mr4_read_val;
				randc bit derate_temp_limit_en;
				bit[31:0] deratectl5;
				bit [31:0]deratestat0;
				randc bit dis_auto_zq_val;
				randc bit zq_reset_val;
				bit[31:0] zqstat_val;
				randc bit[9:0]zq_short_nop;
				randc bit[9:0]zq_reset_nop;
				randc bit[6:0]zq_stop;
				randc bit [19:0]zq_short_interval;
				randc bit dis_srx_zqcl_val;
				randc bit[7:0] dqsosc_runtime_val;
				randc bit[7:0]wck2dqo_runtime_val;
				randc bit[15:4]dqsosc_interval_val;
				randc bit dqsosc_enable_val;
				randc bit dis_autoctrlupd_val;
				randc bit ctrlupd_val;
				bit ctrlupd_busy;
				randc bit dfi_phyupd_en_val;
				randc bit[1:0] auto_refab_en_val;
				randc bit [7:0] t_pbr2pbr_val;
				int test_scenario_iteration;
				randc bit [4:0] dfi_t_ctrl_delay;
				randc bit [9:0] dfi_t_ctrlup_max;
				randc bit [9:0] dfi_t_ctrlup_min;
				randc bit [9:0] dfi_t_ctrlupd_interval_min_x1024;
				randc bit [7:0] dfi_t_ctrlupd_interval_max_x1024;
				randc bit [8:0] dfi_t_ctrlupd_burst_interval_x8;
				//constraint ref_ab_c {refresh_to_ab_val % 32 == 0;} TODO : Not needed
        /*constraint ref_burst_c {
								                if( (test_scenario == 3) && (auto_refab_en_val > 0) )begin
																  refresh_burst_val > 7;
                                end
                                else begin
																	refresh_burst_val >= 1; 
				                        end																
				                       } */
				constraint mr4_read_val_c {mr4_read_val >0;}
				//constraint zq_short_interval_c {zq_short_interval % 1024 == 0;}
				constraint dqsosc_runtime_c {dqsosc_runtime_val > 0;}
				constraint wck2dqo_runtime_c {wck2dqo_runtime_val > 0;}
				constraint dqsosc_interval_c {dqsosc_interval_val > 1;}
				constraint dfi_t_ctrlupd_interval_max_x1024_c {dfi_t_ctrlupd_interval_max_x1024 != 0;}



				function new(string name = "lpddr_management_test_seq");
          super.new(name);
	      endfunction : new

				virtual task body();
				  super.body();
					  repeat(test_scenario_iteration) begin
					    if(!this.randomize()) begin
								$fatal("Randomization Failed");
						  end
							case(test_scenario)
//---------------------------------------------------------------------------Refresh Management Test--------------------------------------------------------------------------------------------
                1 : begin
								      //TODO : TO set the value of rfm_en base on MR27:OP[0]
											//write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"rfm_en",rfm_en_val}});
                    end								

//--------------------------------------------------------------------------ALL Bank Refresh Using Auto-Refresh Feature test-------------------------------------------------------------------------------------------------------										
                2 : begin
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",0}}));//dynamic 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));////section 1.3.9.8 reason for toggling twice this field 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}})); 
								      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"t_rfc_min_ab",t_rfc_min_ab}}));//TODO : tRFCab 
								      reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG3.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG3,'{'{"refresh_to_ab_x32",refresh_to_ab_val}}));//dynamic 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0,'{'{"refresh_burst",refresh_burst_val}}));//dynamic 
								    end

//--------------------------------------------------------------------Per Bank refresh using auto refresh feature------------------------------------------------------------------------------------
								3 : begin
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",0}}));//dynamic 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));////section 1.3.9.8 reason for toggling twice this field 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}})); 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"refresh_to_x1_sel",refresh_sel}})); 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"t_refi_x1_sel",t_refi_sel}})); 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0,'{'{"refresh_burst",refresh_burst_val}})); 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"t_rfc_min",t_rfc_min_val}}));//TODO : t_rfc_min == tRFCpb 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG2,'{'{"t_pbr2pbr",t_pbr2pbr_val}})); 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"refresh_to_x1_x32",refresh_to_x1_x32_val}})); 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1,'{'{"t_refi_x1_x32",refi_x1_x32_val}})); 
								    end		

//-------------------------------------------------------------------Refresh Using Direct Software Request of Refresh Command Test --------------------------------------------------------------										
                  //PER BANK REFRESH = 1 &&  65 REFRESH ENTRIES for rank 0
                4 : begin
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",1}}));//disable autorefresh 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));//section 1.3.9.8 reason for toggling twice this field
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}}));
										  repeat (65) begin	
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[0] == 0);
												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0,'{'{"rank0_refresh",1}}));
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[0] == 1);
											end
							      end	

                  //PER BANK REFRESH = 1 &&  65 REFRESH ENTRIES for rank 1
								5 : begin
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",1}}));//disable autorefresh 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));//section 1.3.9.8 reason for toggling twice this field
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}}));
										  repeat (65) begin	
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[1] == 0);
												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0,'{'{"rank1_refresh",1}}));
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[1] == 1);
											end
								    end

                  //PER BANK REFRESH = 0 &&  9 REFRESH ENTRIES for rank 0
								6 : begin
										  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",1}}));//disable autorefresh 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));//section 1.3.9.8 reason for toggling twice this field
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}}));
										  repeat (9) begin	
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[0] == 0);
												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0,'{'{"rank0_refresh",1}}));
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[0] == 1);
											end
								    end
								
                  //PER BANK REFRESH = 0 &&  9 REFRESH ENTRIES for rank 1
								7 : begin
										  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",1}}));//disable autorefresh 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",1}}));//section 1.3.9.8 reason for toggling twice this field
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"refresh_update_level",0}}));
										  repeat (9) begin	
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[1] == 0);
												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0,'{'{"rank1_refresh",1}}));
								        reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.read(status,refresh_busy);
												wait(refresh_busy[1] == 1);
											end
										end	
//-------------------------------------------------------------------Automatic Temperature Derate-------------------------------------------------------------------------------------------------------------------------------------
								8 : begin
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL0,'{'{"derate_enable",derate_enable_val}})); 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL6.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL6,'{'{"derate_mr4_tuf_dis",derate_mr4_dis}})); 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL5,'{'{"derate_temp_limit_intr_en",derate_temp_limit_en}})); 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL5.read(status,deratectl5); 
											//TODO : DERATEVAL0
											//TODO : MR4
                      
									  end			

//-------------------------------------------------------------------ZQ Calibration Test-------------------------------------------------------------------------------------------------------------
                9 : begin
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL0,'{'{"dis_auto_zq",dis_auto_zq_val}}));//dynamic 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL1,'{'{"zq_reset",zq_reset_val}}));//dynamic 
								      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQSTAT.read(status,zqstat_val);
											//reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
                      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL2,'{'{"dis_srx_zqcl",dis_srx_zqcl_val}}));//QRP2 , 4
											//reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
								    end

//-------------------------------------------------------------------MRR Snooping Test------------------------------------------------------------------------------
                10 : begin
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DQSOSCRUNTIME.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DQSOSCRUNTIME,'{'{"dqsosc_runtime",dqsosc_runtime_val}}));//QRP2
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DQSOSCRUNTIME.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DQSOSCRUNTIME,'{'{"wck2dqo_runtime",wck2dqo_runtime_val}}));//QRP2
											reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DQSOSCCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DQSOSCCTL0,'{'{"dqsosc_interval",dqsosc_interval_val}}));//dynamic 
					            reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DQSOSCCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DQSOSCCTL0,'{'{"dqsosc_enable",dqsosc_enable_val}})); //dynamic
								    end

//-------------------------------------------------------------------DFI Updates Mode Test---------------------------------------------------------------------
                11 : begin
								     scheduler_seq.disable_axi_scheduler; 
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0,'{'{"dis_auto_ctrlupd",dis_autoctrlupd_val}}));
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCMD.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCMD,'{'{"ctrlupd",ctrlupd_val}}));
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLSTAT.read(status,ctrlupd_busy);
										 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0,'{'{"dfi_phyupd_en",dfi_phyupd_en_val}}));
					           reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",dfi_t_ctrl_delay}}));//QRP 4
										 //TODO : Configure DFI Constraints  

								    end

							endcase
		        end	

        endtask

				task configure_static_reg_during_reset();
				  if(test_scenario == 1)begin
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"rfmsbc",rfmsbc_val}})); 
					end
					if(test_scenario == 2)begin
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"per_bank_refresh",0}})); 
				  end
					if(test_scenario == 3)begin
				    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"per_bank_refresh",1}})); 
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"per_bank_refresh_opt_en",opt_en_val}})); 
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"auto_refab_en",auto_refab_en_val}})); 
          end
          if((test_scenario == 4) || (test_scenario == 5))begin
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"per_bank_refresh",1}})); 
				  end
          if((test_scenario == 6) || (test_scenario == 7))begin
					  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0,'{'{"per_bank_refresh",0}})); 
				  end					
					if(test_scenario == 8)begin
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DERATEINT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DERATEINT,'{'{"mr4_read_interval",mr4_read_val}})); 
						reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATESTAT0.read(status,deratestat0); 
					end				
					if(test_scenario == 9)begin
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG0,'{'{"t_zq_short_nop",zq_short_nop}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG1,'{'{"t_zq_reset_nop",zq_reset_nop}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG2,'{'{"t_zq_stop",zq_stop}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.ZQSET1TMG1,'{'{"t_zq_short_interval_x1024",zq_short_interval}})); 
		      end
					if(test_scenario == 11)begin
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG0,'{'{"dfi_t_ctrlup",dfi_t_ctrlup_max}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG0,'{'{"dfi_t_ctrlup_min",dfi_t_ctrlup_min}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG1,'{'{"dfi_t_ctrlupd_interval_min_x1024",dfi_t_ctrlupd_interval_min_x1024}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG1,'{'{"dfi_t_ctrlupd_interval_max_x1024",dfi_t_ctrlupd_interval_max_x1024}})); 
					  reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG3.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFIUPDTMG3,'{'{"dfi_t_ctrlupd_burst_interval_x8",dfi_t_ctrlupd_burst_interval_x8}})); 
						//TODO : DFIUPDTMG2
					end
				endtask
endclass
