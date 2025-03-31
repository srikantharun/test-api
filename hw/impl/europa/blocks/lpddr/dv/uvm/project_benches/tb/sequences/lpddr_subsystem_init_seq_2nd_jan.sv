// TODO this file is not being used, but ddrctl and phy reg are taken from
// databook and phyint c program in future snps reg configuration will be
// replaced register from this file 
//------------------------------------------------------------------------------
// Project     : Axelera lpddr Subsystem
// File Name   : lpddr_subsystem_init_seq.sv
// Unit Name   : lpddr_subsystem_init_seq
//------------------------------------------------------------------------------
// Description : This file contains the base virtual sequence for the lpddr
//               Subsystem Verification Environment.
//------------------------------------------------------------------------------
/// --- 
/// --- `ifndef LPDDR_SUBSYSTEM_INIT_SEQ_SVH
/// --- `define LPDDR_SUBSYSTEM_INIT_SEQ_SVH
/// --- 
/// --- `include "lpddr_subsystem_phy_init_details.sv"
/// --- 
/// --- `define RETURN_MODEL_REG(REG_NAME) reg_value = reg_model.`REG_NAME`.get();
/// --- 
/// --- 
/// --- class lpddr_subsystem_init_seq extends lpddr_subsystem_base_virtual_seq;
/// --- 
/// ---   `uvm_object_utils(lpddr_subsystem_init_seq)
/// --- 
/// ---   uvm_status_e status;
/// ---   bit[31:0]reg_value_1;
/// ---   byte unsigned wr_data_l[] ={1,0,0,0};
/// --- 
/// --- 
/// ---   //----------------------------------------------------------------------------
/// ---   // Function Name : new
/// ---   // Arguments     : string name
/// ---   //----------------------------------------------------------------------------
/// ---   function new ( string name = "lpddr_subsystem_init_seq");
/// ---     super.new(name);
/// ---   endfunction : new
/// --- 
/// ---   //----------------------------------------------------------------------------
/// ---   // Task Name     : body
/// ---   //----------------------------------------------------------------------------
/// ---   task body();
/// ---     
/// ---     // Apply Resets
/// ---     lpddr_subsystem_reset();
/// --- 
/// ---     // Initialization ctl and phy
/// ---     lpddr_ctl_init();
/// --- 
/// ---     // lpddr Controller Register 
/// ---     
/// ---     // Indicate init is complete;
/// ---     // TODO m_env_cfg.init_seq_done = 1'b1;
/// ---   endtask : body
/// --- 
/// ---   //----------------------------------------------------------------------------
/// ---   // Task Name     : lpddr_ctl_reg_during_reset
/// ---   // Description   : This task configure the controler registers which is
/// ---   //               required for the initialization to complete
/// ---   //----------------------------------------------------------------------------
/// ---   task configure_static_reg_during_reset();
/// ---     // Step 2 : TODO : confusion which Note to refer here Note 1 or Note below
/// ---     // the table 14-1
/// ---     // Note 1
/// ---     /*reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR,'{'{"dfi_phymstr_en",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0,'{'{"dfi_phyupd_en",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_en_sr",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0,'{'{"dfi_lp_data_req_en",'b1}}));
/// ---   
/// ---     // Note 
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.INITTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.INITTMG0,'{'{"skip_dram_init",2'b01}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",1'b1}}));
/// --- 
/// --- 
/// ---     // Step 3 : reset_dut and set following register
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",'b0},'{"selfref_en",'b0},'{"en_dfi_dram_clk_disable",'b0}}));
/// --- 
/// --- 
/// ---     // TODO find in snps waveform but not in the init steps 
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR0,'{'{"lpddr5",'b1}}));
/// ---     */
/// --- 
/// ---     ddrctl_register_config(); 
/// ---   endtask : configure_static_reg_during_reset 
/// --- 
/// ---   //----------------------------------------------------------------------------
/// ---   // Task Name     : lpddr_ctl_init
/// ---   // Description   : This task configure the controler registers which is
/// ---   //               required for the initialization to complete
/// ---   //----------------------------------------------------------------------------
/// ---   task lpddr_ctl_init();
/// --- /*
/// ---     // Step 4 : De assert reset this is done in lpddr_subsystem_reset
/// --- 
/// ---     // Step 5
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_init_complete_en",'b0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_reset_n",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
/// ---     */
/// --- 
/// ---     ddrctl_after_RST();
/// ---     // Step 6 
/// ---     phy_register_config();
/// ---     ddrctl_after_phy();
/// ---     ddrctl_register_config2();/*
/// ---     //  Step 7
/// ---     fork begin
/// ---       fork
/// ---         forever begin
/// ---           #1us; // TODO delay could increase to avoid multiple read sends
/// ---           reg_model.DWC_DDRPHYA_APBONLY0.UctShadowRegs.read(status,reg_value_1);
/// ---           `uvm_info("Poll PUB reg UctShadowRegs","expecting to set 0th bit to 0",UVM_LOW)
/// ---           if(reg_value_1[0] == 1'b0 && status==UVM_IS_OK) break;
/// ---         end
/// --- 	begin 
/// --- 	  #100us;
/// ---           `uvm_error("Poll Fail PUB reg UctShadowRegs","expecting to set 0th bit to 0")
/// ---         end
/// ---       join_any
/// ---       disable fork;
/// ---     end join
/// --- 
/// ---     // Step 8
/// ---     reg_model.DWC_DDRPHYA_APBONLY0.UctWriteOnlyShadow.read(status,reg_value_1);
/// --- 
/// ---     //  Step 9
/// ---     reg_model.DWC_DDRPHYA_APBONLY0.DctWriteProt.write(status,'b0);
/// --- 
/// ---     //  Step 10
/// ---     fork begin
/// ---       fork
/// ---         forever begin
/// ---           #1us;
/// ---           reg_model.DWC_DDRPHYA_APBONLY0.UctShadowRegs.read(status,reg_value_1);
/// ---           `uvm_info("Poll PUB reg UctShadowRegs","expecting to set 0th bit to 1",UVM_LOW)
/// ---           if(reg_value_1[0] == 1'b1 && status==UVM_IS_OK) break;
/// ---         end
/// --- 	begin 
/// --- 	  #100us;
/// ---           `uvm_error("Poll Fail PUB reg UctShadowRegs","expecting to set 0th bit to 1")
/// ---         end
/// ---       join_any
/// ---       disable fork;
/// ---     end join
/// --- 
/// ---     //  Step 11
/// ---     reg_model.DWC_DDRPHYA_APBONLY0.DctWriteProt.write(status,'b1);
/// --- 
/// ---     //  Step 12
/// ---     //  TODO MASTER.CalBusy does not find in the RAL
/// --- 
/// ---     // Step 13
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_init_start",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
/// ---     
/// ---     // Step 14
/// ---     fork begin
/// ---       fork
/// ---         forever begin
/// ---           #1us;
/// ---           reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.read(status,reg_value_1);
/// ---           `uvm_info("Poll PUB dfi_init_complete","expecting to set dfi_init_complete bit to 1",UVM_LOW)
/// ---           if(reg_value_1[0] == 1'b1&& status==UVM_IS_OK) break;
/// ---         end
/// --- 	begin 
/// --- 	  #100us;
/// ---           `uvm_error("Poll Fail PUB reg dfi_init_complete","expecting to set dfi_init_complete bit to 1")
/// ---         end
/// ---       join_any
/// ---       disable fork;
/// ---     end join 
/// ---     // Step 15
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_init_start",'b0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
/// ---     #200ns;
/// ---     
/// ---     // Step 16 : 
/// ---     // Register 1
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RANKTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RANKTMG0,'{'{"diff_rank_wr_gap",'h6}}));
/// ---     // Register 2
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RANKTMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RANKTMG0,'{'{"diff_rank_rd_gap",'h6}}));
/// ---     // Register 3
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG2,'{'{"rd2wr",'h6}}));
/// ---     // Register 4
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG2,'{'{"wr2rd",'hd}}));
/// ---     // Register 5
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG24.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG24,'{'{"rd2wr_s",'hf}}));
/// ---     // Register 6
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG9.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DRAMSET1TMG9,'{'{"wr2rd_s",'hd}}));
/// ---     // Register 7
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG0,'{'{"dfi_t_ctrl_delay",'h7}}));
/// ---     // Register 8
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG1,'{'{"dfi_t_wrdata_delay",'b0}}));
/// ---     // Register 9
/// ---     reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFITMG2,'{'{"dfi_twck_delay",'b0}}));
/// ---     
/// ---     // Step 17
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_init_complete_en",'b1},'{"dfi_reset_n",'b1}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SWCTL,'{'{"sw_done",1}}));
/// ---     
/// ---     // Step 18
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",'b0},'{"powerdown_en",'b1}}));
/// ---      
/// ---     // Step 19 
/// ---     fork begin
/// ---       fork
/// ---         forever begin
/// ---           #1us;
/// ---           reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.read(status,reg_value_1);
/// --- 	  `uvm_info("Poll ddrctl ","expecting to set operating mode in normal mode",UVM_LOW)
/// ---           if(reg_value_1[2:0] == 3'b001&& status==UVM_IS_OK) break;
/// ---         end
/// --- 	begin 
/// --- 	  #100us;
/// ---           `uvm_error("Poll Fail ddrctl ","expecting to set operating mode in normal mode")
/// ---         end
/// ---       join_any
/// ---       disable fork;
/// ---     end join 
/// --- 
/// ---     // TODO step 20 - step 3 register 
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",'b0}}));
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR,'{'{"dfi_phymstr_en",'b0}}));
/// --- 
/// ---     #5us;
/// ---     reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR,'{'{"dfi_phymstr_en",'b1}}));
/// ---     #100us;
/// --- */
/// ---   endtask : lpddr_ctl_init
/// --- 
/// ---   // -------------------------------------------------------------------------
/// ---   // Description : This method performs resetting sequence steps for PCTL 
/// ---   // Method Name : lpddr_subsystem_reset
/// ---   // -------------------------------------------------------------------------
/// ---     task lpddr_subsystem_reset();
/// ---       apb_wr_seq apb_master_1_seq_0 = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---       apb_rd_seq apb_master_1_seq_1 = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---       // Step - 1 and 2
/// ---       fork
/// ---         drive_ao_rst_n();
/// ---         drive_global_rst_n();
/// ---       join
/// --- 
/// ---       // Step -3
/// ---       wr_data_l ={1,0,0,0};
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---   
/// ---       wr_data_l ={2,0,0,0};
/// ---       // Step -4
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---       // Step -5
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---       // Step -6
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---   
/// ---       wr_data_l ={1,0,0,0};
/// ---       // Step -7
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---   
/// ---       #200ns;// TODO gap to figure out above steps de-asserts all rst for some time duration
/// ---       // Step - 8 TODO configure all register required for LPDDR subsystem up
/// ---       // like static register
/// ---       configure_static_reg_during_reset();
/// --- 
/// ---       // Step -9 De-asssert Cntrl Reset
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---   
/// ---       // Step -10 De-asssert PHY Reset
/// ---       `uvm_do_on_with(apb_master_1_seq_0, apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---   
/// ---       #0.4us;// reference from snps
/// ---       // register_config(); TODO 
/// ---       // reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.read(status,reg_value_1);
/// ---       // #200ns;
/// ---       // reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.read(status,reg_value_1);
/// ---       // #200ns;
/// ---   endtask : lpddr_subsystem_reset
/// --- 
/// ---   task phy_register_config();
/// ---     bit [31:0]phy_addr;
/// ---     apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---     apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---   
/// ---   
/// ---     foreach(phy_init_headings[step_name]) begin
/// --- 
/// ---       // if(phy_init_skiptrain_details.exists(step_name)) begin
/// ---       //   phy_init_data_t init_data[] = new[phy_init_skiptrain_details[step_name].size()] (phy_init_skiptrain_details[step_name]);
/// ---       // if(phy_init_train_details.exists(step_name)) begin
/// ---       //   phy_init_data_t init_data[] = new[phy_init_train_details[step_name].size()] (phy_init_train_details[step_name]);
/// ---        //if(phy_init_devinit_skiptrain_details.exists(step_name)) begin
/// ---        //  phy_init_data_t init_data[] = new[phy_init_devinit_skiptrain_details[step_name].size()] (phy_init_devinit_skiptrain_details[step_name]);
/// ---        if(snps_phy_init_details.exists(step_name)) begin
/// ---          phy_init_data_t init_data[] = new[snps_phy_init_details[step_name].size()] (snps_phy_init_details[step_name]);
/// ---          `uvm_info("phy_register_config",$psprintf("Step %0s: %0s",step_name,phy_init_headings[step_name]),UVM_NONE);
/// ---         foreach(init_data[idx]) begin
/// ---           if(init_data[idx].step_type == REG_WRITE) begin
/// ---             wr_data_l= {init_data[idx].value[7:0],init_data[idx].value[15:8],init_data[idx].value[23:16],init_data[idx].value[31:24]};
/// ---             `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == local::init_data[idx].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---           end
/// ---           else if(init_data[idx].step_type == POLL) begin
/// ---             phy_addr = init_data[idx].reg_addr;
/// ---             fork begin
/// ---               fork 
/// ---                forever begin
/// ---                       `uvm_info("ADDR_DEBUG POLL START ",$psprintf("Addr = %0h",init_data[idx].reg_addr),UVM_NONE);
/// ---                       `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == phy_addr; })
/// ---                       #6ns;
/// ---                     end
/// ---                begin
/// ---                       #5ns;
/// ---                wait(m_io_vif.apb_master_0_prdata == init_data[idx].value);
/// ---                `uvm_info("ADDR_DEBUG POLL Successful",$psprintf("Addr = %0h poll value be=%0h",init_data[idx].reg_addr,init_data[idx].value),UVM_NONE);
/// ---                end
/// ---                begin
/// ---                #5us;
/// ---                `uvm_info("ADDR_DEBUG POLL Timeout",$psprintf("Addr = %0h poll value should be=%0h",init_data[idx].reg_addr,init_data[idx].value),UVM_NONE);
/// ---                end
/// ---               join_any
/// ---               disable fork;
/// ---             end join
/// ---          end
/// ---          else begin
/// ---          `uvm_info("phy_register_config",$psprintf("Step %0s: %0s - No Stimulus defined for Simulation Purposes.",step_name,phy_init_headings[step_name]),UVM_NONE);
/// ---          end
/// ---       end
/// ---     end
/// ---     end
/// ---   endtask : phy_register_config
/// --- 
/// ---    task ddrctl_register_config2();
/// ---     bit [31:0]ddr_addr;
/// ---     bit [31:0]ddr_data;
/// ---     apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---     apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---   
/// ---   
/// ---     foreach(ddrctl_init_headings[step_name]) begin
/// --- 
/// ---       if(ddrctl_init2_details.exists(step_name)) begin
/// ---         phy_init_data_t init_data[] = new[ddrctl_init2_details[step_name].size()] (ddrctl_init2_details[step_name]);
/// ---          `uvm_info("ddrctl_register_config2",$psprintf("Step %0s: %0s",step_name,ddrctl_init_headings[step_name]),UVM_NONE);
/// ---         foreach(init_data[idx]) begin
/// ---           if(init_data[idx].step_type == REG_WRITE) begin
/// --- 		  ddr_addr = init_data[idx].reg_addr;
/// --- 		  ddr_addr[25] = 1;//local::init_data[idx].reg_addr
/// --- 
/// ---             wr_data_l= {init_data[idx].value[7:0],init_data[idx].value[15:8],init_data[idx].value[23:16],init_data[idx].value[31:24]};
/// ---          `uvm_info("ADDR_DEBUG",$psprintf("Addr = %0h",init_data[idx].reg_addr),UVM_NONE);
/// ---             `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// --- 	                                                          foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---           end
/// ---           else if(init_data[idx].step_type == POLL) begin
/// ---              ddr_addr = init_data[idx].reg_addr;
/// ---              ddr_addr[25] = 1;//local::init_data[idx].reg_addr
/// --- 	     fork begin
/// ---                fork 
/// ---                  forever begin
/// ---                    `uvm_info("ADDR_DEBUG POLL START ",$psprintf("Addr = %0h",init_data[idx].reg_addr),UVM_NONE);
/// ---                    `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == ddr_addr; })
/// ---                    if(init_data[idx].reg_addr == 'h10090) #30ns; 
/// --- 		   else if(init_data[idx].reg_addr == 'h10014) #430ns;
/// --- 		   else begin end//#6ns;
/// ---                  end
/// ---                  begin
/// --- 	           wait(m_io_vif.apb_master_0_prdata == init_data[idx].value);
/// ---                    `uvm_info("ADDR_DEBUG POLL Successful",$psprintf("Addr = %0h poll value =%0h",init_data[idx].reg_addr,init_data[idx].value),UVM_NONE);
/// ---                  end
/// ---                  begin
/// --- 		    #10us;
/// ---                    `uvm_info("ADDR_DEBUG POLL Timeout",$psprintf("Addr = %0h poll value should be=%0h",init_data[idx].reg_addr,init_data[idx].value),UVM_NONE);
/// ---                  end
/// --- 	       join_any
/// --- 	       disable fork;
/// ---              end join
/// --- 	  end
/// ---           else begin
/// ---           `uvm_info("ddrctl_register_config2",$psprintf("Step %0s: %0s - No Stimulus defined for Simulation Purposes.",step_name,ddrctl_init_headings[step_name]),UVM_NONE);
/// ---           end
/// ---         end
/// ---      end
/// --- 
/// ---     end
/// ---   endtask : ddrctl_register_config2
/// --- 
/// ---   task ddrctl_register_config();
/// ---     bit [31:0]ddr_addr;
/// ---     bit [31:0]ddr_data;
/// ---     apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---     apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---   
/// ---  
/// ---     // POLL
/// --- `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == 32'h201_0ff8; })
/// --- `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == 32'h201_0ffc; })
/// ---     foreach(ddrctl_init_headings[step_name]) begin
/// --- 
/// ---       if(ddrctl_init_details.exists(step_name)) begin
/// ---         phy_init_data_t init_data[] = new[ddrctl_init_details[step_name].size()] (ddrctl_init_details[step_name]);
/// ---          `uvm_info("ddrctl_register_config",$psprintf("Step %0s: %0s",step_name,ddrctl_init_headings[step_name]),UVM_NONE);
/// ---         foreach(init_data[idx]) begin
/// ---           if(init_data[idx].step_type == REG_WRITE) begin
/// --- 		  ddr_addr = init_data[idx].reg_addr;
/// --- 		  ddr_addr[25] = 1;//local::init_data[idx].reg_addr
/// --- 
/// ---             wr_data_l= {init_data[idx].value[7:0],init_data[idx].value[15:8],init_data[idx].value[23:16],init_data[idx].value[31:24]};
/// ---          `uvm_info("ADDR_DEBUG",$psprintf("Addr = %0h",init_data[idx].reg_addr),UVM_NONE);
/// ---             `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// --- 	                                                          foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---           end
/// ---         end
/// ---       end
/// ---       else begin
/// ---       `uvm_info("ddrctl_register_config",$psprintf("Step %0s: %0s - No Stimulus defined for Simulation Purposes.",step_name,ddrctl_init_headings[step_name]),UVM_NONE);
/// ---       end
/// --- 
/// ---     end
/// ---           								  
/// --- 
/// ---     //#500ns;
/// ---     
/// ---   endtask : ddrctl_register_config
/// --- 
/// ---   task ddrctl_after_phy();
/// ---     bit [31:0]ddr_addr;
/// ---     bit [31:0]ddr_data;
/// ---     apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---     apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---     ddr_data='d0	;								  
/// ---     ddr_addr=32'h10c80;
/// ---     ddr_addr[25]=1;
/// ---     wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---     `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---     ddr_data='d65588	;								  
/// ---     ddr_addr=32'h10510;
/// ---     ddr_addr[25]=1;
/// ---     wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---     `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---     
/// ---     ddr_data='d1	;								  
/// ---     ddr_addr=32'h10c80;
/// ---     ddr_addr[25]=1;
/// ---     wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---     `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 							       
/// --- 
/// ---     // POLL 
/// ---     ddr_addr=32'h10c84;
/// ---     ddr_addr[25]=1;
/// ---     `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == ddr_addr; })
/// ---     if(m_io_vif.apb_master_0_prdata != 1) `uvm_error("POLL failedd h10c84"," values should be 1")
/// --- 
/// ---     // POLL 
/// ---     ddr_addr=32'h10510;
/// ---     ddr_addr[25]=1;
/// ---     `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == ddr_addr; })
/// ---     if(m_io_vif.apb_master_0_prdata != 32'd65588) `uvm_error("POLL failedd h10510"," values should be d65588")
/// --- 
/// ---     // PHY write 
/// ---     ddr_data='d0	;								  
/// ---     ddr_addr=32'hd0000<<2;
/// ---     wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---     `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---     // PHY write 
/// ---     ddr_data='d1	;								  
/// ---     ddr_addr=32'hd0000<<2;
/// ---     wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---     `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---     							       
/// --- 							       
/// ---   endtask : ddrctl_after_phy 
/// ---   task ddrctl_after_RST();
/// ---     bit [31:0]ddr_addr;
/// ---     bit [31:0]ddr_data;
/// ---     apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
/// ---     apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");
/// ---  wr_data_l= {8'd1,8'd0,8'd0,8'd0};
/// ---  ddr_addr=32'h10180;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---  wr_data_l= {8'd0,8'd0,8'd0,8'd0};
/// ---  ddr_addr=32'h10180;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr ==ddr_addr; 
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---  wr_data_l= {8'd0,8'd0,8'd0,8'd0};
/// ---  ddr_addr=32'h10180;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr ==ddr_addr; 
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 							       
/// ---  wr_data_l= {8'd0,8'd0,8'd0,8'd0};
/// ---  ddr_addr=32'h10100;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr ==ddr_addr; 
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---  wr_data_l= {8'd0,8'd0,8'd0,8'd0};
/// ---  ddr_addr=32'h10c80;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr; 
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---  ddr_data='d65540	;								  
/// ---  ddr_addr=32'h10510;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---    ddr_data='d1;
/// ---  ddr_addr=32'h10c80;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr ==ddr_addr; 
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---  #1.25ns;
/// ---  // POLL						  
/// ---  ddr_addr=32'h10c84;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr ==ddr_addr;}) 
/// --- 						  
/// ---    ddr_data='d0;
/// ---  ddr_addr=32'h10c80;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---    ddr_data='d65556	;								  
/// ---  ddr_addr=32'h10510;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// --- 
/// ---  ddr_data='d1;
/// ---  ddr_addr=32'h10c80;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == ddr_addr;
/// ---                                                        foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---  #1.25ns;
/// ---  // POLL						  
/// ---  ddr_addr=32'h10c84;
/// ---  ddr_addr[25]=1;
/// ---  `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr ==ddr_addr;})
/// --- 
/// ---    ddr_data='d0;
/// ---  ddr_addr=32'h10208;
/// ---  ddr_addr[25]=1;
/// ---  wr_data_l= {ddr_data[7:0],ddr_data[15:8],ddr_data[23:16],ddr_data[31:24]};
/// ---  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr ==ddr_addr; 
/// --- 	                                                          foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
/// ---             
/// ---   endtask
/// --- endclass : lpddr_subsystem_init_seq
/// --- 
/// --- `endif //LPDDR_SUBSYSTEM_INIT_SEQ_SVH 
