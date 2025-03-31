//
// File: top_example_vseq.svh
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
// The purpose of this example virtual sequence is to show how the default or selected sequences for 
// each QVIP can be run. The sequences are run in series in an arbitary order. 

`include "lpddr_subsystem_phy_init_details.sv"
`include "init_from_snps_sim.sv"

`define RETURN_MODEL_REG(REG_NAME) reg_value = reg_model.`REG_NAME`.get();
`define GET_FIELD(REG_NAME,FIELD_NAME) field = REG_NAME.get_field_by_name(FIELD_NAME);

typedef struct {string name;bit [31:0] value;} field_t;
class top_example_vseq extends top_vseq_base;
    `uvm_object_utils(top_example_vseq)
    lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block reg_model;
    uvm_status_e status;
    bit[31:0]reg_value_1;

    byte unsigned wr_data_l[] ={1,0,0,0};
    function new
    (
        string name = "top_example_vseq"
    );
        super.new(name);
	if(!uvm_config_db#(lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block)::get(null,"","reg_model",reg_model))
		`uvm_error("lpddr_subsystem_apb_reg_block","reg model not found")
    endfunction
    
    extern function bit[31:0]generate_write_value(uvm_reg reg_name, field_t fields[]);
    extern task body;
    extern task register_config();
    extern task phy_register_config();
    extern task lpddr_subsystem_reset;
    
endclass: top_example_vseq

task top_example_vseq::body;  
    apb_wr_seq apb_master_0_seq_0 = apb_wr_seq::type_id::create("apb_wr_seq");
    axi4_fixed_wr_deparam_seq axi4_master_0_seq_1 = axi4_fixed_wr_deparam_seq::type_id::create("axi4_fixed_wr_deparam_seq");

    // Sequences run in the following order
    // TODO 
    #1us;
    lpddr_subsystem_reset();

    #1us;
        
endtask: body

// -------------------------------------------------------------------------------------------------
//  Initialization Sequence  register configurations
// -------------------------------------------------------------------------------------------------
task top_example_vseq::register_config();

  //reg_model.lpddr_ctrl_block.DFIPHYMSTR_reg.write(status,reg_value_1);
  //reg_model.lpddr_ctrl_block.DFIPHYMSTR_reg.read(status,reg_value_1);
  // reg_model.lpddr_ctrl_block.DFIUPD0_reg.print();
 
  // -------------------------------------------------------------------------------------------------
  //  Initialization Sequence  
  // -------------------------------------------------------------------------------------------------
  
  // Step 2 : TODO : Note 1 is not clear
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.dfi_phymstr_en.write(status,'b1);
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.dfi_phyupd_en.write(status,'b1);

  // Step 3 : reset_dut and set following register
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.dis_auto_refresh.write(status,'b1);
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",'b0},'{"selfref_en",'b0},'{"en_dfi_dram_clk_disable",'b0}}));
  
  // Step 4 : De assert reset
  //reg_model.lpddr_ctrl_block.DFISTAT_reg.read(status,reg_value_1);//generate_write_value(reg_model.lpddr_ctrl_block.DFISTAT_reg,'{'{"dfi_init_complete",'b1}}));
  // TODO
  
  // Step 5
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.dfi_init_complete_en.write(status,'b0);
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.dfi_reset_n.write(status,'b1);
  
  // Step 6 
    phy_register_config();

  //  Step 7
  //-- > forever begin
  //-- >   #100ns;
  //-- >   reg_model.DWC_DDRPHYA_APBONLY0.UctShadowRegs.read(status,reg_value_1);
  //-- >   if(reg_value_1[0] == 1'b0) break;
  //-- > end

  //  Step 9
  reg_model.DWC_DDRPHYA_APBONLY0.DctWriteProt.write(status,'b0);

  //  Step 10
  //-- > forever begin
  //-- >   #100ns;
  //-- >   reg_model.DWC_DDRPHYA_APBONLY0.UctShadowRegs.read(status,reg_value_1);
  //-- >   if(reg_value_1[0] == 1'b1) break;
  //-- > end

  //  Step 11
  reg_model.DWC_DDRPHYA_APBONLY0.DctWriteProt.write(status,'b1);

  //  Step 12
  //-- > forever begin
  //-- >   #100ns;
  //-- >   reg_model.DWC_DDRPHYA_APBONLY0.UctShadowRegs.read(status,reg_value_1);
  //-- >   if(reg_value_1[0] == 1'b1) break;
  //-- > end

  // Step 13
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_init_start",'b1}}));
  
  // Step 14
  // reg_model.lpddr_ctrl_block.DFISTAT_reg.read(status,reg_value_1);//generate_write_value(reg_model.lpddr_ctrl_block.DFISTAT_reg,'{'{"dfi_init_complete",'b1}}));
  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.print();
  /* 
  // Step 15
  reg_model.lpddr_ctrl_block.DFIMISC_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DFIMISC_reg,'{'{"dfi_init_start",'b0}}));
  #200ns;
  
  // Step 16 : TODO : Need to calculate value of each field from databook.
  // Register 1
  reg_model.lpddr_ctrl_block.RANKTMG0_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.RANKTMG0_reg,'{'{"diff_rank_wr_gap",'b0}}));
  #200ns;
  // Register 2
  reg_model.lpddr_ctrl_block.RANKTMG0_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.RANKTMG0_reg,'{'{"diff_rank_rd_gap",'b0}}));
  #200ns;
  // Register 3
  reg_model.lpddr_ctrl_block.DRAMSET1TMG2_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DRAMSET1TMG2_reg,'{'{"rd2wr",'b0}}));
  #200ns;
  // Register 4
  reg_model.lpddr_ctrl_block.DRAMSET1TMG2_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DRAMSET1TMG2_reg,'{'{"wr2rd",'b0}}));
  #200ns;
  // Register 5
  reg_model.lpddr_ctrl_block.DRAMSET1TMG24_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DRAMSET1TMG24_reg,'{'{"rd2wr_s",'b0}}));
  #200ns;
  // Register 6
  reg_model.lpddr_ctrl_block.DRAMSET1TMG9_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DRAMSET1TMG9_reg,'{'{"wr2rd_s",'b0}}));
  #200ns;
  // Register 7
  reg_model.lpddr_ctrl_block.DFITMG0_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DFITMG0_reg,'{'{"dfi_t_ctrl_delay",'h7}}));
  #200ns;
  // Register 8
  reg_model.lpddr_ctrl_block.DFITMG1_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DFITMG1_reg,'{'{"dfi_t_wrdata_delay",'b0}}));
  #200ns;
  // Register 9
  reg_model.lpddr_ctrl_block.DFITMG2_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DFITMG2_reg,'{'{"dfi_twck_delay",'b0}}));
  #200ns;
  
  // Step 17
  reg_model.lpddr_ctrl_block.DFIMISC_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.DFIMISC_reg,'{'{"dfi_init_complete_en",'b1}}));
  #200ns;
  
  // Step 18
  reg_model.lpddr_ctrl_block.PWRCTL_reg.write(status,generate_write_value(reg_model.lpddr_ctrl_block.PWRCTL_reg,'{'{"selfref_sw",'b0}}));
  */ 
  #1us;
endtask : register_config

// -------------------------------------------------------------------------
// Description : This method is to write on registers via APB
// Method Name generate_write_value
// Argument : reg_name : Which register to perform write, 
//            fields   : Which specific register field to write
// -------------------------------------------------------------------------
function bit[31:0] top_example_vseq::generate_write_value(uvm_reg reg_name, field_t fields[]);
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

// -------------------------------------------------------------------------
// Description : This method performs resetting sequence steps 
// Method Name : lpddr_subsystem_reset
// -------------------------------------------------------------------------
task top_example_vseq::lpddr_subsystem_reset();
    apb_wr_seq apb_master_1_seq_0 = apb_wr_seq::type_id::create("apb_wr_seq");
    apb_rd_seq apb_master_1_seq_1 = apb_rd_seq::type_id::create("apb_rd_seq");
    apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
    // Step -3
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})


    wr_data_l ={2,0,0,0};
    // Step -4
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    // Step -5
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    // Step -6
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    #200ns;
    `uvm_do_on_with(apb_master_1_seq_1,apb_master_1_sqr,{addr == 'h8;})
    #200ns;

    wr_data_l ={1,0,0,0};
    // Step -7
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h0;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})


      foreach(phy_init_snps_data_details_pre[idx]) begin
          wr_data_l= {phy_init_snps_data_details_pre[idx].value[7:0],phy_init_snps_data_details_pre[idx].value[15:8],phy_init_snps_data_details_pre[idx].value[23:16],phy_init_snps_data_details_pre[idx].value[31:24]};
	  if(phy_init_snps_data_details_pre[idx].access_type == 'h1)
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == {8'h01,phy_init_snps_data_details_pre[idx].reg_addr[24:0]};foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
	  else if (phy_init_snps_data_details_pre[idx].access_type == 'h2) 
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == phy_init_snps_data_details_pre[idx].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
      end



    // Step - 8 TODO configure all register required for LPDDR subsystem up
    // Step -9 Cntrl Reset
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h4;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    #200ns;

    // Step -10 -- PHY Reset
    `uvm_do_on_with(apb_master_1_seq_0,apb_master_1_sqr,{addr == 'h8;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    #200ns;
#1us;

    //top_example_vseq::register_config();
    top_example_vseq::phy_register_config();

    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.read(status,reg_value_1);//generate_write_value(reg_model.lpddr_ctrl_block.DFISTAT_reg,'{'{"dfi_init_complete",'b1}}));
    #200ns;
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.read(status,reg_value_1);
endtask : lpddr_subsystem_reset


task top_example_vseq::phy_register_config();
	bit [31:0]phy_addr;
    apb_wr_seq apb_master_0_seq_wr = apb_wr_seq::type_id::create("apb_wr_seq");
    apb_rd_seq apb_master_0_seq_rd = apb_rd_seq::type_id::create("apb_rd_seq");

      foreach(phy_init_snps_data_details[idx]) begin
          wr_data_l= {phy_init_snps_data_details[idx].value[7:0],phy_init_snps_data_details[idx].value[15:8],phy_init_snps_data_details[idx].value[23:16],phy_init_snps_data_details[idx].value[31:24]};
	  if(phy_init_snps_data_details[idx].access_type == 'h1 && phy_init_snps_data_details[idx].rd_wr == 'h3)
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == {8'h01,phy_init_snps_data_details[idx].reg_addr[24:0]};foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
	  else if (phy_init_snps_data_details[idx].access_type == 'h2 && phy_init_snps_data_details[idx].rd_wr == 'h3) 
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == phy_init_snps_data_details[idx].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
	  if(phy_init_snps_data_details[idx].rd_wr=='h2 && phy_init_snps_data_details[idx].reg_addr== 'h1040088) #65us;
      end

   
   /// forever begin
   ///   #300ns;
   ///   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.read(status,reg_value_1);//generate_write_value(reg_model.lpddr_ctrl_block.DFISTAT_reg,'{'{"dfi_init_complete",'b1}}));
   ///   if(reg_value_1[0] == 1'b1) break;
   /// end
    foreach(phy_init_snps_data_details_post[idx]) begin
          wr_data_l= {phy_init_snps_data_details_post[idx].value[7:0],phy_init_snps_data_details_post[idx].value[15:8],phy_init_snps_data_details_post[idx].value[23:16],phy_init_snps_data_details_post[idx].value[31:24]};
	  if(phy_init_snps_data_details_post[idx].access_type == 'h1 && phy_init_snps_data_details_post[idx].rd_wr == 'h3)
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == {8'h01,phy_init_snps_data_details_post[idx].reg_addr[24:0]};foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
	  else if (phy_init_snps_data_details_post[idx].access_type == 'h2 && phy_init_snps_data_details_post[idx].rd_wr == 'h3) 
		  `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == phy_init_snps_data_details_post[idx].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
	  if(phy_init_snps_data_details_post[idx].rd_wr=='h2 && phy_init_snps_data_details_post[idx].reg_addr== 'h1040088) #65us;
      end

    /// -------- >foreach(phy_init_headings[step_name]) begin
    /// -------- >  phy_init_data_t init_data[] = new[phy_init_data_details[step_name].size()] (phy_init_data_details[step_name]);
    /// -------- >  `uvm_info("phy_register_config",$printf("Step %0s: %0s",step_name,phy_init_headings[step_name]),UVM_NONE);
    /// -------- >  foreach(init_data[idx]) begin
    /// -------- >    if(init_data[idx].step_type == REG_WRITE) begin
    /// -------- >      wr_data_l= {init_data[idx].value[7:0],init_data[idx].value[15:8],init_data[idx].value[23:16],init_data[idx].value[31:24]};
    /// -------- >      `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == init_data[idx].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    /// -------- >    end
    /// -------- >  end
    /// -------- >end
    // --> //for(int itr = 0; itr<phy_init_data_details["C"].size;itr++)begin
    // --> for(int itr = 0; itr<2;itr++)begin
    // -->   wr_data_l= {phy_init_data_details["C"][itr].value[7:0],phy_init_data_details["C"][itr].value[15:8],phy_init_data_details["C"][itr].value[23:16],phy_init_data_details["C"][itr].value[31:24]};
    // -->   //`uvm_info("phy_register_config",$sformatf("PHY_ADDR=%0d and data =%0p",phy_init_data_details["C"][0].reg_addr,wr_data_l),UVM_LOW)
    // -->   `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == phy_init_data_details["C"][itr].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    // -->   #200ns;
    // --> end

    // --> `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == phy_init_data_details["C"][0].reg_addr;})
    // --> #200ns;

    // --> /// for(int itr = 0; itr<phy_init_data_details["D"].size;itr++)begin
    // --> ///   wr_data_l= {phy_init_data_details["D"][itr].value[7:0],phy_init_data_details["D"][itr].value[15:8],phy_init_data_details["D"][itr].value[23:16],phy_init_data_details["D"][itr].value[31:24]};
    // --> ///   //`uvm_info("phy_register_config",$sformatf("PHY_ADDR=%0d and data =%0p",phy_init_data_details["D"][0].reg_addr,wr_data_l),UVM_LOW)
    // --> ///   `uvm_do_on_with(apb_master_0_seq_wr,apb_master_0_sqr,{addr == phy_init_data_details["D"][itr].reg_addr;foreach(wr_data_l[i])wr_data[i] == wr_data_l[i];})
    // --> ///   #200ns;
    // --> /// end

    // --> `uvm_do_on_with(apb_master_0_seq_rd,apb_master_0_sqr,{addr == phy_init_data_details["D"][0].reg_addr;})
endtask : phy_register_config
