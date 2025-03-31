/**************************************************************************
 * Testname: ai_core_dwpu_bypass_test
 * Author  : Roswin
* Description: This testcase checks the ifd0-> DWPU -> iau -> dpu -> odr 
                and ifd1->dpu-> odr paths in bypass mode. Here mv bypass is
                used in the dpu.
 * ************************************************************************/
`ifndef GUARD_AI_CORE_DWPU_BYPASS_TEST_SV
`define GUARD_AI_CORE_DWPU_BYPASS_TEST_SV
typedef aic_ls_ifd_seq#(ai_core_env)            aic_ls_ifd_seq_t;
typedef aic_ls_odr_seq#(ai_core_env)            aic_ls_odr_seq_t;
class ai_core_dwpu_bypass_test extends ai_core_base_test;
  // Factory registration
  `uvm_component_utils(ai_core_dwpu_bypass_test);

  aic_ls_ifd_seq_t            m_ifd_seq[];
  aic_ls_odr_seq_t            m_odr_seq[];
  //dpu_mv_instruction_sequence dpu_mv_instruction_seq;
  //dpu_cmd_descriptor_sequence dpu_cmd_descriptor_seq;
  int unsigned                    m_ifd_tlast_count[];
  int unsigned                    m_odr_tlast_count[];
  int unsigned                    m_ifd_mem_base_offsett[];
  int unsigned                    m_odr_mem_base_offsett[];
  //bit [15:0] addr_descr_start0;

  // Class constructor
  function new (string name="ai_core_dwpu_bypass_test", uvm_component parent);
    super.new (name, parent);
    m_ifd_seq = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_seq = new[AIC_LS_ENV_ODR_NUM_DEVICE];
    m_ifd_tlast_count = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_tlast_count = new[AIC_LS_ENV_ODR_NUM_DEVICE];
    m_ifd_mem_base_offsett = new[AIC_LS_ENV_IFD_NUM_DEVICE];
    m_odr_mem_base_offsett = new[AIC_LS_ENV_ODR_NUM_DEVICE];

  endfunction : new

  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_dwpu_bypass_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
   // iid_if_i.iid_i = 0;
     //m_env_cfg.m_ddpu_env_cfg.MVM_FLOW = 0;  //for dwpu 
     //m_env_cfg.m_ddpu_env_cfg.has_coverage = 0;  //for mvm 
    `uvm_info ("ai_core_dwpu_bypass_test", "Build phase exited", UVM_HIGH)
  endfunction : build_phase

  // Start of simulation phase
  function void start_of_simulation_phase (uvm_phase phase);
    super.start_of_simulation_phase(phase);
  endfunction: start_of_simulation_phase

  virtual function void randomize_sequences();  //function to randomise the ifd and odr sequences
    int unsigned num_bytes;
    int unsigned tlast_count;
    foreach (AIC_LS_DMC_IFD_DEVICE[i]) begin
      m_ifd_seq[i] = aic_ls_ifd_seq_t::type_id::create($sformatf("m_ifd_seq_%0d",i));
      m_ifd_seq[i].m_env_name = "AI_CORE_ENV";
    end
    foreach (AIC_LS_DMC_ODR_DEVICE[i]) begin
      m_odr_seq[i] = aic_ls_odr_seq_t::type_id::create($sformatf("m_odr_seq_%0d",i));
       m_odr_seq[i].m_env_name = "AI_CORE_ENV";
    end
    foreach (m_ifd_seq[i]) begin
      m_ifd_seq[i].m_prev_tlast_count = m_ifd_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      m_ifd_seq[i].m_enable_wr_to_l1 = 1;                     // We are preloading aicore L1
      if (!(m_ifd_seq[i].randomize() with {
        m_ag_cmd_format   == CMDFORMAT_LINEAR;
        m_device          == AIC_LS_DMC_IFD_DEVICE[i];
        m_ag_length       == 8;
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_ifd_seq!")
      end
    end
    foreach (m_odr_seq[i]) begin
      m_odr_seq[i].m_prev_tlast_count = m_odr_tlast_count[i]; // set prev tlast count before randomize to add in post randomize of the seq
      if (!(m_odr_seq[i].randomize() with {
        m_ag_cmd_format   == CMDFORMAT_LINEAR;
        m_device          == AIC_LS_DMC_ODR_DEVICE[i];
        m_ag_length == (m_ifd_seq[4].m_ag_length);
      })) begin
        `uvm_fatal(get_name(), "Randomization failed for m_odr_seq!")
      end
    end
  endfunction

  // Main phase
  virtual task main_phase(uvm_phase phase);

   phase.raise_objection(this);
   super.main_phase(phase);

   `uvm_info(get_type_name(), "Entered uvm main phase", UVM_LOW);
    uvm_sw_ipc_wait_event(16);
   `uvm_info(get_type_name(), "Received the event 16 from C test and DMA configurations and stimulus tranfer will start now", UVM_LOW);

    randomize_sequences();

   `uvm_info(get_name(),$sformatf("Setting the command descriptor for dwpu to be in bypass mode"), UVM_LOW)
   axi_write_txn(`AI_CORE_DID_DWPU_COMMAND_DESC,64'h0009_0000_0000_0000, 1'b1);
   env.m_ral.write_reg(.regblock_num(D_DWPU_REGMOD),  .data(64'h1), .name("cmdblk_ctrl"));


   `uvm_info(get_name(),$sformatf("Setting the command descriptor for iau to be in bypass mode"), UVM_LOW)
   axi_write_txn(`AI_CORE_DID_IAU_COMMAND_DESC,64'h0009_0000_0000_0000, 1'b1);
   env.m_ral.write_reg(.regblock_num(D_IAU_REGMOD),  .data(64'h1), .name("cmdblk_ctrl")); //iau

   `uvm_info(get_name(),$sformatf("Setting the command descriptor for dpu to be in bypass mode"), UVM_LOW) //if we are using mv bypass, no need of this
   axi_write_txn(`AI_CORE_DID_DPU_COMMAND_DESC,64'h0009_0000_0000_0000,1'b1);
   env.m_ral.write_reg(.regblock_num(D_DPU_REGMOD),  .data(64'h1), .name("cmdblk_ctrl")); //dpu
     

   //  //---------------------------------------------- PROGRAM 1 - for setting dpu for ifd0 input----------------------------------------------
   //  // Randomize the instruction sequence
   //   dpu_mv_instruction_seq = dpu_mv_instruction_sequence::type_id::create($sformatf("dpu_mv_instruction_seq"));
   //   dpu_mv_instruction_seq.m_dpu_env_name = "AI_CORE_DDPU_ENV";
   //   dpu_mv_instruction_seq.randomize() with {
   //   src0 == DPU_SRC_STREAM_IFD0_INT32;
   //   dest == DPU_DST_STREAM_O_INT8;
   //   instruction_addr == 32'h150;
   //   rfs == 1;
   //   };

   //   dpu_mv_instruction_seq.start(env.m_axi_system_env.master[1].sequencer);
   //   addr_descr_start0 = dpu_mv_instruction_seq.instruction_addr;

   //  //---------------------------------------------- PROGRAM 1 - for setting dpu for ifd1 input----------------------------------------------
   //  // Randomize the instruction sequence
   //   dpu_mv_instruction_seq = dpu_mv_instruction_sequence::type_id::create($sformatf("dpu_mv_instruction_seq"));
   //   dpu_mv_instruction_seq.m_dpu_env_name = "AI_CORE_DDPU_ENV";
   //   dpu_mv_instruction_seq.randomize() with {
   //   src0 == DPU_SRC_STREAM_IFD1_INT8;
   //   dest == DPU_DST_STREAM_L_INT8;
   //   instruction_addr == addr_descr_start0+1;
   //   rfs == 1;
   //   };

   //   dpu_mv_instruction_seq.start(env.m_axi_system_env.master[1].sequencer);

   fork
   begin
    m_ifd_seq[4].start(null); // mvm ifd0
   end

 //   begin
 //   //---------------------------------------------- COMMAND 1 ----------------------------------------------
 //   /*** Setting up dpu cmd descriptor  ****/
 //     dpu_cmd_descriptor_seq = dpu_cmd_descriptor_sequence::type_id::create($sformatf("dpu_cmd_descriptor_seq"));
 //     dpu_cmd_descriptor_seq.m_dpu_env_name = "AI_CORE_DDPU_ENV";
 //     dpu_cmd_descriptor_seq.randomize() with {
 //     loop_start == addr_descr_start0;
 //     loop_len == 2;
 //     header.cmd_format == DPU_CMD_LOOPONLY;
 //     header.cmd_id == 'd3;
 //     loop_iter == 1;
 //   };
 //    /*** Executing dpu program used for moving***/
 //    dpu_cmd_descriptor_seq.start(env.m_axi_system_env.master[1].sequencer);
 //   end

    begin
     m_odr_seq[1].start(null); // dwpu odr
    end
  join


//  fork
//   begin
//    fork
//       m_ifd_seq[3].wait_data_done();
//    join
//    if (m_ifd_seq[3].m_use_token_mechanism==0 ) begin
//       m_ifd_seq[3].read_register("cmdblk_status", "idle", 1, 1); // poll IDLE field to be 1
//    end
//   end
//
//  join
//
   #100us;
   `uvm_info(get_type_name(), "DMA transfers done, Generating event 1", UVM_LOW);
    uvm_sw_ipc_gen_event(1);

     phase.drop_objection(this);

  endtask : main_phase


endclass:ai_core_dwpu_bypass_test

`endif // GUARD_AI_CORE_DWPU_BYPASS_TEST_SV



