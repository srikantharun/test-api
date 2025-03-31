// MVM basic test-case class
// Backpressure test
//Applying delayed sequence for IAU interface in a concurrent proframming and execution random multiplication test, so that IAU does not accept output from MVM.
//This results in banks going inactive inside the MVM. After ready getting asserted banks go active again
`ifndef __AI_CORE_MVM_CONCURRENT_PRG_EXE_RANDOM_MATRIX_MLTPLCTN_BCKPRSR_TEST__
`define __AI_CORE_MVM_CONCURRENT_PRG_EXE_RANDOM_MATRIX_MLTPLCTN_BCKPRSR_TEST__

class ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test extends ai_core_mvm_base_test;
   // Registration with the factory
  `uvm_component_utils(ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test)
      mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h;
      mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
      mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
      mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
      mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;
      bit prg_wt_set;
  // Class constructor
  function new (string name="ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase

  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");
    uvm_config_db#(uvm_object_wrapper)::set(this, "env.axi_system_env.slave*.sequencer.run_phase", "default_sequence", axi_slave_mem_delay_sequence::type_id::get());
    
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      void'(randomize());

      `uvm_info("MVM_CONCURRENT_PRG_EXE_RANDOM_TEST",$sformatf("ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test starting"), UVM_LOW)
      #100ns;
      ral_write_data = 64'h000_0001;
      configure_prg_reg;
      
      prg_wt_set=1;
      prepare_prg_packet_and_send_ifdw;
      wait_for_prg_status;
      
      
      fork
        // Run concurrent the PRG and EXE
        begin
           prg_wt_set=0;
           prepare_prg_packet_and_send_ifdw;
           wait_for_prg_status;
        end

        begin
          configure_exe_reg;
          prepare_exe_instr;
          prepare_exe_packet_and_send_ifd0;
          wait_for_exe_status;
        end

      join
      
      check_irq_status();

      `uvm_info("MVM_CONCURRENT_PRG_EXE_RANDOM_TEST",$sformatf("ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test end"), UVM_LOW)
    phase.drop_objection(this);
  endtask

  task configure_prg_reg;
    int delay;
      begin
        void'(std::randomize(delay) with { delay inside {[0:300]};});
        #(delay * 10ns);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmprg_regmod.cmdblk_ctrl.update(status);
      end
  endtask

  task configure_exe_reg;
    int delay;
      begin
        void'(std::randomize(delay) with { delay inside {[0:300]};});
        #(delay * 10ns);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.exec_en.set(1'b1);
        mvm_regmodel.m_mvmexe_regmod.cmdblk_ctrl.update(status);
      end
  endtask

  task prepare_prg_packet_and_send_ifdw;
    if (!mvm_prg_cmd_tb_data_h.randomize ()) 
      `uvm_fatal("run_phase", "Failed to randomize");
    uvm_report_info(get_type_name(), $psprintf("mvm_prg_cmd_tb_data_h = \n %s", mvm_prg_cmd_tb_data_h.sprint()), UVM_HIGH);
    if (!axi_wr_seq.randomize() with {
      cfg_addr        == MVM_PRG_CMDB_START_ADDR ;
      sequence_length == 'd1;
      burst_size_enum_t == BURST_SIZE_64BIT;
      burst_type_enum_t == INCR;
      burst_lenght_enum_t == BURST_LENGTH_2;
      cfg_data[0] == 64'h0000_0000_0000_0000;
      cfg_data[1] == mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data;
    })
      `uvm_fatal("run_phase", "Failed to randomize");
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    if(prg_wt_set==1) begin
        mvm_exe_instr_tb_data_h.concurrent_prg_data  =   mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data;
        uvm_report_info(get_type_name(), $psprintf("from 103 line value of concurrent_prg_data  = \n %h", mvm_exe_instr_tb_data_h.concurrent_prg_data), UVM_HIGH);
    end
      fork
         begin
           key.get(1);
           send_ifdw_packet;
           key.put(1);
         end
      join_none
  endtask

  task send_ifdw_packet;
    int ifdw_burst_len = mvm_prg_cmd_tb_data_h.ifdw_burst_len.pop_front();
    randcase
    1: begin
          if (!axi_master_stream_zero_delay_ifdw_base_seq.randomize() with { sequence_length ==  1;
                burst_length ==  ifdw_burst_len;
                })
          `uvm_fatal("run_phase", "Failed to randomize");
          uvm_report_info(get_type_name(), $psprintf("axi_master_stream_zero_delay_ifdw_base_seq = \n %s", axi_master_stream_zero_delay_ifdw_base_seq.sprint()), UVM_HIGH);
          axi_master_stream_zero_delay_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
      end
    1: begin
          if (!axi_master_stream_ifdw_base_seq.randomize() with { sequence_length ==  1;
                burst_length ==  ifdw_burst_len;
                })
          `uvm_fatal("run_phase", "Failed to randomize");
          uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifdw_base_seq = \n %s", axi_master_stream_ifdw_base_seq.sprint()), UVM_HIGH);
          axi_master_stream_ifdw_base_seq.start(env.axi_system_env.master[1].sequencer);
        end
    endcase
  endtask


  task prepare_exe_instr;
     // ==========QCommand packet=====================//mvm_exe_instr_addr.size

    if (($test$plusargs("SHORT_RUN")) ) begin
      if (!mvm_exe_instr_tb_data_packet_h.randomize() with {mvm_exe_instr_addr.size inside {[1:5]};})
         `uvm_fatal("run_phase", "Failed to randomize");
    end
    else begin
      if (!mvm_exe_instr_tb_data_packet_h.randomize() with {mvm_exe_instr_addr.size inside {[6:max_addr_size]};} )
         `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_addr.size = \n %d", mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr.size()), UVM_LOW);
    end

    foreach(mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]) begin
      uvm_report_info(get_type_name(), $psprintf("value of concurrent_prg_data  = \n %h", mvm_exe_instr_tb_data_h.concurrent_prg_data), UVM_HIGH);
      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.a_s == mvm_exe_instr_tb_data_h.concurrent_prg_data[9:8];   
                                                   mvm_exe_instr_struct.a_u_pw >= mvm_exe_instr_tb_data_h.concurrent_prg_data[19:16];
                                                   mvm_exe_instr_struct.wb_u_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[35:32] ;
                                                   mvm_exe_instr_struct.a_u_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[19:16] + mvm_exe_instr_tb_data_h.concurrent_prg_data[35:32] ;
                                                   mvm_exe_instr_struct.a_u_pw + mvm_exe_instr_tb_data_h.mvm_exe_instr_struct.wb_u_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[19:16] + mvm_exe_instr_tb_data_h.concurrent_prg_data[35:32] ;
                                                   mvm_exe_instr_struct.a_t_pw >= mvm_exe_instr_tb_data_h.concurrent_prg_data[26:24];
                                                   mvm_exe_instr_struct.wb_t_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[42:40] ;
                                                   mvm_exe_instr_struct.a_t_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[26:24] +  mvm_exe_instr_tb_data_h.concurrent_prg_data[42:40];
                                                   mvm_exe_instr_struct.a_t_pw + mvm_exe_instr_struct.wb_t_pw <= mvm_exe_instr_tb_data_h.concurrent_prg_data[26:24] + mvm_exe_instr_tb_data_h.concurrent_prg_data[42:40] ;   } )
         `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("after randomisation instruction data = \n %h", mvm_exe_instr_tb_data_h.mvm_exe_instr_data), UVM_HIGH);
      uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_h = \n %s", mvm_exe_instr_tb_data_h.sprint()), UVM_HIGH);
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_data[i] = mvm_exe_instr_tb_data_h.mvm_exe_instr_data;
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_input_size[mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]] = mvm_exe_instr_tb_data_h.mvm_exe_instr_input_size;
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_output_size[mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]] = mvm_exe_instr_tb_data_h.mvm_exe_instr_output_size;
      uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_packet_h = \n %s", mvm_exe_instr_tb_data_packet_h.sprint()), UVM_HIGH);
      //$display("=================================================================");
      //$display($time,"mvm_exe_instr_addr[%0d]=%0h, mvm_exe_instr_input_size[%0d]=%0d",i,mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i],i,mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_input_size[mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]]);
      // ==============================================//
      if (!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_INSTR_START_ADDR + (mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i] * 2);
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_16BIT;
        burst_type_enum_t == FIXED;
        burst_lenght_enum_t == BURST_LENGTH_1;
        cfg_data[0] == mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_data[i];
      })
         `uvm_fatal("run_phase", "Failed to randomize");
        axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
        uvm_report_info(get_type_name(), $psprintf("execution instruction  packet  = \n %s", axi_wr_seq.sprint()), UVM_HIGH);
    end
  endtask

  task prepare_exe_packet_and_send_ifd0;
    // ==========EXE command packet=====================//
    //Create the exe command packet
    for (int j =0; j<mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr.size(); j++) begin
      case (mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[j][1:0])
        0: mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[0].push_back(mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[j]);
        1: mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[1].push_back(mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[j]);
        2: mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[2].push_back(mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[j]);
        3: mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[3].push_back(mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[j]);
      endcase
    end
     for (int weight_set=0;weight_set<WEIGHT_SETS;weight_set++) begin
        mvm_exe_cmd_tb_data_packet_h.len = 1;
        if(mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set].size() > 0) begin // Size ==0
          mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set].sort();
        end
        if(mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set].size == 1) begin //  size ==1
            mvm_exe_cmd_tb_data_packet_h.current_addr = mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set][0];
            mvm_exe_cmd_tb_data_packet_h.ptr = mvm_exe_cmd_tb_data_packet_h.current_addr;
            mvm_exe_cmd_tb_data_packet_h.len = 1;
            if (($test$plusargs("SHORT_RUN")) ) begin
              if (!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                    mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                    mvm_exe_cmd_struct.loop_iter inside {[1:5]};})
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
            else begin
              if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                     mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                    })
                 `uvm_fatal("run_phase", "Failed to randomize");

            end
            mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
            uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s",mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
            configure_exe_cmdb_packet;
            send_ifd0_packet;
        end
        for (int i =0; i<mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set].size()-1; i++ ) begin //  size > 1
            mvm_exe_cmd_tb_data_packet_h.current_addr = mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set][i];
            mvm_exe_cmd_tb_data_packet_h.next_addr = mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set][i+1];
            if( mvm_exe_cmd_tb_data_packet_h.len ==1 && (mvm_exe_cmd_tb_data_packet_h.current_addr + 1) == mvm_exe_cmd_tb_data_packet_h.next_addr ) begin  // present and next equal
              mvm_exe_cmd_tb_data_packet_h.ptr = mvm_exe_cmd_tb_data_packet_h.current_addr;
              mvm_exe_cmd_tb_data_packet_h.len = mvm_exe_cmd_tb_data_packet_h.len +1;
            end
            else if(mvm_exe_cmd_tb_data_packet_h.len ==1 && (mvm_exe_cmd_tb_data_packet_h.current_addr + 1) != mvm_exe_cmd_tb_data_packet_h.next_addr) begin
              mvm_exe_cmd_tb_data_packet_h.ptr = mvm_exe_cmd_tb_data_packet_h.current_addr;
            if (($test$plusargs("SHORT_RUN")) ) begin
              if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                    mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                    mvm_exe_cmd_struct.loop_iter inside {[1:5]};})
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
            else begin
              if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                     mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                    })
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
              mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
              uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s",mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
              configure_exe_cmdb_packet;
              send_ifd0_packet;
            end
            else if( mvm_exe_cmd_tb_data_packet_h.len !=1 && ((mvm_exe_cmd_tb_data_packet_h.current_addr + 1) == mvm_exe_cmd_tb_data_packet_h.next_addr) ) begin  // present and next equal
              mvm_exe_cmd_tb_data_packet_h.len = mvm_exe_cmd_tb_data_packet_h.len +1;
            end
            else if(mvm_exe_cmd_tb_data_packet_h.len !=1 && ((mvm_exe_cmd_tb_data_packet_h.current_addr + 1) != mvm_exe_cmd_tb_data_packet_h.next_addr) ) begin
              if (($test$plusargs("SHORT_RUN")) ) begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                      mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                      mvm_exe_cmd_struct.loop_iter inside {[1:5]};})
                 `uvm_fatal("run_phase", "Failed to randomize");
              end
              else begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                       mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                      })
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
             mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
             uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
             configure_exe_cmdb_packet;
             send_ifd0_packet;
             mvm_exe_cmd_tb_data_packet_h.len =1;
            end
            if (i == mvm_exe_cmd_tb_data_packet_h.mvm_exe_instr_addr_sort[weight_set].size()-2) begin
              if(mvm_exe_cmd_tb_data_packet_h.len ==1) begin
                mvm_exe_cmd_tb_data_packet_h.ptr = mvm_exe_cmd_tb_data_packet_h.next_addr;
              end
              else begin
                mvm_exe_cmd_tb_data_packet_h.ptr = mvm_exe_cmd_tb_data_packet_h.current_addr;
              end
              if (($test$plusargs("SHORT_RUN")) ) begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                      mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                      mvm_exe_cmd_struct.loop_iter inside {[1:5]};})
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
              else begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                       mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                      })
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
              mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
              uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
              configure_exe_cmdb_packet;
              send_ifd0_packet;
            end
        end  // For loop
     end //weight_set
    uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_packet_h = \n %s", mvm_exe_cmd_tb_data_packet_h.sprint()), UVM_HIGH);
      // ==============================================//
  endtask

  task configure_exe_cmdb_packet;
    if ( !((cmd_done_cnt - mvm_if.cmdblk_cmd_done_count ) < CMDBLK_DEPTH )) begin 
          wait ((cmd_done_cnt - mvm_if.cmdblk_cmd_done_count ) < CMDBLK_DEPTH );
    end
    if(!axi_wr_seq.randomize() with {
        cfg_addr        == MVM_EXE_CMDB_START_ADDR;
        sequence_length == 'd1;
        burst_size_enum_t == BURST_SIZE_64BIT;
        burst_type_enum_t == INCR;
        burst_lenght_enum_t == BURST_LENGTH_2;
        cfg_data[0] == 64'h0000_0000_0000_0000;
        cfg_data[1] == (mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
    })
      `uvm_fatal("run_phase", "Failed to randomize");
    axi_wr_seq.start(env.axi_system_env.master[0].sequencer);
    uvm_report_info(get_type_name(), $psprintf("execution command  packet(for loop_len/iter)  = \n %s", axi_wr_seq.sprint()), UVM_HIGH);
    cmd_done_cnt++;
  endtask

  task send_ifd0_packet;
  bit [7:0] ptr;
  bit [7:0] len;
  int total_input_size;
  int ifd0_burst_length;
   fork
      begin
        key.get(1);
        ptr = mvm_exe_cmd_tb_data_h.loop_ptr_q.pop_front();
        len = mvm_exe_cmd_tb_data_h.loop_len_q.pop_front();
        //$display("=================================================================");
        uvm_report_info(get_type_name(), $psprintf("mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
        uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_packet_h = \n %s", mvm_exe_instr_tb_data_packet_h.sprint()), UVM_HIGH);
        //$display("=================================================================");
        for(int i=0;i<len;i++) begin
          total_input_size = total_input_size + mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_input_size[ptr+i];
        end
        ifd0_burst_length = total_input_size * mvm_exe_cmd_tb_data_h.loop_iter_q.pop_front();

        randcase
          1: begin
               if(!axi_master_stream_ifd0_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifd0_base_seq = \n %s", axi_master_stream_ifd0_base_seq.sprint()), UVM_HIGH);

               axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
          end
          1: begin
               if(!axi_master_stream_zero_delay_ifd0_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_zero_delay_ifd0_base_seq = \n %s", axi_master_stream_zero_delay_ifd0_base_seq.sprint()), UVM_HIGH);

               axi_master_stream_zero_delay_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
          end
        endcase
        key.put(1);
      end
   join_none
  endtask

endclass:ai_core_mvm_concurrent_prg_exe_random_matrix_mltplctn_bckprsr_test

`endif	// __AI_CORE_MVM_CONCURRENT_PRG_EXE_RANDOM_MATRIX_MLTPLCTN_BCKPRSR_TEST__
