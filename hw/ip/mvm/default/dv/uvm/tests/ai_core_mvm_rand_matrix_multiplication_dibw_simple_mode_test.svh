// MVM basic test-case class
`ifndef __AI_CORE_MVM_RAND_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_TEST__
`define __AI_CORE_MVM_RAND_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_TEST__

class ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test extends ai_core_mvm_base_test;
  // Registration with the factory
  `uvm_component_utils(ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test)
   mvm_prg_cmd_tb_data mvm_prg_cmd_tb_data_h, mvm_prg_cmd_tb_data_dibw_prsrv ;
   mvm_exe_instr_tb_data mvm_exe_instr_tb_data_h;
   mvm_exe_instr_tb_data_packet mvm_exe_instr_tb_data_packet_h;
   mvm_exe_cmd_tb_data mvm_exe_cmd_tb_data_h;
   mvm_exe_cmd_tb_data_packet mvm_exe_cmd_tb_data_packet_h;

   bit ifdw;
   int ifdw_burst_len;
  // Class constructor
  function new (string name="ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new
  // Build phase
  virtual function void build_phase(uvm_phase phase);
    `uvm_info ("ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test", "Build phase entered", UVM_HIGH)
    super.build_phase(phase);
    mvm_prg_cmd_tb_data_h= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_h");
    mvm_prg_cmd_tb_data_dibw_prsrv= mvm_prg_cmd_tb_data::type_id::create("mvm_prg_cmd_tb_data_dibw_prsrv");
    mvm_exe_instr_tb_data_h = mvm_exe_instr_tb_data::type_id::create("mvm_exe_instr_tb_data_h");
    mvm_exe_instr_tb_data_packet_h = mvm_exe_instr_tb_data_packet::type_id::create("mvm_exe_instr_tb_data_packet_h");
    mvm_exe_cmd_tb_data_h= mvm_exe_cmd_tb_data::type_id::create("mvm_exe_cmd_tb_data_h");
    mvm_exe_cmd_tb_data_packet_h= mvm_exe_cmd_tb_data_packet::type_id::create("mvm_exe_cmd_tb_data_packet_h");

  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    super.run_phase(phase);
      void'(randomize());
      `uvm_info("MVM_RAND_TEST",$sformatf("MVM rand matrix multiplication starting"), UVM_LOW)
     #100ns;

      ral_write_data = 64'h000_0001;
      ral_read_data   = 64'h000_0000;  
  
      configure_prg_reg;
      configure_exe_reg;
      
      ifdw=0;
      prepare_prg_packet_and_send_ifdw;
      wait_for_prg_status;
      uvm_report_info(get_type_name(), $psprintf("IFDW0 first PRG STATUS READ FINISHED "), UVM_LOW);
      
      ifdw=1;
      prepare_prg_packet_and_send_ifdw;
      wait_for_prg_status;
      uvm_report_info(get_type_name(), $psprintf("IFDW2 second PRG STATUS READ Done"), UVM_LOW);
      prepare_exe_instr;

      prepare_exe_packet_and_send_ifd0_2;
      wait_for_exe_status;
      
      check_irq_status();

      `uvm_info("MVM_RANDOM_TEST",$sformatf("MVM random matrix multiplication end"), UVM_HIGH)
    phase.drop_objection(this);
  endtask

     
task prepare_prg_packet_and_send_ifdw;
    if(ifdw==0) begin 
      if (!mvm_prg_cmd_tb_data_h.randomize with {mvm_prg_cmd_struct.a_t_pw < 4; 
                                                 mvm_prg_cmd_struct.a_t_pw + mvm_prg_cmd_struct.wb_t_pw < 4;
                                                }) 
        `uvm_fatal("run_phase", "Failed to randomize");
      mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct = mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct;
    end
    else begin mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.a_t_pw = mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.a_t_pw + 4;
               mvm_prg_cmd_tb_data_h.mvm_prg_cmd_data = {mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.wb_t_pw, mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.wb_u_pw,
                                                         mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.a_t_pw, mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.a_u_pw,
                                                         mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.a_s, mvm_prg_cmd_tb_data_h.mvm_prg_cmd_struct.extra};
    end

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
      fork
         begin
           key.get(1);
           send_ifdw_packet;
           key.put(1);
         end
      join_none
  endtask

  task send_ifdw_packet;
    if(ifdw==0) begin 
      ifdw_burst_len = mvm_prg_cmd_tb_data_h.ifdw_burst_len.pop_front();
    end
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
      if (!mvm_exe_instr_tb_data_h.randomize with {mvm_exe_instr_struct.a_s == mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_s[1:0];   
                                                   mvm_exe_instr_struct.a_u_pw >= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_u_pw[3:0];
                                                   mvm_exe_instr_struct.wb_u_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_u_pw[3:0] ;
                                                   mvm_exe_instr_struct.a_u_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_u_pw[3:0] + mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_u_pw[3:0] ;
                                                   mvm_exe_instr_struct.a_u_pw + mvm_exe_instr_struct.wb_u_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_u_pw[3:0] + mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_u_pw[3:0] ;
                                                   mvm_exe_instr_struct.a_t_pw >= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_t_pw[2:0];
                                                   mvm_exe_instr_struct.wb_t_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_t_pw[2:0] ;
                                                   mvm_exe_instr_struct.a_t_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_t_pw[2:0] + mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_t_pw[2:0] ;
                                                   mvm_exe_instr_struct.a_t_pw + mvm_exe_instr_struct.wb_t_pw <= mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.a_t_pw[2:0] + mvm_prg_cmd_tb_data_dibw_prsrv.mvm_prg_cmd_struct.wb_t_pw[2:0] ;       } )
         `uvm_fatal("run_phase", "Failed to randomize");
      uvm_report_info(get_type_name(), $psprintf("after randomisation instruction data = \n %h", mvm_exe_instr_tb_data_h.mvm_exe_instr_data), UVM_MEDIUM);
      uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_h = \n %s", mvm_exe_instr_tb_data_h.sprint()), UVM_HIGH);
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_data[i] = mvm_exe_instr_tb_data_h.mvm_exe_instr_data;
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_input_size[mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]] = mvm_exe_instr_tb_data_h.mvm_exe_instr_input_size;
      mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_output_size[mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_addr[i]] = mvm_exe_instr_tb_data_h.mvm_exe_instr_output_size;
      uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_packet_h = \n %s", mvm_exe_instr_tb_data_packet_h.sprint()), UVM_HIGH);
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
        uvm_report_info(get_type_name(), $psprintf("execution instruction  packet  = \n %s", axi_wr_seq.sprint()), UVM_MEDIUM);
    end
  endtask

  task prepare_exe_packet_and_send_ifd0_2;
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
                                                           mvm_exe_cmd_struct.loop_iter inside {[1:5]};
							                               mvm_exe_cmd_struct.extra == 1 ; }) //enabling dibw mode
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
            else begin
              if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                          mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
							                              mvm_exe_cmd_struct.extra == 1; //enabling dibw mode
                                                    })
                 `uvm_fatal("run_phase", "Failed to randomize");

            end
            mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
            uvm_report_info(get_type_name(), $psprintf("from line 207 -> mvm_exe_cmd_tb_data_h = \n %s",mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
            configure_exe_cmdb_packet;
            send_ifd0_ifd2_packet;
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
                                                    mvm_exe_cmd_struct.loop_iter inside {[1:5]};
							                        mvm_exe_cmd_struct.extra == 1; }) //enabling dibw mode
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
            else begin
              if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                     mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
							                         mvm_exe_cmd_struct.extra == 1; //enabling dibw mode
                                                    })
                 `uvm_fatal("run_phase", "Failed to randomize");
            end
              mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
              uvm_report_info(get_type_name(), $psprintf("from line 235 ->mvm_exe_cmd_tb_data_h = \n %s",mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
              configure_exe_cmdb_packet;
              send_ifd0_ifd2_packet;
            end
            else if( mvm_exe_cmd_tb_data_packet_h.len !=1 && ((mvm_exe_cmd_tb_data_packet_h.current_addr + 1) == mvm_exe_cmd_tb_data_packet_h.next_addr) ) begin  // present and next equal
              mvm_exe_cmd_tb_data_packet_h.len = mvm_exe_cmd_tb_data_packet_h.len +1;
            end
            else if(mvm_exe_cmd_tb_data_packet_h.len !=1 && ((mvm_exe_cmd_tb_data_packet_h.current_addr + 1) != mvm_exe_cmd_tb_data_packet_h.next_addr) ) begin
              if (($test$plusargs("SHORT_RUN")) ) begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                      mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                      mvm_exe_cmd_struct.loop_iter inside {[1:5]};
							                          mvm_exe_cmd_struct.extra == 1; }) //enabling dibw mode
                 `uvm_fatal("run_phase", "Failed to randomize");
              end
              else begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                       mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                       mvm_exe_cmd_struct.extra == 1; //enabling dibw mode 
                                                      })
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
             mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
             uvm_report_info(get_type_name(), $psprintf("from line 258 -> mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
             configure_exe_cmdb_packet;
             send_ifd0_ifd2_packet;
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
                                                      mvm_exe_cmd_struct.loop_iter inside {[1:5]};
                                                       mvm_exe_cmd_struct.extra == 1; //enabling dibw mode
                                                      })
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
              else begin
                if(!mvm_exe_cmd_tb_data_h.randomize() with {mvm_exe_cmd_struct.loop_len == mvm_exe_cmd_tb_data_packet_h.len;
                                                       mvm_exe_cmd_struct.loop_ptr ==  mvm_exe_cmd_tb_data_packet_h.ptr;
                                                       mvm_exe_cmd_struct.extra == 1; //enabling dibw mode
                                                      })
                  `uvm_fatal("run_phase", "Failed to randomize");
              end
              mvm_exe_cmd_tb_data_packet_h.mvm_exe_cmd_data.push_back(mvm_exe_cmd_tb_data_h.mvm_exe_cmd_data);
              uvm_report_info(get_type_name(), $psprintf("from line 283 -> mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
              configure_exe_cmdb_packet;
              send_ifd0_ifd2_packet;
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
    uvm_report_info(get_type_name(), $psprintf("execution command  packet(for loop_len/iter)  = \n %s", axi_wr_seq.sprint()), UVM_MEDIUM);
    cmd_done_cnt++;
  endtask

  task send_ifd0_ifd2_packet;
  bit [7:0] ptr;
  bit [7:0] len;
  int total_input_size;
  int ifd0_2_burst_length;
   fork
      begin
        key.get(1);
        ptr = mvm_exe_cmd_tb_data_h.loop_ptr_q.pop_front();
        len = mvm_exe_cmd_tb_data_h.loop_len_q.pop_front();
        //$display("=================================================================");
        uvm_report_info(get_type_name(), $psprintf("from line 323 -> mvm_exe_cmd_tb_data_h = \n %s", mvm_exe_cmd_tb_data_h.sprint()), UVM_HIGH);
        uvm_report_info(get_type_name(), $psprintf("mvm_exe_instr_tb_data_packet_h = \n %s", mvm_exe_instr_tb_data_packet_h.sprint()), UVM_HIGH);
        //$display("=================================================================");
        for(int i=0;i<len;i++) begin
          total_input_size = total_input_size + mvm_exe_instr_tb_data_packet_h.mvm_exe_instr_input_size[ptr+i];
        end
        ifd0_2_burst_length = total_input_size * mvm_exe_cmd_tb_data_h.loop_iter_q.pop_front();

        randcase
          1: begin
               if(!axi_master_stream_ifd0_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_2_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifd0_base_seq = \n %s", axi_master_stream_ifd0_base_seq.sprint()), UVM_HIGH);

               if(!axi_master_stream_ifd2_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_2_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_ifd2_base_seq = \n %s", axi_master_stream_ifd2_base_seq.sprint()), UVM_HIGH);


               fork : run_ifd0_ifd2_seq 
                 axi_master_stream_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
                 axi_master_stream_ifd2_base_seq.start(env.axi_system_env.master[3].sequencer);
               join : run_ifd0_ifd2_seq
          end
          1: begin
               if(!axi_master_stream_zero_delay_ifd0_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_2_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_zero_delay_ifd0_base_seq = \n %s", axi_master_stream_zero_delay_ifd0_base_seq.sprint()), UVM_HIGH);
               
               if(!axi_master_stream_zero_delay_ifd2_base_seq.randomize() with {
                 sequence_length == 1;
                 burst_length == ifd0_2_burst_length;
               })
                 `uvm_fatal("run_phase", "Failed to randomize");
               uvm_report_info(get_type_name(), $psprintf("axi_master_stream_zero_delay_ifd2_base_seq = \n %s", axi_master_stream_zero_delay_ifd2_base_seq.sprint()), UVM_HIGH);
               
               fork : run_ifd0_ifd2_zero_delay_seq 
                 axi_master_stream_zero_delay_ifd0_base_seq.start(env.axi_system_env.master[2].sequencer);
                 axi_master_stream_zero_delay_ifd2_base_seq.start(env.axi_system_env.master[3].sequencer);
               join : run_ifd0_ifd2_zero_delay_seq
          end
        endcase
        key.put(1);
      end
   join_none
  endtask

endclass:ai_core_mvm_rand_matrix_multiplication_dibw_simple_mode_test

`endif	// __AI_CORE_MVM_RAND_MATRIX_MULTIPLICATION_DIBW_SIMPLE_MODE_TEST__
