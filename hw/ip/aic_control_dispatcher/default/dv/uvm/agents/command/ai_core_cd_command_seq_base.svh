// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: gbratu

`ifndef GUARD_AI_CORE_CD_COMMAND_SEQ_BASE_SVH
`define GUARD_AI_CORE_CD_COMMAND_SEQ_BASE_SVH

class ai_core_cd_command_seq_base extends uvm_sequence #(ai_core_cd_command);

    //ai_core_dp_cmd_gen_cmdb_agent         m_cmdb_agent;
    svt_axi_system_env                    p_axi_system_env;
    axi_master_write_random_sequence      axi_seq;

    `uvm_object_utils(ai_core_cd_command_seq_base)

    function new(string name = "");
        super.new(name);
    endfunction : new

    //task pre_start();
    //    uvm_phase phase = get_starting_phase();
    //    if (phase != null)
    //        phase.raise_objection(this);
    //endtask : pre_start

    //task post_start();
    //    uvm_phase phase = get_starting_phase();
    //    if (phase != null)
    //        phase.drop_objection(this);
    //endtask : post_start

    task body();
        //ai_core_dp_cmd_gen_cmdb_sqr _sqr;
        //assert($cast(_sqr, m_sequencer));

        //`uvm_info(get_type_name(), $psprintf("Body %0d programs, %0d transactions (0x%x-0x%x)", _sqr.m_env_cfg.n_programs, _sqr.m_env_cfg.n_transactions, this.m_cmdb_agent.m_mem_range.base, this.m_cmdb_agent.m_mem_range.top), UVM_LOW)
    

        axi_seq  = axi_master_write_random_sequence::type_id::create("axi_seq");
        assert(axi_seq.randomize() with {
                                            //sequence_length      == (req.length);
                                            sequence_length      == 1; //1 command  (toDO: create command list to send burst of commands )
                                            //cfg_addr             == (req.task_list_ptr);
                                            cfg_addr             == ACD_CMD_ST_ADDR;
                                            burst_size           == svt_axi_transaction::BURST_SIZE_64BIT;
                                            burst_type           == svt_axi_transaction::FIXED;
                                            burst_length         == 1;
                                            max_bw               == 8;
                                            min_addr_valid_delay == 0;
                                            max_addr_valid_delay == 16;
                                            min_bready_delay     == 0;
                                            max_bready_delay     == 16;
                                            foreach(cfg_data[j]) { cfg_data[j] == 0 }
        });
        axi_seq.print();
        axi_seq.start(p_axi_system_env.master[0].sequencer);

    endtask : body


endclass : ai_core_cd_command_seq_base

`endif // GUARD_AI_CORE_CD_COMMAND_SEQ_BASE_SVH
