// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_ENV_CFG_SVH
`define GUARD_TIMESTAMP_LOGGER_ENV_CFG_SVH

// IAU_DPU memory module environment configuration class
class timestamp_logger_env_cfg extends uvm_object;

         int unsigned  n_groups                         = `NUM_GROUPS;
         int unsigned  mem_depth                        = `MEM_DEPTH;
         int unsigned  csr_base                         = `CSR_ST_ADDR;
         int unsigned  csr_top                          = `CSR_END_ADDR;
         int unsigned  mem_base                         = `MEM_ST_ADDR;
         int unsigned  mem_top                          = `MEM_END_ADDR;
         int unsigned  group_msg_width[`NUM_GROUPS]     = `GROUP_MSG_WIDTH;
         int unsigned  fifo_depth                       = `TIMESTAMP_FIFO_DEPTH;
    rand int unsigned  n_programs                       = 0;
    rand int unsigned  cfg_id                           = 0;
    rand int unsigned  random_cfg_read_rate             = 0;
    rand bit           rate_limit                       = 1'b0;

    constraint c_n_programs           { soft n_programs               == 1;         }
    constraint c_cfg_id               { soft cfg_id               inside {[0:15]};  }
    constraint c_random_cfg_read_rate {      random_cfg_read_rate inside {[0:100]}; }
    constraint c_rate_limit           { soft rate_limit               == 1'b0;      }

    `uvm_object_utils_begin(timestamp_logger_env_cfg)
        `uvm_field_int(n_programs,               UVM_DEFAULT)
        `uvm_field_int(cfg_id,                   UVM_DEFAULT)
        `uvm_field_int(mem_depth,                UVM_DEFAULT)
        `uvm_field_int(csr_base,                 UVM_DEFAULT)
        `uvm_field_int(csr_top,                  UVM_DEFAULT)
        `uvm_field_int(mem_base,                 UVM_DEFAULT)
        `uvm_field_int(mem_top,                  UVM_DEFAULT)
        `uvm_field_sarray_int(group_msg_width,   UVM_DEFAULT)
        `uvm_field_int(fifo_depth,               UVM_DEFAULT)
        `uvm_field_int(random_cfg_read_rate,     UVM_DEFAULT)
        `uvm_field_int(rate_limit,               UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="timestamp_logger_env_cfg");
        super.new (name);
    endfunction:new

endclass : timestamp_logger_env_cfg

`endif // GUARD_TIMESTAMP_LOGGER_ENV_CFG_SVH
