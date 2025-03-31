// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_ENV_CFG_SVH
`define GUARD_NOC_MEM_ENV_CFG_SVH

class noc_mem_env_cfg extends uvm_object;
    rand int unsigned  n_transactions    = 0;
    rand int unsigned  n_partitions      = 0;

    constraint c_n_transactions { soft n_transactions == 64*1024; }
    constraint c_n_partitions   { soft n_partitions   == 1; }

    `uvm_object_utils_begin(noc_mem_env_cfg)
        `uvm_field_int(n_transactions, UVM_DEFAULT)
        `uvm_field_int(n_partitions,   UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="noc_mem_env_cfg");
        super.new (name);
    endfunction:new

endclass : noc_mem_env_cfg

`endif // GUARD_NOC_MEM_ENV_CFG_SVH
