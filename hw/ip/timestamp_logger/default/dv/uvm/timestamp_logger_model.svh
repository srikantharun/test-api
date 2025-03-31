// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_MODEL_SVH
`define GUARD_TIMESTAMP_LOGGER_MODEL_SVH

`uvm_analysis_imp_decl (_timestamp_logger_cfg_item)
`uvm_analysis_imp_decl (_timestamp_logger_event_item)

class  timestamp_logger_model extends uvm_component;
    timestamp_logger_env_cfg         m_env_cfg;
    timestamp_logger_cfg_item        cfg;

    logic [15:0]                     entry_count = 0;
    logic [63:0]                     internal[logic[63:0]];
    logic [63:0]                     external[logic[63:0]];

    uvm_analysis_imp_timestamp_logger_cfg_item   #(timestamp_logger_cfg_item,   timestamp_logger_model) analysis_imp_cfg;
    uvm_analysis_imp_timestamp_logger_event_item #(timestamp_logger_event_item, timestamp_logger_model) analysis_imp_event;

    int unsigned group_en_bit_idx;
    bit          group_en_bit_value;

    // Covergroups
    covergroup cg;
        option.per_instance = 1'b1;
        option.name         = "cg";

        cp_trace_mode                : coverpoint cfg.trace_mode;
        cp_external_mode             : coverpoint cfg.external_mode;
        cp_cntr_division             : coverpoint cfg.cntr_division;
        cp_sync_ctrl                 : coverpoint cfg.sync_ctrl;
        cp_st_addr                   : coverpoint cfg.st_addr {
            bins s[]  = {0, 8, 16};
            bins m    = {[17:`MEM_DEPTH-17]};
            bins l[]  = {`MEM_DEPTH-16, `MEM_DEPTH-8};
        }
        cp_log_size                  : coverpoint cfg.log_size {
            bins s[]  = {8, 16, 24};
            bins m    = {[25:`MEM_DEPTH-17]};
            bins l[]  = {`MEM_DEPTH-16, `MEM_DEPTH-8, `MEM_DEPTH};
        }
        cp_burst_size                : coverpoint cfg.burst_size iff (cfg.external_mode);

        cp_n_transactions            : coverpoint cfg.n_transactions {
            bins s[] = {0, 1, 3};
            bins m   = {[4:100]};
            bins l   = {[101:$]};
        }
        cp_wrap                      : coverpoint (cfg.n_transactions > (cfg.log_size / 8));
        cp_entry_count               : coverpoint entry_count {
            bins s[] = {0, 1, 3};
            bins m   = {[4:100]};
            bins l   = {[101:$]};
        }
        cc_trace_mode_X_external_mode    : cross cp_trace_mode, cp_external_mode;
        cc_trace_mode_X_cntr_division    : cross cp_trace_mode, cp_cntr_division;
        cc_external_mode_X_cntr_division : cross cp_external_mode, cp_cntr_division;
        cc_st_addr_X_log_size            : cross cp_st_addr, cp_log_size;
        cc_trace_mode_X_wrap             : cross cp_trace_mode, cp_wrap;

        cp_burst_size_0_n_transactions   : coverpoint cfg.n_transactions[0]   iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b000)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_1_n_transactions   : coverpoint cfg.n_transactions[1:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b001)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_2_n_transactions   : coverpoint cfg.n_transactions[2:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b010)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_3_n_transactions   : coverpoint cfg.n_transactions[3:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b011)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_4_n_transactions   : coverpoint cfg.n_transactions[4:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b100)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_5_n_transactions   : coverpoint cfg.n_transactions[5:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b101)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_6_n_transactions   : coverpoint cfg.n_transactions[6:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b110)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

        cp_burst_size_7_n_transactions   : coverpoint cfg.n_transactions[7:0] iff ((cfg.external_mode == 1'b1) && (cfg.burst_size == 3'b111)) {
            bins zero   = {0};
            bins others = {[1:$]};
        }

    endgroup : cg

    covergroup cg_group_en;
        option.per_instance = 1'b1;
        option.name         = "cg_group_en";

        cp_group_en_bit_idx   : coverpoint group_en_bit_idx {
           bins n[] = {[0:`NUM_GROUPS-1]};
        }
        cp_group_en_bit_value : coverpoint group_en_bit_value;

        cc_group_en           : cross cp_group_en_bit_idx, cp_group_en_bit_value;

    endgroup : cg_group_en

    `uvm_component_utils_begin(timestamp_logger_model)
        `uvm_field_int(entry_count,     UVM_DEFAULT)
        `uvm_field_aa_int_int(internal, UVM_DEFAULT)
        `uvm_field_aa_int_int(external, UVM_DEFAULT)
    `uvm_component_utils_end

    function  new(string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_cfg   = new("analysis_imp_cfg",   this);
        analysis_imp_event = new("analysis_imp_event", this);

        // Coverage
        cg          = new();
        cg_group_en = new();

    endfunction : new

    function void build_phase(uvm_phase phase);
        assert(uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
    endfunction: build_phase

    function void write_timestamp_logger_cfg_item(timestamp_logger_cfg_item t);
        if(t.capture_enable) begin
            `uvm_info("timestamp_logger", $sformatf("write:\n%s", t.sprint()), UVM_NONE);
            entry_count = 0;
        end
        else begin
            // Coverage
            cg.sample();

            for (group_en_bit_idx = 0; group_en_bit_idx < `NUM_GROUPS; group_en_bit_idx++) begin
                group_en_bit_value = cfg.group_en[group_en_bit_idx];
                cg_group_en.sample();
            end
        end
        cfg = t;
    endfunction : write_timestamp_logger_cfg_item

    function void write_timestamp_logger_event_item(timestamp_logger_event_item t);
        logic [15:0] entry_count_offset;

       `uvm_info("timestamp_logger", $sformatf("write:\n%s", t.sprint()), UVM_DEBUG);
        if (cfg.capture_enable && |t.triggers) begin
            for (int i = 0; i < m_env_cfg.n_groups; i++) begin
                if (t.triggers[i] && cfg.group_en[i]) begin
                    logic [63:0] entry;
                    logic [63:0] msg_mask;

                    // Discard
                    if ((cfg.trace_mode == 1'b0) && (entry_count == cfg.log_size/8))
                        continue;

                    // Wrap
                    entry_count_offset = entry_count % (cfg.log_size/8);

                    msg_mask = (1 << m_env_cfg.group_msg_width[i])-1;
                    entry    = (t.msgs[i] & msg_mask)  << 0;
                    entry   |= i                       << 24;
                    entry   |= t.timestamp             << 32;

                    if (cfg.external_mode == 1'b0) begin
                        internal[cfg.st_addr + entry_count_offset] = entry;
                        `uvm_info(get_full_name(), $psprintf("internal[0x%x] -> 0x%x", cfg.st_addr + entry_count_offset, entry), UVM_DEBUG)
                    end
                    else begin
                        external[cfg.st_addr + entry_count_offset] = entry;
                        `uvm_info(get_full_name(), $psprintf("external[0x%x] -> 0x%x", cfg.st_addr + entry_count_offset, entry), UVM_DEBUG)
                    end
                    entry_count++;
                end
            end
        end
    endfunction : write_timestamp_logger_event_item

    function logic [63:0] get_entry_count();
        if (cfg.trace_mode == 1'b0)
            return get_log_size();
        else
            return entry_count;
    endfunction: get_entry_count

    function logic [63:0] get_log_size();
        if (entry_count > cfg.log_size/8)
            return cfg.log_size/8;
        else
            return entry_count;
    endfunction: get_log_size

    function logic [63:0] get_entry(int i);
        logic[63:0] addr;
        addr  = cfg.st_addr;
        addr +=  i % (cfg.log_size/8);

        if (cfg.external_mode == 1'b0) begin
            if (internal.exists(addr))
                return internal[addr];
            else
                return 64'bx;
        end
        else begin
            if (external.exists(addr))
                return external[addr];
            else
                return 64'bx;
        end

    endfunction: get_entry

endclass : timestamp_logger_model

`endif // GUARD_TIMESTAMP_LOGGER_MODEL_SVH
