// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_MODEL_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_MODEL_SVH

class _loop_ extends uvm_object;

    aic_dp_cmd_gen_pkg::loop_index_t     main_index    = 0;
    aic_dp_cmd_gen_pkg::loop_pointer_t   first         = 0;
    aic_dp_cmd_gen_pkg::loop_pointer_t   last          = 0;
    aic_dp_cmd_gen_pkg::loop_iteration_t iterations    = 0;
    aic_dp_cmd_gen_pkg::loop_iteration_t count         = 0;
    aic_dp_cmd_gen_pkg::loop_iteration_t next_count    = 0;
    _loop_                               main          = null;
    _loop_                               parent        = null;
    _loop_                               sibling       = null;
    _loop_                               children[$];

    `uvm_object_utils_begin(_loop_)
        `uvm_field_int(main_index,   UVM_DEFAULT)
        `uvm_field_int(first,        UVM_DEFAULT)
        `uvm_field_int(last,         UVM_DEFAULT)
        `uvm_field_int(iterations,   UVM_DEFAULT)
        `uvm_field_int(count,        UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="_loop_", _loop_ parent=null);
        super.new (name);

        if (parent !=null) begin
            this.parent= parent;
            parent.children.push_back(this);
            main_index = parent.main_index;

            if  (parent.parent == null)
                this.main = parent;
            else
                this.main = parent.parent;
        end
        else begin
            this.main = this;
        end
    endfunction:new

    function aic_dp_cmd_gen_pkg::loop_index_t get_main_index();
        return main.main_index;
    endfunction : get_main_index

    function bit get_overall_last();
        bit    retVal = 1'b1;
        _loop_ loop   = this;


        while((loop != null) && (retVal == 1'b1)) begin
            retVal &= (loop.count   == loop.iterations - 1);
            retVal &= (loop.sibling == null);
            loop    = loop.parent;
        end
        return retVal;
    endfunction

    function void step(input  aic_dp_cmd_gen_pkg::loop_pointer_t ptr,
                       output bit                                command_valid,
                       output aic_dp_cmd_gen_pkg::loop_pointer_t next_ptr,
                       output _loop_                             loop,
                       output bit                                done);
        command_valid = 1'b1;
        loop          = this;
        next_ptr      = ptr + 1;

        // Decend into children
        foreach(children[i]) begin
            if (ptr == children[i].first) begin
                command_valid   = 1'b0;
                loop            = children[i];
                next_ptr        = children[i].first;
                return;
            end
        end

        // Ascend through parents
        while(1) begin
            if (ptr == loop.last) begin
                loop.next_count = loop.count + 1;

                if (loop.next_count == loop.iterations) begin
                    loop.next_count = 0;
                    if (loop.parent == null) begin
                        if (loop.sibling == null) begin
                            done = 1'b1;
                            break;
                        end
                        else begin
                            loop     = loop.sibling;
                            next_ptr = loop.first;
                            break;
                        end
                    end
                    else begin
                        loop = loop.parent;
                    end
                end
                else begin
                    next_ptr = loop.first;
                    break;
                end
            end
            else begin
                break;
            end
        end
    endfunction : step

endclass : _loop_

class ai_core_dp_cmd_gen_model#(type dp_command_t) extends uvm_subscriber #(ai_core_dp_cmd_gen_cmdb);

    uvm_analysis_port #(ai_core_dp_cmd_gen_cmdb) cmdb_ap;

    uvm_analysis_port #(ai_core_dp_cmd_gen_command#(dp_command_t)) command_ap;

    `uvm_component_param_utils(ai_core_dp_cmd_gen_model#(dp_command_t))


    function new(string name, uvm_component parent);
        super.new(name, parent);
        cmdb_ap  = new("cmdb_ap",  this);
        command_ap = new("command_ap", this);

    endfunction : new

    function void write(input ai_core_dp_cmd_gen_cmdb t);
        process_cmdb(t);
    endfunction : write

    function void process_cmdb(ai_core_dp_cmd_gen_cmdb t);

        aic_dp_cmd_gen_pkg::loop_pointer_t ptr, next_ptr;
        _loop_                             loop, next_loop;
        _loop_                             main_loop_0   = null;
        _loop_                             main_loop_1   = null;
        _loop_                             main_loop_2   = null;
        _loop_                             nested_loop_0 = null;
        _loop_                             nested_loop_1 = null;

        bit                                command_valid, last;

        if (!t.valid)
            return;

        // Send the updated cmdb to the socreboard
        begin
           ai_core_dp_cmd_gen_cmdb cmdb;
           assert($cast(cmdb, t.clone()));
           cmdb.set_name("from_model");
           cmdb_ap.write(cmdb);
        end

        // Errors have no commands
        if (t.errors != '0)
            return;

        // Create the loop
        if (t.format == aic_dp_cmd_gen_pkg::Bypass) begin
            ai_core_dp_cmd_gen_command#(dp_command_t) command = new("from_model");

            command.data         = '0;
            command.format       = t.format;
            command.extra        = t.extra;
            command.last         = 1'b1;
            command.overall_last = 1'b1;
            command.main_index   = '0;
            command.main         = '0;
            command.nested_0     = '0;
            command.nested_1     = '0;
            command_ap.write(command);
            return;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM1N0) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM1N1) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            nested_loop_0             = new("nested_0", main_loop_0);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM1N2) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            nested_loop_0             = new("nested_0", main_loop_0);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;

            nested_loop_1             = new("nested_1", t.is_parallel() ? main_loop_0 : nested_loop_0);
            nested_loop_1.first       = t.nested_1.start;
            nested_loop_1.last        = t.nested_1.start + t.nested_1.length - 1;
            nested_loop_1.iterations  = t.nested_1.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM2N0) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_0.sibling       = main_loop_1;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM2N1) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_0.sibling       = main_loop_1;

            nested_loop_0             = new("nested_0", (t.nested_0_map_main == 0) ? main_loop_0 : main_loop_1);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM2N2) begin
            main_loop_0               = new("main_0", null);
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_0.sibling       = main_loop_1;

            nested_loop_0             = new("nested_0", (t.nested_0_map_main == 0) ? main_loop_0 : main_loop_1);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;

            nested_loop_1             = new("nested_1", (t.co_nested() && !t.is_parallel()) ? nested_loop_0 : (t.nested_1_map_main == 0) ? main_loop_0 : main_loop_1);
            nested_loop_1.first       = t.nested_1.start;
            nested_loop_1.last        = t.nested_1.start + t.nested_1.length - 1;
            nested_loop_1.iterations  = t.nested_1.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM3N0) begin
            main_loop_0               = new("main_0");
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_1.main          = main_loop_1;
            main_loop_0.sibling       = main_loop_1;

            main_loop_2               = new("main_2", null);
            main_loop_2.main_index    = 2;
            main_loop_2.first         = t.main_2.start;
            main_loop_2.last          = t.main_2.start + t.main_2.length - 1;
            main_loop_2.iterations    = t.main_2.iteration;
            main_loop_2.main          = main_loop_2;
            main_loop_1.sibling       = main_loop_2;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM3N1) begin
            main_loop_0               = new("main_0");
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_1.main          = main_loop_1;
            main_loop_0.sibling       = main_loop_1;

            main_loop_2               = new("main_2", null);
            main_loop_2.main_index    = 2;
            main_loop_2.first         = t.main_2.start;
            main_loop_2.last          = t.main_2.start + t.main_2.length - 1;
            main_loop_2.iterations    = t.main_2.iteration;
            main_loop_2.main          = main_loop_2;
            main_loop_1.sibling       = main_loop_2;

            nested_loop_0             = new("nested_0", (t.nested_0_map_main == 0) ? main_loop_0 : (t.nested_0_map_main == 1) ? main_loop_1 : main_loop_2);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;
        end
        else if (t.format == aic_dp_cmd_gen_pkg::LoopsM3N2) begin
            main_loop_0               = new("main_0");
            main_loop_0.main_index    = 0;
            main_loop_0.first         = t.main_0.start;
            main_loop_0.last          = t.main_0.start + t.main_0.length - 1;
            main_loop_0.iterations    = t.main_0.iteration;

            main_loop_1               = new("main_1", null);
            main_loop_1.main_index    = 1;
            main_loop_1.first         = t.main_1.start;
            main_loop_1.last          = t.main_1.start + t.main_1.length - 1;
            main_loop_1.iterations    = t.main_1.iteration;
            main_loop_1.main          = main_loop_1;
            main_loop_0.sibling       = main_loop_1;

            main_loop_2               = new("main_2", null);
            main_loop_2.main_index    = 2;
            main_loop_2.first         = t.main_2.start;
            main_loop_2.last          = t.main_2.start + t.main_2.length - 1;
            main_loop_2.iterations    = t.main_2.iteration;
            main_loop_2.main          = main_loop_2;
            main_loop_1.sibling       = main_loop_2;

            nested_loop_0             = new("nested_0", (t.nested_0_map_main == 0) ? main_loop_0 : (t.nested_0_map_main == 1) ? main_loop_1 : main_loop_2);
            nested_loop_0.first       = t.nested_0.start;
            nested_loop_0.last        = t.nested_0.start + t.nested_0.length - 1;
            nested_loop_0.iterations  = t.nested_0.iteration;

            nested_loop_1             = new("nested_1", (t.co_nested() && !t.is_parallel()) ? nested_loop_0 : (t.nested_1_map_main == 0) ? main_loop_0 : (t.nested_1_map_main == 1) ? main_loop_1 : main_loop_2);
            nested_loop_1.first       = t.nested_1.start;
            nested_loop_1.last        = t.nested_1.start + t.nested_1.length - 1;
            nested_loop_1.iterations  = t.nested_1.iteration;
        end
        else begin
            `uvm_fatal(get_name(), $psprintf("Unknown CMDB Format:\n%s", t.sprint()));
        end

        loop         = main_loop_0;
        ptr          = t.main_0.start;
        last         = 1'b0;

        while(!last) begin
            loop.step(ptr, command_valid, next_ptr, next_loop, last);

            // Create the command Item
            if (command_valid)
            begin
                ai_core_dp_cmd_gen_command#(dp_command_t) command = new("from_model");

                command.data         = dp_command_t'(ptr); // TODO
                command.format       = t.format;
                command.extra        = t.extra;
                command.last         = last;
                command.overall_last = loop.get_overall_last();;
                command.main_index   = loop.get_main_index();

                command.main         = loop.main.count;
                command.nested_0     = (nested_loop_0 == null) ? '0 : nested_loop_0.count;
                command.nested_1     = (nested_loop_1 == null) ? '0 : nested_loop_1.count;
                command_ap.write(command);
            end
            //`uvm_info(get_name(), $psprintf("%0d loop=%s-%s ptr=0x%x-0x%x loop.count=%0d", command_valid, loop.get_name(), next_loop.get_name(), ptr, next_ptr, loop.count), UVM_NONE)

            if (main_loop_0   != null) main_loop_0.count   = main_loop_0.next_count;
            if (main_loop_1   != null) main_loop_1.count   = main_loop_1.next_count;
            if (main_loop_2   != null) main_loop_2.count   = main_loop_2.next_count;
            if (nested_loop_0 != null) nested_loop_0.count = nested_loop_0.next_count;
            if (nested_loop_1 != null) nested_loop_1.count = nested_loop_1.next_count;

            ptr        = next_ptr;
            loop       = next_loop;
        end

    endfunction : process_cmdb

endclass : ai_core_dp_cmd_gen_model

`endif // GUARD_AI_CORE_DP_CMD_GEN_MODEL_SVH
