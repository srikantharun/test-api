// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_SVH

class ai_core_dp_cmd_gen_cmdb extends uvm_sequence_item;

    rand bit                                    valid;
    rand aic_dp_cmd_gen_pkg::cmd_format_t       format;
    rand aic_dp_cmd_gen_pkg::loop_index_t       nested_1_map_main;
    rand aic_dp_cmd_gen_pkg::loop_description_t nested_1;
    rand aic_dp_cmd_gen_pkg::loop_index_t       nested_0_map_main;
    rand aic_dp_cmd_gen_pkg::loop_description_t nested_0;
    rand aic_dp_cmd_gen_pkg::command_reserved_t reserved_1;
    rand aic_dp_cmd_gen_pkg::loop_description_t main_2;
    rand aic_dp_cmd_gen_pkg::command_reserved_t reserved_0;
    rand aic_dp_cmd_gen_pkg::loop_description_t main_1;
    rand aic_dp_cmd_gen_pkg::command_extra_t    extra;
    rand aic_dp_cmd_gen_pkg::loop_description_t main_0;
    rand aic_dp_cmd_gen_pkg::loop_errors_t      errors;

    rand bit                                    parallel;
    int unsigned                                base, top;
    real                                        timestamp;
    int unsigned                                valid_cycle, ready_cycle, done_cycle;

    rand int                                    flush_delay;

    constraint c_no_flush {
        flush_delay == -1;
    }

    constraint c_defaults {
        soft valid == 1'b0;
    }

    constraint c_order {
        solve errors before valid;
        solve valid  before format;
        solve format before nested_0_map_main;
        solve format before nested_1_map_main;
    }

    constraint c_invalid {
        !`_main_0_valid_   -> format             == '0;
        !`_main_0_valid_   -> main_0             == '0;
        !`_main_1_valid_   -> main_1             == '0;
        !`_main_2_valid_   -> main_2             == '0;
        !`_nested_0_valid_ -> nested_0           == '0;
        !`_nested_1_valid_ -> nested_1           == '0;
        !`_nested_0_valid_ -> nested_0_map_main  == '0;
        !`_nested_1_valid_ -> nested_1_map_main  == '0;
        !`_main_0_valid_   -> extra              == '0;
    }

    constraint c_reserved_0 {
        reserved_0 == aic_dp_cmd_gen_pkg::command_reserved_t'('0);
    }

    constraint c_reserved_1 {
        reserved_1 == aic_dp_cmd_gen_pkg::command_reserved_t'('0);
    }

    constraint c_valid_format {
        valid -> format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N0);
        valid -> format <= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::Bypass);
    }

    constraint c_nested_map {
        nested_0_map_main >= 0;
        nested_0_map_main <= 2;
        nested_1_map_main >= 0;
        nested_1_map_main <= 2;
    }

    constraint c_nested_map_0 {
        !`_main_1_valid_ -> nested_0_map_main < 1;
        !`_main_1_valid_ -> nested_1_map_main < 1;
    }

    constraint c_nested_map_1 {
        !`_main_2_valid_ -> nested_0_map_main < 2;
        !`_main_2_valid_ -> nested_1_map_main < 2;
    }

    constraint c_main_0 {
        `_main_0_valid_ -> `_start_(main_0)     >=     base;
        `_main_0_valid_ -> `_start_(main_0)     <=     top;
        `_main_0_valid_ -> `_length_(main_0)     >     0;
        `_main_0_valid_ -> `_end_(main_0)       <=     top;
    }

    constraint c_main_1 {
        `_main_1_valid_ -> `_start_(main_1)      >     base;
        `_main_1_valid_ -> `_start_(main_1)     <=     top;
        `_main_1_valid_ -> `_length_(main_1)     >     0;
        `_main_1_valid_ -> `_end_(main_1)       <=     top;
    }

    constraint c_main_2 {
        `_main_2_valid_ -> `_start_(main_2)      >     base;
        `_main_2_valid_ -> `_start_(main_2)     <=     top;
        `_main_2_valid_ -> `_length_(main_2)     >     0;
        `_main_2_valid_ -> `_end_(main_2)       <=     top;
    }

    constraint c_nested_m0n1 {
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_start_(nested_0)  >= `_start_(main_0);
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_start_(nested_0)  <= `_end_(main_0);
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_length_(nested_0)  > 0;
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_end_(nested_0)    <= `_end_(main_0);
    }

    constraint c_nested_m0n2 {
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_start_(nested_1)  >= `_start_(main_0);
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_start_(nested_1)  <= `_end_(main_0);
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_length_(nested_1)  > 0;
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_end_(nested_1)    <= `_end_(main_0);
    }

    constraint c_nested_m1n1 {
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_start_(nested_0)  >= `_start_(main_1);
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_start_(nested_0)  <= `_end_(main_1);
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_length_(nested_0)  > 0;
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_end_(nested_0)    <= `_end_(main_1);
    }

    constraint c_nested_m1n2 {
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_start_(nested_1)  >= `_start_(main_1);
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_start_(nested_1)  <= `_end_(main_1);
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_length_(nested_1)  > 0;
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_end_(nested_1)    <= `_end_(main_1);
    }

    constraint c_nested_m2n1 {
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_start_(nested_0)  >= `_start_(main_2);
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_start_(nested_0)  <= `_end_(main_2);
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_length_(nested_0)  > 0;
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_end_(nested_0)    <= `_end_(main_2);
    }

    constraint c_nested_m2n2 {
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_start_(nested_1)  >= `_start_(main_2);
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_start_(nested_1)  <= `_end_(main_2);
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_length_(nested_1)  > 0;
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_end_(nested_1)    <= `_end_(main_2);
    }

    constraint c_nested_1   {
        // No nesting and overlapping
        errors.nested_nesting                        -> !errors.nested_overlap;
        errors.nested_overlap                        -> !errors.nested_nesting;

        // Nested order
        `_nested_1_valid_ &&  errors.nested_order    -> `_start_(nested_1)    < `_start_(nested_0);
        `_nested_1_valid_ && !errors.nested_order    -> `_start_(nested_1)   >=  `_start_(nested_0);

        // Nested Nesting
        `_nested_1_valid_ &&  errors.nested_nesting  -> (
                                                            (
                                                                (`_start_(nested_1)  == `_start_(nested_0))
                                                                &&
                                                                (`_end_(nested_1)     > `_end_(nested_0))
                                                            )
                                                            ||
                                                            (
                                                                (`_start_(nested_1)   < `_start_(nested_0))
                                                                &&
                                                                (`_end_(nested_1)    >= `_end_(nested_0))
                                                            )
                                                        );
        // Nested Overlapping
        `_nested_1_valid_ &&  errors.nested_overlap  -> (
                                                            (
                                                                (`_start_(nested_1) < `_start_(nested_0))
                                                                &&
                                                                (`_end_(nested_1)  >= `_start_(nested_0))
                                                                &&
                                                                (`_end_(nested_1)  <= `_end_(nested_0))
                                                            )
                                                            ||
                                                            (
                                                                (`_start_(nested_1)  > `_start_(nested_0))
                                                                &&
                                                                (`_start_(nested_1) <= `_end_(nested_0))
                                                                &&
                                                                (`_end_(nested_1)    >  `_end_(nested_0))
                                                            )
                                               );

        `_nested_1_valid_ && !errors.nested_overlap && !errors.nested_nesting ->    (
                                                                                        (`_start_(nested_1)  > `_end_(nested_0))
                                                                                        ||
                                                                                        (
                                                                                            (`_start_(nested_1)  >= `_start_(nested_0))
                                                                                            &&
                                                                                            (`_start_(nested_1)  <= `_end_(nested_0))
                                                                                            &&
                                                                                            (`_end_(nested_1)    <=  `_end_(nested_0))
                                                                                        )
                                                                                    );


    }

   // Attempt to keep sim runtime sane
    constraint c_iterations {
        `_main_0_valid_   -> `_iteration_(main_0)   > 0;
        `_main_1_valid_   -> `_iteration_(main_1)   > 0;
        `_main_2_valid_   -> `_iteration_(main_2)   > 0;
        `_nested_0_valid_ -> `_iteration_(nested_0) > 0;
        `_nested_1_valid_ -> `_iteration_(nested_1) > 0;
    }

    // Attempt to keep sim runtime sane
    constraint c_runtime {
        `_main_0_valid_   -> soft `_length_(main_0)      dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_main_0_valid_   -> soft `_iteration_(main_0)   dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_main_1_valid_   -> soft `_length_(main_1)      dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_main_1_valid_   -> soft `_iteration_(main_1)   dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_main_2_valid_   -> soft `_length_(main_2)      dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_main_2_valid_   -> soft `_iteration_(main_2)   dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_nested_0_valid_ -> soft `_length_(nested_0)    dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_nested_0_valid_ -> soft `_iteration_(nested_0) dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_nested_1_valid_ -> soft `_length_(nested_1)    dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
        `_nested_1_valid_ -> soft `_iteration_(nested_1) dist   {[1:7]   := 1,
                                                                 [8:63]  :/ 4};
    }

    // Errors
    constraint c_no_errors {
        soft errors.illegal_format     == 1'b0;
        soft errors.empty_program      == 1'b0;
        soft errors.main_0_length      == 1'b0;
        soft errors.main_1_length      == 1'b0;
        soft errors.main_2_length      == 1'b0;
        soft errors.nested_0_length    == 1'b0;
        soft errors.nested_1_length    == 1'b0;
        soft errors.nested_0_mapping   == 1'b0;
        soft errors.nested_1_mapping   == 1'b0;
        soft errors.nested_0_segfault  == 1'b0;
        soft errors.nested_1_segfault  == 1'b0;
        soft errors.nested_order       == 1'b0;
        soft errors.nested_nesting     == 1'b0;
        soft errors.nested_overlap     == 1'b0;
    }

    constraint c_errors_valid {
        |errors -> valid;
    }

    constraint c_errors_bypass {
        |errors -> format != aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::Bypass);
    }

    constraint c_empty_program {
        errors.empty_program -> errors.main_0_length      == 1'b0;
        errors.empty_program -> errors.main_1_length      == 1'b0;
        errors.empty_program -> errors.main_2_length      == 1'b0;
        errors.empty_program -> errors.nested_0_length    == 1'b0;
        errors.empty_program -> errors.nested_1_length    == 1'b0;
        errors.empty_program -> errors.nested_0_mapping   == `_nested_0_valid_;
        errors.empty_program -> errors.nested_1_mapping   == `_nested_1_valid_;
        errors.empty_program -> errors.nested_0_segfault  == 1'b0;
        errors.empty_program -> errors.nested_1_segfault  == 1'b0;
        errors.empty_program -> errors.nested_order       == 1'b0;
        errors.empty_program -> errors.nested_nesting     == 1'b0;
        errors.empty_program -> errors.nested_overlap     == 1'b0;
    }

    constraint c_error_empty_program {
        errors.empty_program -> !errors.main_0_length;
        errors.empty_program -> !errors.main_1_length;
        errors.empty_program -> !errors.main_2_length;
    }

    constraint c_error_illegal_main_0_length{
        errors.main_0_length -> `_main_0_valid_;
        errors.main_0_length -> !errors.empty_program;
    }

    constraint c_error_illegal_main_1_length{
        errors.main_1_length -> `_main_1_valid_;
        errors.main_1_length -> !errors.empty_program;
    }

    constraint c_error_illegal_main_2_length{
        errors.main_2_length -> `_main_2_valid_;
        errors.main_2_length -> !errors.empty_program;
    }

    constraint c_error_illegal_nested_0_length{
        errors.nested_0_length -> `_nested_0_valid_;
        errors.nested_0_length -> errors.nested_0_segfault;
    }

    constraint c_error_illegal_nested_1_length{
        errors.nested_1_length -> `_nested_1_valid_;
        errors.nested_1_length -> errors.nested_1_segfault;
    }

    constraint c_error_illegal_nested_0_mapping{
        errors.nested_0_mapping -> `_nested_0_valid_;
    }

    constraint c_error_illegal_nested_1_mapping{
        errors.nested_1_mapping -> `_nested_1_valid_;
    }

    constraint c_error_illegal_nested_0_segfault{
        errors.nested_0_segfault -> `_nested_0_valid_;
    }

    constraint c_error_illegal_nested_1_segfault{
        errors.nested_1_segfault -> `_nested_1_valid_;
    }

    constraint c_error_illegal_nested_order{
        errors.nested_order -> `_co_nested_;
    }

    constraint c_error_illegal_nested_nesting{
        errors.nested_nesting -> `_co_nested_;
    }

    constraint c_error_illegal_nested_overlap{
        errors.nested_overlap -> `_co_nested_;
    }

    constraint c_error_mapping_to_nesting {
        (errors.nested_0_mapping || errors.nested_1_mapping) -> !errors.nested_order;
        (errors.nested_0_mapping || errors.nested_1_mapping) -> !errors.nested_nesting;
        (errors.nested_0_mapping || errors.nested_1_mapping) -> !errors.nested_overlap;
    }

    constraint c_error_mapping_to_segfault {
        errors.nested_0_mapping -> !errors.nested_0_segfault;
        errors.nested_1_mapping -> !errors.nested_1_segfault;
    }

    `uvm_object_utils_begin(ai_core_dp_cmd_gen_cmdb)
        `uvm_field_int(  valid,             UVM_DEFAULT)
        `uvm_field_int(  format,            UVM_DEFAULT)
        `uvm_field_int(  nested_1_map_main, UVM_DEFAULT )
        `uvm_field_int(  nested_1,          UVM_DEFAULT | UVM_NOPRINT)
        `uvm_field_int(  nested_0_map_main, UVM_DEFAULT)
        `uvm_field_int(  nested_0,          UVM_DEFAULT | UVM_NOPRINT)
        `uvm_field_int(  reserved_1,        UVM_DEFAULT)
        `uvm_field_int(  main_2,            UVM_DEFAULT | UVM_NOPRINT)
        `uvm_field_int(  reserved_0,        UVM_DEFAULT)
        `uvm_field_int(  main_1,            UVM_DEFAULT | UVM_NOPRINT)
        `uvm_field_int(  extra,             UVM_DEFAULT)
        `uvm_field_int(  main_0,            UVM_DEFAULT | UVM_NOPRINT)
        `uvm_field_int(  errors,            UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
        `uvm_field_int(  base,              UVM_DEFAULT | UVM_HEX | UVM_NOCOMPARE)
        `uvm_field_int(  top,               UVM_DEFAULT | UVM_HEX | UVM_NOCOMPARE)
        `uvm_field_real( timestamp,         UVM_DEFAULT | UVM_NOCOMPARE) // Debug only
        `uvm_field_int(  valid_cycle,       UVM_DEFAULT | UVM_NOCOMPARE) // Debug / Coverage only
        `uvm_field_int(  ready_cycle,       UVM_DEFAULT | UVM_NOCOMPARE) // Debug / Coverage only
        `uvm_field_int(  done_cycle,        UVM_DEFAULT | UVM_NOCOMPARE) // Debug / Coverage only
        `uvm_field_int(  flush_delay,       UVM_DEFAULT | UVM_NOCOMPARE | UVM_NOPRINT)
    `uvm_object_utils_end

    function new(string name = "");
        super.new(name);
    endfunction : new

    function string description_str(aic_dp_cmd_gen_pkg::loop_description_t desc);
        if ((desc.length == '0) || (desc.iteration == '0))
            return $psprintf("0x%04x-null   (%0d commands) %0d iterations", desc.start,                           desc.length, desc.iteration);
        else
            return $psprintf("0x%04x-0x%04x (%0d commands) %0d iterations", desc.start, desc.start+desc.length-1, desc.length, desc.iteration);
    endfunction : description_str

    virtual function void do_print(uvm_printer printer);
        aic_dp_cmd_gen_pkg::cmd_format_e format_enum = aic_dp_cmd_gen_pkg::cmd_format_e'(format);
        super.do_print(printer);
        printer.print_string("main_0",   this.description_str(main_0));
        printer.print_string("main_1",   this.description_str(main_1));
        printer.print_string("main_2",   this.description_str(main_2));
        printer.print_string("nested_0", this.description_str(nested_0));
        printer.print_string("nested_1", this.description_str(nested_1));
        printer.print_string("format(enum)", format_enum.name());
        if (errors != 0 ) begin
            printer.print_string("errors.illegal_format",    $psprintf("%0d", errors.illegal_format));
            printer.print_string("errors.empty_program",     $psprintf("%0d", errors.empty_program));
            printer.print_string("errors.main_0_length",     $psprintf("%0d", errors.main_0_length));
            printer.print_string("errors.main_1_length",     $psprintf("%0d", errors.main_1_length));
            printer.print_string("errors.main_2_length",     $psprintf("%0d", errors.main_2_length));
            printer.print_string("errors.nested_0_length",   $psprintf("%0d", errors.nested_0_length));
            printer.print_string("errors.nested_1_length",   $psprintf("%0d", errors.nested_1_length));
            printer.print_string("errors.nested_0_mapping",  $psprintf("%0d", errors.nested_0_mapping));
            printer.print_string("errors.nested_1_mapping",  $psprintf("%0d", errors.nested_1_mapping));
            printer.print_string("errors.nested_0_segfault", $psprintf("%0d", errors.nested_0_segfault));
            printer.print_string("errors.nested_1_segfault", $psprintf("%0d", errors.nested_1_segfault));
            printer.print_string("errors.nested_order",      $psprintf("%0d", errors.nested_order));
            printer.print_string("errors.nested_nesting",    $psprintf("%0d", errors.nested_nesting));
            printer.print_string("errors.nested_overlap",    $psprintf("%0d", errors.nested_overlap));
        end

        if (flush_delay >= 0) begin
           printer.print_field_int("flush_delay", flush_delay, 32);
        end
    endfunction : do_print

    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        bit retVal;
        ai_core_dp_cmd_gen_cmdb _rhs;
        assert($cast(_rhs, rhs));

        retVal  = super.do_compare(_rhs, comparer);

        // Illegal format make the error checks very strange
        // The key thing is to be safe and flaggig any error is good for this
        if (this.errors.illegal_format == 1'b0)
            retVal &= _rhs.errors == this.errors;
        else
            retVal &= |_rhs.errors == |this.errors;

        return retVal;
    endfunction : do_compare

    function aic_dp_cmd_gen_pkg::cmd_format_e get_format();
        return aic_dp_cmd_gen_pkg::cmd_format_e'(format);
    endfunction : get_format

    function bit main_valid(int idx);
        bit retVal = valid;

        case(idx)
            0       : begin end
            1       : retVal &= (format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N0));
            2       : retVal &= (format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N0));
            default : retVal = 0;
        endcase
        return retVal;
    endfunction : main_valid

    function bit main_empty(int idx);
        bit retVal = !main_valid(idx);

        retVal |= get_length(1,    idx) == 0;
        retVal |= get_iteration(1, idx) == 0;

        return retVal;
    endfunction : main_empty

    function bit nested_valid(int idx);
        bit retVal = valid;

        case(idx)
            0       : retVal &= (format inside {aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N1),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N2),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N1),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N2),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N1),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2)});
            1       : retVal &= (format inside {aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N2),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N2),
                                                aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2)});
            default : assert(0);
        endcase
        return retVal;
    endfunction : nested_valid

    function bit nested_empty(int idx);
        bit retVal = !nested_valid(idx);

        retVal |= get_length(0,    idx) == 0;
        retVal |= get_iteration(0, idx) == 0;

        return retVal;
    endfunction : nested_empty

    function bit co_nested();
        bit retVal = valid;

        retVal &= nested_valid(1);
        retVal &= (nested_0_map_main == nested_1_map_main);

        return retVal;
    endfunction : co_nested

    function bit is_parallel();
        bit retVal = valid;

        retVal &= co_nested();
        retVal &= get_start(1'b0,1) > get_end(1'b0, 0);

        return retVal;
    endfunction : is_parallel

    function aic_dp_cmd_gen_pkg::loop_length_t get_length(bit main_not_nested, int idx);
        if (main_not_nested) begin
            case(idx)
                0       : return main_0.length;
                1       : return main_1.length;
                2       : return main_2.length;
                default : return 0;
            endcase
        end
        else begin
            case(idx)
                0       : return nested_0.length;
                1       : return nested_1.length;
                default : return 0;
            endcase
        end
    endfunction : get_length

    function int get_map_main(int idx);
        case(idx)
            0       : return nested_0_map_main;
            1       : return nested_1_map_main;
            default : assert(0);
        endcase
    endfunction : get_map_main

    function aic_dp_cmd_gen_pkg::loop_pointer_t get_start(bit main_not_nested, int idx);
        if (main_not_nested) begin
            case(idx)
                0       : return main_0.start;
                1       : return main_1.start;
                2       : return main_2.start;
                default : assert(0);
            endcase
        end
        else begin
            case(idx)
                0       : return nested_0.start;
                1       : return nested_1.start;
                default : assert(0);
            endcase
        end
    endfunction : get_start

    function int unsigned get_end(bit main_not_nested, int idx); // Not using typedef as it can overflow and needed for errors
        if (main_not_nested) begin
            case(idx)
                0       : return main_0.start + get_length(main_not_nested, idx) - 1;
                1       : return main_1.start + get_length(main_not_nested, idx) - 1;
                2       : return main_2.start + get_length(main_not_nested, idx) - 1;
                default : assert(0);
            endcase
        end
        else begin
            case(idx)
                0       : return nested_0.start + get_length(main_not_nested, idx) - 1;
                1       : return nested_1.start + get_length(main_not_nested, idx) - 1;
                default : assert(0);
            endcase
        end
    endfunction : get_end

    function aic_dp_cmd_gen_pkg::loop_iteration_t get_iteration(bit main_not_nested, int idx);
        if (main_not_nested) begin
            case(idx)
                0       : return main_0.iteration;
                1       : return main_1.iteration;
                2       : return main_2.iteration;
                default : return 0;
            endcase
        end
        else begin
            case(idx)
                0       : return nested_0.iteration;
                1       : return nested_1.iteration;
                default : return 0;
            endcase
        end
    endfunction : get_iteration

    function void post_randomize();
        if (|errors == 1'b0) return;

        // Error conditions added in post randomize
        if (errors.illegal_format) begin
            assert(std::randomize(format) with { format > aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::Bypass); });
            return;
        end

        if (errors.empty_program) begin
            randcase
                1 : main_0.length    = '0;
                1 : main_0.iteration = '0;
                1 : begin
                       main_0.length    = '0;
                       main_0.iteration = '0;
                    end
                1 : main_0 = '0;
            endcase
            randcase
                1 : main_1.length    = '0;
                1 : main_1.iteration = '0;
                1 : begin
                       main_1.length    = '0;
                       main_1.iteration = '0;
                    end
                1 : main_1 = '0;
            endcase
            randcase
                1 : main_2.length    = '0;
                1 : main_2.iteration = '0;
                1 : begin
                       main_2.length    = '0;
                       main_2.iteration = '0;
                    end
                1 : main_2 = '0;
            endcase
        end

        if (errors.main_0_length) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            assert(std::randomize(_loop_) with { `_start_(_loop_) == `_start_(main_0);
                                                 `_end_(_loop_)    > top; });
            main_0.length = _loop_.length;
        end

        if (errors.main_1_length) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            assert(std::randomize(_loop_) with { `_start_(_loop_) == `_start_(main_1);
                                                 `_end_(_loop_)    > top; });
            main_1.length = _loop_.length;
        end

        if (errors.main_2_length) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            assert(std::randomize(_loop_) with { `_start_(_loop_) == `_start_(main_2);
                                                 `_end_(_loop_)    > top; });
            main_2.length = _loop_.length;
        end

        if (errors.nested_0_length) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            assert(std::randomize(_loop_) with { `_start_(_loop_) == `_start_(nested_0);
                                                 `_end_(_loop_)    > top; });
            nested_0.length = _loop_.length;
        end

        if (errors.nested_1_length) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            assert(std::randomize(_loop_) with { `_start_(_loop_) == `_start_(nested_0);
                                                 `_end_(_loop_)    > top; });
            nested_1.length = _loop_.length;
        end

        if (errors.nested_0_mapping) begin
            aic_dp_cmd_gen_pkg::loop_index_t  _map_;
            assert(std::randomize(_map_) with { `_main_0_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(1);
                                                `_main_1_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(2);
                                                `_main_2_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(3);
                                              });
            nested_0_map_main = _map_;
        end else begin
            if (`_nested_0_valid_) begin
                errors.nested_0_mapping |= (get_length(1'b1,    get_map_main(0)) == 0);
                errors.nested_0_mapping |= (get_iteration(1'b1, get_map_main(0)) == 0);
            end
        end

        if (errors.nested_1_mapping) begin
            aic_dp_cmd_gen_pkg::loop_index_t  _map_;
            assert(std::randomize(_map_) with { `_main_0_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(1);
                                                `_main_1_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(2);
                                                `_main_2_valid_ -> _map_ >= aic_dp_cmd_gen_pkg::loop_index_t'(3);
                                              });
            nested_1_map_main = _map_;
        end else begin
            if (`_nested_1_valid_) begin
                errors.nested_1_mapping |= (get_length(1'b1,    get_map_main(1)) == 0);
                errors.nested_1_mapping |= (get_iteration(1'b1, get_map_main(1)) == 0);
            end
        end

        if (!errors.nested_0_length && errors.nested_0_segfault) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            randcase
                (get_start(1'b1, nested_0_map_main) > base) : begin
                    assert(std::randomize(_loop_) with  {
                                                            `_end_(_loop_)   ==  `_end_(nested_0);
                                                            `_start_(_loop_) >= base;
                                                            `_start_(_loop_)  < get_start(1'b1, nested_0_map_main);
                                                            `_iteration_(_loop_) == `_iteration_(nested_0);
                                                        });
                end
                1 : begin
                    assert(std::randomize(_loop_) with {
                                                            `_start_(_loop_) == `_start_(nested_0);
                                                            `_end_(_loop_)    > get_end(1'b1,   nested_0_map_main);
                                                            `_iteration_(_loop_) == `_iteration_(nested_0);
                                                        });
                end
            endcase
            nested_0 = _loop_;
        end

        if (!errors.nested_1_length && errors.nested_1_segfault) begin
            aic_dp_cmd_gen_pkg::loop_description_t _loop_;
            randcase
                (get_start(1'b1, nested_1_map_main) > base) : begin
                    assert(std::randomize(_loop_) with  {
                                                            `_end_(_loop_)   ==  `_end_(nested_1);
                                                            `_start_(_loop_) >= base;
                                                            `_start_(_loop_)  < get_start(1'b1, nested_1_map_main);
                                                            `_iteration_(_loop_) == `_iteration_(nested_1);
                                                        });
                end
                1 : begin
                    assert(std::randomize(_loop_) with {
                                                            `_start_(_loop_) == `_start_(nested_1);
                                                            `_end_(_loop_)    > get_end(1'b1,   nested_1_map_main);
                                                            `_iteration_(_loop_) == `_iteration_(nested_1);
                                                        });
                end
            endcase
            nested_1 = _loop_;
        end


        // Update errors
        errors = '0;
        errors.illegal_format = format > aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::Bypass);

        errors.empty_program = main_empty(0) && main_empty(1) && main_empty(2);

        errors.main_0_length   = (`_length_(main_0)   == 0) ? 1'b0 : `_end_(main_0)   > top;
        errors.main_1_length   = (`_length_(main_1)   == 0) ? 1'b0 : `_end_(main_1)   > top;
        errors.main_2_length   = (`_length_(main_2)   == 0) ? 1'b0 : `_end_(main_2)   > top;
        errors.nested_0_length = (`_length_(nested_0) == 0) ? 1'b0 : `_end_(nested_0) > top;
        errors.nested_1_length = (`_length_(nested_1) == 0) ? 1'b0 : `_end_(nested_1) > top;

        errors.nested_0_mapping = (get_map_main(0) > 2);
        if (!errors.nested_0_mapping) begin
            errors.nested_0_mapping  = main_empty(get_map_main(0));
            errors.nested_0_segfault |= (
                                            (get_start(1'b0, 0)  < get_start(1'b1, get_map_main(0)))
                                            &&
                                            (get_end(1'b0, 0)   >= get_start(1'b1, get_map_main(0)))
                                            &&
                                            (get_end(1'b0, 0)   <= get_end(1'b1, get_map_main(0)))
                                        );
            errors.nested_0_segfault |= (
                                            (get_start(1'b0, 0) >= get_start(1'b1, get_map_main(0)))
                                            &&
                                            (get_start(1'b0, 0) <= get_end(1'b1, get_map_main(0)))
                                            &&
                                            (get_end(1'b0, 0)    > get_end(1'b1, get_map_main(0)))
                                        );
            errors.nested_0_segfault &= !nested_empty(0);
        end

        errors.nested_1_mapping = (get_map_main(1) > 2);
        if (!errors.nested_1_mapping) begin
            errors.nested_1_mapping  = main_empty(get_map_main(1));
            errors.nested_1_segfault |= (
                                            (get_start(1'b0, 1)  < get_start(1'b1, get_map_main(1)))
                                            &&
                                            (get_end(1'b0, 1)   >= get_start(1'b1, get_map_main(1)))
                                            &&
                                            (get_end(1'b0, 1)   <= get_end(1'b1, get_map_main(1)))
                                        );
            errors.nested_1_segfault |= (
                                            (get_start(1'b0, 1) >= get_start(1'b1, get_map_main(1)))
                                            &&
                                            (get_start(1'b0, 1) <= get_end(1'b1, get_map_main(1)))
                                            &&
                                            (get_end(1'b0, 1)    > get_end(1'b1, get_map_main(1)))
                                        );
            errors.nested_1_segfault &= !nested_empty(1);
        end

        if (`_co_nested_) begin
            if (`_start_(nested_1) < `_start_(nested_0)) begin
                errors.nested_order = 1'b1;
                if (`_end_(nested_1) < `_end_(nested_0)) begin
                    errors.nested_overlap = (`_end_(nested_1) >= `_start_(nested_0));
                end else begin
                    errors.nested_nesting = 1'b1;
                end
            end else if (`_start_(nested_1) == `_start_(nested_0)) begin
               errors.nested_nesting = `_end_(nested_1) > `_end_(nested_0);
            end else begin
                if (`_start_(nested_1) <= `_end_(nested_0)) begin
                    if (`_end_(nested_1) > `_end_(nested_0)) begin
                        errors.nested_overlap = 1'b1;
                    end
                end
            end
        end
    endfunction : post_randomize
endclass : ai_core_dp_cmd_gen_cmdb

class ai_core_dp_cmd_gen_cmdb_legal extends ai_core_dp_cmd_gen_cmdb;
    constraint c_valid  { valid  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_legal)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_legal");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_legal

class ai_core_dp_cmd_gen_cmdb_short extends ai_core_dp_cmd_gen_cmdb_legal;

    constraint c_runtime {
                            `_length_(main_0)      <= 3;
                            `_iteration_(main_0)   <= 3;
                            `_length_(main_1)      <= 3;
                            `_iteration_(main_1)   <= 3;
                            `_length_(main_2)      <= 3;
                            `_iteration_(main_2)   <= 3;
                            `_length_(nested_0)    <= 3;
                            `_iteration_(nested_0) <= 3;
                            `_length_(nested_1)    <= 3;
                            `_iteration_(nested_1) <= 3;
                         }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_short)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_short");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_short

class ai_core_dp_cmd_gen_cmdb_bypass extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::Bypass); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_bypass)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_bypass");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_bypass

class ai_core_dp_cmd_gen_cmdb_m1n0 extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N0); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m1n0)

    function new(string name = "");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_m1n0

class ai_core_dp_cmd_gen_cmdb_m1n1 extends ai_core_dp_cmd_gen_cmdb_m1n0;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N1); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m1n1)

    function new(string name = "");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_m1n1

class ai_core_dp_cmd_gen_cmdb_m1n2 extends ai_core_dp_cmd_gen_cmdb_m1n1;
    constraint c_format   { format   == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM1N2); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m1n2)

    function new(string name = "");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_m1n2

class ai_core_dp_cmd_gen_cmdb_m2n0 extends ai_core_dp_cmd_gen_cmdb;
    constraint c_valid  { valid  == 1'b1; }
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N0); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m2n0)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m2n0

class ai_core_dp_cmd_gen_cmdb_m2n1 extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N1); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m2n1)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m2n1

class ai_core_dp_cmd_gen_cmdb_m2n2 extends ai_core_dp_cmd_gen_cmdb_m2n1;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N2); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m2n2)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m2n2

class ai_core_dp_cmd_gen_cmdb_m3n0 extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N0); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m3n0)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m3n0

class ai_core_dp_cmd_gen_cmdb_m3n1 extends ai_core_dp_cmd_gen_cmdb_m3n0;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N1); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m3n1)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m3n1

class ai_core_dp_cmd_gen_cmdb_m3n2 extends ai_core_dp_cmd_gen_cmdb_m3n1;
    constraint c_format { format == aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2); }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_m3n2)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_m3n2

class ai_core_dp_cmd_gen_cmdb_overlapping_main extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_format { format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM2N0);
                          format >= aic_dp_cmd_gen_pkg::cmd_format_t'(aic_dp_cmd_gen_pkg::LoopsM3N2); }

    constraint c_overlapping_mains {
        `_main_1_valid_ -> `_start_(main_1)     >=     `_start_(main_0);
        `_main_1_valid_ -> `_start_(main_1)     <=     `_end_(main_0);
        `_main_2_valid_ -> `_start_(main_2)     >=     `_start_(main_0);
        `_main_2_valid_ -> `_start_(main_2)     <=     `_end_(main_0);
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_overlapping_main)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_overlapping_main

class ai_core_dp_cmd_gen_cmdb_separate_nested extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_nested_valid {
                                `_nested_0_valid_ == 1'b1;
                                `_nested_1_valid_ == 1'b1;
    }
    constraint c_nested_separate {
                                    nested_0_map_main != nested_1_map_main;
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_separate_nested)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_separate_nested

class ai_core_dp_cmd_gen_cmdb_nested_main_same_start extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_nested_valid {
                                `_nested_0_valid_ | `_nested_1_valid_== 1'b1;
    }

    constraint c_same_start {
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_start_(nested_0)  == `_start_(main_0);
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_start_(nested_0)  == `_start_(main_1);
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_start_(nested_0)  == `_start_(main_2);
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_start_(nested_1)  == `_start_(main_0);
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_start_(nested_1)  == `_start_(main_1);
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_start_(nested_1)  == `_start_(main_2);
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_nested_main_same_start)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_nested_main_same_start

class ai_core_dp_cmd_gen_cmdb_nested_main_same_end extends ai_core_dp_cmd_gen_cmdb_legal;
    constraint c_nested_valid {
                                `_nested_0_valid_ | `_nested_1_valid_== 1'b1;
    }

    constraint c_same_end {
        `_nested_0_valid_ && (nested_0_map_main == 0) -> `_end_(nested_0)  == `_end_(main_0);
        `_nested_0_valid_ && (nested_0_map_main == 1) -> `_end_(nested_0)  == `_end_(main_1);
        `_nested_0_valid_ && (nested_0_map_main == 2) -> `_end_(nested_0)  == `_end_(main_2);
        `_nested_1_valid_ && (nested_1_map_main == 0) -> `_end_(nested_1)  == `_end_(main_0);
        `_nested_1_valid_ && (nested_1_map_main == 1) -> `_end_(nested_1)  == `_end_(main_1);
        `_nested_1_valid_ && (nested_1_map_main == 2) -> `_end_(nested_1)  == `_end_(main_2);
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_nested_main_same_end)

    function new(string name = "");
        super.new(name);
    endfunction : new
endclass : ai_core_dp_cmd_gen_cmdb_nested_main_same_end

class ai_core_dp_cmd_gen_cmdb_illegal extends ai_core_dp_cmd_gen_cmdb;
    constraint c_valid  { valid  == 1'b1; }
    constraint c_error  { errors != '0;}
    constraint c_error_illegal_format  { errors.illegal_format == 1'b0; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal");
        super.new(name);
        this.c_no_errors.constraint_mode(0);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal

class ai_core_dp_cmd_gen_cmdb_illegal_format extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error_illegal_format  { errors.illegal_format == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_format)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_format");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_format

class ai_core_dp_cmd_gen_cmdb_empty_program extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error  { errors.empty_program  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_empty_program)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_empty_program");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_empty_program

class ai_core_dp_cmd_gen_cmdb_illegal_main_0_length extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error        { errors.main_0_length  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_main_0_length)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_main_0_length");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_main_0_length

class ai_core_dp_cmd_gen_cmdb_illegal_main_1_length extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error        { errors.main_1_length  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_main_1_length)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_main_1_length");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_main_1_length

class ai_core_dp_cmd_gen_cmdb_illegal_main_2_length extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error        { errors.main_2_length  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_main_2_length)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_main_2_length");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_main_2_length

class ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          { errors.nested_0_length  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_0_length

class ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          { errors.nested_1_length  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_1_length

class ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          { errors.nested_0_mapping  == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_0_mapping

class ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          { errors.nested_1_mapping == 1'b1; }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_1_mapping

class ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          {
        errors.nested_0_segfault == 1'b1;
        errors.main_0_length == 1'b0;
        errors.main_1_length == 1'b0;
        errors.main_2_length == 1'b0;
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_0_segfault

class ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          {
        errors.nested_1_segfault == 1'b1;
        errors.main_0_length == 1'b0;
        errors.main_1_length == 1'b0;
        errors.main_2_length == 1'b0;
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_1_segfault

class ai_core_dp_cmd_gen_cmdb_illegal_nested_order extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          {   errors.nested_order       == 1'b1;
                                    errors.main_0_length      == 1'b0;
                                    errors.main_1_length      == 1'b0;
                                    errors.main_2_length      == 1'b0;
                                    errors.nested_0_length    == 1'b0;
                                    errors.nested_1_length    == 1'b0;
                                    errors.nested_0_segfault  == 1'b0;
                                    errors.nested_1_segfault  == 1'b0;
                                }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_order)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_order");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_order

class ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_errors {
      errors.nested_nesting     == 1'b1;
      errors.empty_program      == 1'b0;
      errors.nested_0_length    == 1'b0;
      errors.nested_1_length    == 1'b0;
      errors.nested_0_mapping   == 1'b0;
      errors.nested_1_mapping   == 1'b0;
      errors.nested_0_segfault  == 1'b0;
      errors.nested_1_segfault  == 1'b0;
      errors.nested_order       == 1'b0;
      errors.nested_overlap     == 1'b0;
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_nesting

class ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap extends ai_core_dp_cmd_gen_cmdb_illegal;
    constraint c_error          {
      errors.nested_overlap     == 1'b1;
      errors.empty_program      == 1'b0;
      errors.nested_0_length    == 1'b0;
      errors.nested_1_length    == 1'b0;
      errors.nested_0_mapping   == 1'b0;
      errors.nested_1_mapping   == 1'b0;
      errors.nested_0_segfault  == 1'b0;
      errors.nested_1_segfault  == 1'b0;
      errors.nested_order       == 1'b0;
      errors.nested_nesting     == 1'b0;
    }

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap)

    function new(string name = "ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap");
        super.new(name);
    endfunction : new

endclass : ai_core_dp_cmd_gen_cmdb_illegal_nested_overlap


`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_SVH
