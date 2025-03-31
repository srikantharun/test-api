// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style numeric 
// Interesting numeric values
// Owner: abond

// Class : axe_uvm_numeric
class axe_uvm_numeric #(type T=int) extends uvm_component;

    typedef axe_uvm_numeric #(T) this_t;

    bit is_signed;

    T   one_hot[$];
    T   one_cold[$];
    T   all_zero;
    T   all_one;
    T   near_zero[$];
    T   near_min[$];
    T   near_max[$];

    `uvm_component_param_utils_begin(this_t)
        `uvm_field_int(is_signed,        UVM_DEFAULT)
        `uvm_field_queue_int(one_hot,    UVM_DEFAULT)
        `uvm_field_queue_int(one_cold,   UVM_DEFAULT)
        `uvm_field_int(all_zero,         UVM_DEFAULT)
        `uvm_field_int(all_one,          UVM_DEFAULT)
        `uvm_field_queue_int(near_zero,  UVM_DEFAULT | UVM_DEC)
        `uvm_field_queue_int(near_min,   UVM_DEFAULT | UVM_DEC)
        `uvm_field_queue_int(near_max,   UVM_DEFAULT | UVM_DEC)
    `uvm_component_utils_end

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the numeric class
          parent - Parent class

       Returns:

          Instance axe_uvm_numeric
    */
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        T min, max;

        // Calculate if vairable is signed
        is_signed = (T'('1) < 0);

        // One hot/cold
        for (int i = 0; i < $bits(T); i++)
        begin
            one_hot.push_back( T'(1 << i));
            one_cold.push_back(T'(~(1 << i)));
        end

        // All zero / one
        all_zero = T'('0);
        all_one  = T'('1);

        // Near zero
        if (is_signed)
        begin
            min = 1 << ($bits(T)-1);
            max = ~(min);

            for (T i = -2; i<2; i++)
            begin
                near_zero.push_back(i);
            end
        end
        else
        begin
            min = T'('0);
            max = T'('1);

            for (T i = 0; i<2; i++)
            begin
                near_zero.push_back(i);
            end           
        end

        `uvm_info(get_type_name(), $sformatf("min=%0d max=%0d", min, max), UVM_NONE)
        for (T i = min; i <= min+1; i++)
        begin
            near_min.push_back(i);
        end

        for (T i = max-1; i <= max; i++)
        begin
            near_max.push_back(i);
            if (i == max) break;
        end

    endfunction : build_phase

    /* Function: get_random

       Return a random number of this type

       Parameters:
            pc_random: Pecentage genuine random number

       Returns:

          Instance of T
    */
    virtual function T get_random(int pc_random=10);
        T retVal;
        randcase
            pc_random       : assert(std::randomize(retVal));
            (100-pc_random) : begin
                randcase
                    1 : assert(std::randomize(retVal) with { retVal inside {this.all_zero, this.all_one}; });
                    1 : assert(std::randomize(retVal) with { retVal inside {this.one_hot}; });
                    1 : assert(std::randomize(retVal) with { retVal inside {this.one_cold}; });
                    1 : assert(std::randomize(retVal) with { retVal inside {this.near_zero}; });
                    1 : assert(std::randomize(retVal) with { retVal inside {this.near_min}; });
                    1 : assert(std::randomize(retVal) with { retVal inside {this.near_max}; });
                endcase
            end

        endcase
    
        return retVal;
    endfunction: get_random

endclass : axe_uvm_numeric
