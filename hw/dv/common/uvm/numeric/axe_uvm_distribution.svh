// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style distribution generator 
// Owner: abond

class axe_uvm_base_distribution extends uvm_object;

    int unsigned weight = 0;

    `uvm_object_utils_begin(axe_uvm_base_distribution)
        `uvm_field_int(weight,  UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="axe_uvm_base_distribution");
        super.new(name);
    endfunction : new

    virtual function int unsigned next();
        return 0;
    endfunction 

endclass : axe_uvm_base_distribution

class axe_uvm_distribution_range extends axe_uvm_base_distribution;

    int unsigned minimum = 0;
    int unsigned maximum = 0;

    `uvm_object_utils_begin(axe_uvm_distribution_range)
        `uvm_field_int(minimum, UVM_DEFAULT)
        `uvm_field_int(maximum, UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="axe_uvm_distribution_range");
        super.new(name);
    endfunction : new

    virtual function int unsigned next();
        next = $urandom_range(maximum, minimum);
    endfunction 

endclass : axe_uvm_distribution_range

class axe_uvm_distribution_rate extends axe_uvm_base_distribution;

    int unsigned rate = 0;

    `uvm_object_utils_begin(axe_uvm_distribution_rate)
        `uvm_field_int(rate, UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="axe_uvm_distribution_rate");
        super.new(name);
    endfunction : new

    virtual function int unsigned next();
        int unsigned r;
        next = -1;
      do begin
        next += 1;
        r = $urandom_range(100, 0);
      end while (r > rate);
    endfunction 

endclass : axe_uvm_distribution_rate

class axe_uvm_distribution extends uvm_object;

    axe_uvm_base_distribution distributions[$];
    int unsigned              weights[$];

    `uvm_object_utils(axe_uvm_distribution)

    function new (string name="axe_uvm_distribution");
        super.new(name);
    endfunction : new

    function void add_distribution(axe_uvm_base_distribution distribution);
        for (int i = 0; i < distribution.weight; i++)
            weights.push_back(distributions.size());

        distributions.push_back(distribution);
    endfunction : add_distribution

    function void add_range(int unsigned weight, int unsigned minimum, int unsigned maximum);
        axe_uvm_distribution_range d = new();
        d.weight  = weight;
        d.minimum = minimum;
        d.maximum = maximum;

        add_distribution(d);
    endfunction : add_range

    function void add_rate(int unsigned weight, int unsigned rate);
        axe_uvm_distribution_rate d = new();
        d.weight  = weight;
        d.rate    = rate;
        assert(rate  > 0);
        assert(rate <= 100);
        add_distribution(d);
    endfunction :add_rate

    function int unsigned next();
        int idx;
        assert(std::randomize(idx) with {idx inside { [0:weights.size()-1] } ; });

        next = distributions[weights[idx]].next();
    endfunction : next 
endclass : axe_uvm_distribution
