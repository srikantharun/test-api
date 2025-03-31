`ifndef RAL_PIE_PKG
`define RAL_PIE_PKG

package ral_PIE_pkg;
import uvm_pkg::*;

class ral_mem_PIE_PIE extends uvm_mem;
   function new(string name = "PIE_PIE");
      super.new(name, `UVM_REG_ADDR_WIDTH'h1000, 32, "RW", build_coverage(UVM_NO_COVERAGE));
 add_coverage(build_coverage(UVM_NO_COVERAGE));
   endfunction
   virtual function void build();
   endfunction: build

   `uvm_object_utils(ral_mem_PIE_PIE)

endclass : ral_mem_PIE_PIE


class ral_block_PIE extends uvm_reg_block;
	rand ral_mem_PIE_PIE PIE;
   local uvm_reg_data_t m_offset;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	PIE : coverpoint m_offset {
		bins first_location_accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		bins last_location_accessed = { `UVM_REG_ADDR_WIDTH'hFFF };
		bins other_locations_accessed = { [`UVM_REG_ADDR_WIDTH'h1:`UVM_REG_ADDR_WIDTH'hFFE] };
		option.weight = 3;
	}
endgroup
	function new(string name = "PIE");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.PIE = ral_mem_PIE_PIE::type_id::create("PIE",,get_full_name());
      this.PIE.configure(this, "");
      this.PIE.build();
      this.default_map.add_mem(this.PIE, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
   endfunction : build

	`uvm_object_utils(ral_block_PIE)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_PIE


endpackage
`endif
