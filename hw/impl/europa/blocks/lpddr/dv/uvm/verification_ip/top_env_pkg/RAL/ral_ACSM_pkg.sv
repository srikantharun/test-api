`ifndef RAL_ACSM_PKG
`define RAL_ACSM_PKG

package ral_ACSM_pkg;
import uvm_pkg::*;

class ral_mem_ACSM_ACSM extends uvm_mem;
   function new(string name = "ACSM_ACSM");
      super.new(name, `UVM_REG_ADDR_WIDTH'h1000, 32, "RW", build_coverage(UVM_NO_COVERAGE));
 add_coverage(build_coverage(UVM_NO_COVERAGE));
   endfunction
   virtual function void build();
   endfunction: build

   `uvm_object_utils(ral_mem_ACSM_ACSM)

endclass : ral_mem_ACSM_ACSM


class ral_block_ACSM extends uvm_reg_block;
	rand ral_mem_ACSM_ACSM ACSM;
   local uvm_reg_data_t m_offset;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ACSM : coverpoint m_offset {
		bins first_location_accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		bins last_location_accessed = { `UVM_REG_ADDR_WIDTH'hFFF };
		bins other_locations_accessed = { [`UVM_REG_ADDR_WIDTH'h1:`UVM_REG_ADDR_WIDTH'hFFE] };
		option.weight = 3;
	}
endgroup
	function new(string name = "ACSM");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ACSM = ral_mem_ACSM_ACSM::type_id::create("ACSM",,get_full_name());
      this.ACSM.configure(this, "");
      this.ACSM.build();
      this.default_map.add_mem(this.ACSM, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
   endfunction : build

	`uvm_object_utils(ral_block_ACSM)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_ACSM


endpackage
`endif
