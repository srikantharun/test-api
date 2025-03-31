`ifndef RAL_DCCM_PKG
`define RAL_DCCM_PKG

package ral_DCCM_pkg;
import uvm_pkg::*;

class ral_mem_DCCM_DCCM extends uvm_mem;
   function new(string name = "DCCM_DCCM");
      super.new(name, `UVM_REG_ADDR_WIDTH'h8000, 32, "RW", build_coverage(UVM_NO_COVERAGE));
 add_coverage(build_coverage(UVM_NO_COVERAGE));
   endfunction
   virtual function void build();
   endfunction: build

   `uvm_object_utils(ral_mem_DCCM_DCCM)

endclass : ral_mem_DCCM_DCCM


class ral_block_DCCM extends uvm_reg_block;
	rand ral_mem_DCCM_DCCM DCCM;
   local uvm_reg_data_t m_offset;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DCCM : coverpoint m_offset {
		bins first_location_accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		bins last_location_accessed = { `UVM_REG_ADDR_WIDTH'hFFFF };
		bins other_locations_accessed = { [`UVM_REG_ADDR_WIDTH'h1:`UVM_REG_ADDR_WIDTH'hFFFE] };
		option.weight = 3;
	}
endgroup
	function new(string name = "DCCM");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DCCM = ral_mem_DCCM_DCCM::type_id::create("DCCM",,get_full_name());
      this.DCCM.configure(this, "");
      this.DCCM.build();
      this.default_map.add_mem(this.DCCM, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
   endfunction : build

	`uvm_object_utils(ral_block_DCCM)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DCCM


endpackage
`endif
