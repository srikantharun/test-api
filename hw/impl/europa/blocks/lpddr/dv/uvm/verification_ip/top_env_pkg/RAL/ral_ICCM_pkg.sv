`ifndef RAL_ICCM_PKG
`define RAL_ICCM_PKG

package ral_ICCM_pkg;
import uvm_pkg::*;

class ral_mem_ICCM_ICCM extends uvm_mem;
   function new(string name = "ICCM_ICCM");
      super.new(name, `UVM_REG_ADDR_WIDTH'h8000, 32, "RW", build_coverage(UVM_NO_COVERAGE));
 add_coverage(build_coverage(UVM_NO_COVERAGE));
   endfunction
   virtual function void build();
   endfunction: build

   `uvm_object_utils(ral_mem_ICCM_ICCM)

endclass : ral_mem_ICCM_ICCM


class ral_block_ICCM extends uvm_reg_block;
	rand ral_mem_ICCM_ICCM ICCM;
   local uvm_reg_data_t m_offset;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ICCM : coverpoint m_offset {
		bins first_location_accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		bins last_location_accessed = { `UVM_REG_ADDR_WIDTH'h7FFF };
		bins other_locations_accessed = { [`UVM_REG_ADDR_WIDTH'h1:`UVM_REG_ADDR_WIDTH'h7FFE] };
		option.weight = 3;
	}
endgroup
	function new(string name = "ICCM");
		super.new(name, build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ICCM = ral_mem_ICCM_ICCM::type_id::create("ICCM",,get_full_name());
      this.ICCM.configure(this, "");
      this.ICCM.build();
      this.default_map.add_mem(this.ICCM, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
   endfunction : build

	`uvm_object_utils(ral_block_ICCM)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_ICCM


endpackage
`endif
