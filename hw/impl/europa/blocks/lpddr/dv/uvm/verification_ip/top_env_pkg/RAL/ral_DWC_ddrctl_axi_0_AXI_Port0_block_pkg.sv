`ifndef RAL_DWC_DDRCTL_AXI_0_AXI_PORT0_BLOCK_PKG
`define RAL_DWC_DDRCTL_AXI_0_AXI_PORT0_BLOCK_PKG

package ral_DWC_ddrctl_axi_0_AXI_Port0_block_pkg;
import uvm_pkg::*;

class ral_mem_DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block extends uvm_mem;
   function new(string name = "DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block");
      super.new(name, `UVM_REG_ADDR_WIDTH'h1000, 32, "RW", build_coverage(UVM_CVR_ADDR_MAP));
 add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
   endfunction
   virtual function void build();
   endfunction: build

   `uvm_object_utils(ral_mem_DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block)

endclass : ral_mem_DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block


class ral_block_DWC_ddrctl_axi_0_AXI_Port0_block extends uvm_reg_block;
	rand ral_mem_DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block DWC_ddrctl_axi_0_AXI_Port0_block;
   local uvm_reg_data_t m_offset;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DWC_ddrctl_axi_0_AXI_Port0_block : coverpoint m_offset {
		bins first_location_accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		bins last_location_accessed = { `UVM_REG_ADDR_WIDTH'hFFF };
		bins other_locations_accessed = { [`UVM_REG_ADDR_WIDTH'h1:`UVM_REG_ADDR_WIDTH'hFFE] };
		option.weight = 3;
	}
endgroup
	function new(string name = "DWC_ddrctl_axi_0_AXI_Port0_block");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DWC_ddrctl_axi_0_AXI_Port0_block = ral_mem_DWC_ddrctl_axi_0_AXI_Port0_block_DWC_ddrctl_axi_0_AXI_Port0_block::type_id::create("DWC_ddrctl_axi_0_AXI_Port0_block",,get_full_name());
      this.DWC_ddrctl_axi_0_AXI_Port0_block.configure(this, "");
      this.DWC_ddrctl_axi_0_AXI_Port0_block.build();
      this.default_map.add_mem(this.DWC_ddrctl_axi_0_AXI_Port0_block, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
   endfunction : build

	`uvm_object_utils(ral_block_DWC_ddrctl_axi_0_AXI_Port0_block)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_ddrctl_axi_0_AXI_Port0_block


endpackage
`endif
