`ifndef RAL_DWC_DDRCTL_MAP_REGB_ADDR_MAP0_PKG
`define RAL_DWC_DDRCTL_MAP_REGB_ADDR_MAP0_PKG

package ral_DWC_ddrctl_map_REGB_ADDR_MAP0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1 extends uvm_reg;
	rand uvm_reg_field addrmap_cs_bit0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_cs_bit0: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_cs_bit0 = uvm_reg_field::type_id::create("addrmap_cs_bit0",,get_full_name());
      this.addrmap_cs_bit0.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3 extends uvm_reg;
	rand uvm_reg_field addrmap_bank_b0;
	rand uvm_reg_field addrmap_bank_b1;
	rand uvm_reg_field addrmap_bank_b2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_bank_b0: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   addrmap_bank_b1: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   addrmap_bank_b2: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_bank_b0 = uvm_reg_field::type_id::create("addrmap_bank_b0",,get_full_name());
      this.addrmap_bank_b0.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
      this.addrmap_bank_b1 = uvm_reg_field::type_id::create("addrmap_bank_b1",,get_full_name());
      this.addrmap_bank_b1.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
      this.addrmap_bank_b2 = uvm_reg_field::type_id::create("addrmap_bank_b2",,get_full_name());
      this.addrmap_bank_b2.configure(this, 6, 16, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4 extends uvm_reg;
	rand uvm_reg_field addrmap_bg_b0;
	rand uvm_reg_field addrmap_bg_b1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_bg_b0: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	   addrmap_bg_b1: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd_as_0 = {7'b?????01};
	      wildcard bins bit_0_rd_as_1 = {7'b?????11};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd_as_0 = {7'b????0?1};
	      wildcard bins bit_1_rd_as_1 = {7'b????1?1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd_as_0 = {7'b???0??1};
	      wildcard bins bit_2_rd_as_1 = {7'b???1??1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd_as_0 = {7'b??0???1};
	      wildcard bins bit_3_rd_as_1 = {7'b??1???1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd_as_0 = {7'b?0????1};
	      wildcard bins bit_4_rd_as_1 = {7'b?1????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd_as_0 = {7'b0?????1};
	      wildcard bins bit_5_rd_as_1 = {7'b1?????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_bg_b0 = uvm_reg_field::type_id::create("addrmap_bg_b0",,get_full_name());
      this.addrmap_bg_b0.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
      this.addrmap_bg_b1 = uvm_reg_field::type_id::create("addrmap_bg_b1",,get_full_name());
      this.addrmap_bg_b1.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5 extends uvm_reg;
	rand uvm_reg_field addrmap_col_b7;
	rand uvm_reg_field addrmap_col_b8;
	rand uvm_reg_field addrmap_col_b9;
	rand uvm_reg_field addrmap_col_b10;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_col_b7: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_col_b8: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_col_b9: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_col_b10: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_col_b7 = uvm_reg_field::type_id::create("addrmap_col_b7",,get_full_name());
      this.addrmap_col_b7.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_col_b8 = uvm_reg_field::type_id::create("addrmap_col_b8",,get_full_name());
      this.addrmap_col_b8.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_col_b9 = uvm_reg_field::type_id::create("addrmap_col_b9",,get_full_name());
      this.addrmap_col_b9.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_col_b10 = uvm_reg_field::type_id::create("addrmap_col_b10",,get_full_name());
      this.addrmap_col_b10.configure(this, 5, 24, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6 extends uvm_reg;
	rand uvm_reg_field addrmap_col_b3;
	rand uvm_reg_field addrmap_col_b4;
	rand uvm_reg_field addrmap_col_b5;
	rand uvm_reg_field addrmap_col_b6;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_col_b3: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   addrmap_col_b4: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   addrmap_col_b5: coverpoint {m_data[19:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	   addrmap_col_b6: coverpoint {m_data[27:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd_as_0 = {5'b???01};
	      wildcard bins bit_0_rd_as_1 = {5'b???11};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd_as_0 = {5'b??0?1};
	      wildcard bins bit_1_rd_as_1 = {5'b??1?1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd_as_0 = {5'b?0??1};
	      wildcard bins bit_2_rd_as_1 = {5'b?1??1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd_as_0 = {5'b0???1};
	      wildcard bins bit_3_rd_as_1 = {5'b1???1};
	      option.weight = 16;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_col_b3 = uvm_reg_field::type_id::create("addrmap_col_b3",,get_full_name());
      this.addrmap_col_b3.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
      this.addrmap_col_b4 = uvm_reg_field::type_id::create("addrmap_col_b4",,get_full_name());
      this.addrmap_col_b4.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 1);
      this.addrmap_col_b5 = uvm_reg_field::type_id::create("addrmap_col_b5",,get_full_name());
      this.addrmap_col_b5.configure(this, 4, 16, "RW", 0, 4'h0, 1, 0, 1);
      this.addrmap_col_b6 = uvm_reg_field::type_id::create("addrmap_col_b6",,get_full_name());
      this.addrmap_col_b6.configure(this, 4, 24, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7 extends uvm_reg;
	rand uvm_reg_field addrmap_row_b14;
	rand uvm_reg_field addrmap_row_b15;
	rand uvm_reg_field addrmap_row_b16;
	rand uvm_reg_field addrmap_row_b17;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_row_b14: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b15: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b16: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b17: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_row_b14 = uvm_reg_field::type_id::create("addrmap_row_b14",,get_full_name());
      this.addrmap_row_b14.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b15 = uvm_reg_field::type_id::create("addrmap_row_b15",,get_full_name());
      this.addrmap_row_b15.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b16 = uvm_reg_field::type_id::create("addrmap_row_b16",,get_full_name());
      this.addrmap_row_b16.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b17 = uvm_reg_field::type_id::create("addrmap_row_b17",,get_full_name());
      this.addrmap_row_b17.configure(this, 5, 24, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8 extends uvm_reg;
	rand uvm_reg_field addrmap_row_b10;
	rand uvm_reg_field addrmap_row_b11;
	rand uvm_reg_field addrmap_row_b12;
	rand uvm_reg_field addrmap_row_b13;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_row_b10: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b11: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b12: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b13: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_row_b10 = uvm_reg_field::type_id::create("addrmap_row_b10",,get_full_name());
      this.addrmap_row_b10.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b11 = uvm_reg_field::type_id::create("addrmap_row_b11",,get_full_name());
      this.addrmap_row_b11.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b12 = uvm_reg_field::type_id::create("addrmap_row_b12",,get_full_name());
      this.addrmap_row_b12.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b13 = uvm_reg_field::type_id::create("addrmap_row_b13",,get_full_name());
      this.addrmap_row_b13.configure(this, 5, 24, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9 extends uvm_reg;
	rand uvm_reg_field addrmap_row_b6;
	rand uvm_reg_field addrmap_row_b7;
	rand uvm_reg_field addrmap_row_b8;
	rand uvm_reg_field addrmap_row_b9;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_row_b6: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b7: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b8: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b9: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_row_b6 = uvm_reg_field::type_id::create("addrmap_row_b6",,get_full_name());
      this.addrmap_row_b6.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b7 = uvm_reg_field::type_id::create("addrmap_row_b7",,get_full_name());
      this.addrmap_row_b7.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b8 = uvm_reg_field::type_id::create("addrmap_row_b8",,get_full_name());
      this.addrmap_row_b8.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b9 = uvm_reg_field::type_id::create("addrmap_row_b9",,get_full_name());
      this.addrmap_row_b9.configure(this, 5, 24, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10 extends uvm_reg;
	rand uvm_reg_field addrmap_row_b2;
	rand uvm_reg_field addrmap_row_b3;
	rand uvm_reg_field addrmap_row_b4;
	rand uvm_reg_field addrmap_row_b5;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_row_b2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b3: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b4: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b5: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_row_b2 = uvm_reg_field::type_id::create("addrmap_row_b2",,get_full_name());
      this.addrmap_row_b2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b3 = uvm_reg_field::type_id::create("addrmap_row_b3",,get_full_name());
      this.addrmap_row_b3.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b4 = uvm_reg_field::type_id::create("addrmap_row_b4",,get_full_name());
      this.addrmap_row_b4.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b5 = uvm_reg_field::type_id::create("addrmap_row_b5",,get_full_name());
      this.addrmap_row_b5.configure(this, 5, 24, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11 extends uvm_reg;
	rand uvm_reg_field addrmap_row_b0;
	rand uvm_reg_field addrmap_row_b1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   addrmap_row_b0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	   addrmap_row_b1: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd_as_0 = {6'b????01};
	      wildcard bins bit_0_rd_as_1 = {6'b????11};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd_as_0 = {6'b???0?1};
	      wildcard bins bit_1_rd_as_1 = {6'b???1?1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd_as_0 = {6'b??0??1};
	      wildcard bins bit_2_rd_as_1 = {6'b??1??1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd_as_0 = {6'b?0???1};
	      wildcard bins bit_3_rd_as_1 = {6'b?1???1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd_as_0 = {6'b0????1};
	      wildcard bins bit_4_rd_as_1 = {6'b1????1};
	      option.weight = 20;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.addrmap_row_b0 = uvm_reg_field::type_id::create("addrmap_row_b0",,get_full_name());
      this.addrmap_row_b0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.addrmap_row_b1 = uvm_reg_field::type_id::create("addrmap_row_b1",,get_full_name());
      this.addrmap_row_b1.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11


class ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12 extends uvm_reg;
	rand uvm_reg_field nonbinary_device_density;
	rand uvm_reg_field bank_hash_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   nonbinary_device_density: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {4'b??00};
	      wildcard bins bit_0_wr_as_1 = {4'b??10};
	      wildcard bins bit_0_rd_as_0 = {4'b??01};
	      wildcard bins bit_0_rd_as_1 = {4'b??11};
	      wildcard bins bit_1_wr_as_0 = {4'b?0?0};
	      wildcard bins bit_1_wr_as_1 = {4'b?1?0};
	      wildcard bins bit_1_rd_as_0 = {4'b?0?1};
	      wildcard bins bit_1_rd_as_1 = {4'b?1?1};
	      wildcard bins bit_2_wr_as_0 = {4'b0??0};
	      wildcard bins bit_2_wr_as_1 = {4'b1??0};
	      wildcard bins bit_2_rd_as_0 = {4'b0??1};
	      wildcard bins bit_2_rd_as_1 = {4'b1??1};
	      option.weight = 12;
	   }
	   bank_hash_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.nonbinary_device_density = uvm_reg_field::type_id::create("nonbinary_device_density",,get_full_name());
      this.nonbinary_device_density.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 0);
      this.bank_hash_en = uvm_reg_field::type_id::create("bank_hash_en",,get_full_name());
      this.bank_hash_en.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12


class ral_block_DWC_ddrctl_map_REGB_ADDR_MAP0 extends uvm_reg_block;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1 ADDRMAP1;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3 ADDRMAP3;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4 ADDRMAP4;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5 ADDRMAP5;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6 ADDRMAP6;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7 ADDRMAP7;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8 ADDRMAP8;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9 ADDRMAP9;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10 ADDRMAP10;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11 ADDRMAP11;
	rand ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12 ADDRMAP12;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field ADDRMAP1_addrmap_cs_bit0;
	rand uvm_reg_field addrmap_cs_bit0;
	rand uvm_reg_field ADDRMAP3_addrmap_bank_b0;
	rand uvm_reg_field addrmap_bank_b0;
	rand uvm_reg_field ADDRMAP3_addrmap_bank_b1;
	rand uvm_reg_field addrmap_bank_b1;
	rand uvm_reg_field ADDRMAP3_addrmap_bank_b2;
	rand uvm_reg_field addrmap_bank_b2;
	rand uvm_reg_field ADDRMAP4_addrmap_bg_b0;
	rand uvm_reg_field addrmap_bg_b0;
	rand uvm_reg_field ADDRMAP4_addrmap_bg_b1;
	rand uvm_reg_field addrmap_bg_b1;
	rand uvm_reg_field ADDRMAP5_addrmap_col_b7;
	rand uvm_reg_field addrmap_col_b7;
	rand uvm_reg_field ADDRMAP5_addrmap_col_b8;
	rand uvm_reg_field addrmap_col_b8;
	rand uvm_reg_field ADDRMAP5_addrmap_col_b9;
	rand uvm_reg_field addrmap_col_b9;
	rand uvm_reg_field ADDRMAP5_addrmap_col_b10;
	rand uvm_reg_field addrmap_col_b10;
	rand uvm_reg_field ADDRMAP6_addrmap_col_b3;
	rand uvm_reg_field addrmap_col_b3;
	rand uvm_reg_field ADDRMAP6_addrmap_col_b4;
	rand uvm_reg_field addrmap_col_b4;
	rand uvm_reg_field ADDRMAP6_addrmap_col_b5;
	rand uvm_reg_field addrmap_col_b5;
	rand uvm_reg_field ADDRMAP6_addrmap_col_b6;
	rand uvm_reg_field addrmap_col_b6;
	rand uvm_reg_field ADDRMAP7_addrmap_row_b14;
	rand uvm_reg_field addrmap_row_b14;
	rand uvm_reg_field ADDRMAP7_addrmap_row_b15;
	rand uvm_reg_field addrmap_row_b15;
	rand uvm_reg_field ADDRMAP7_addrmap_row_b16;
	rand uvm_reg_field addrmap_row_b16;
	rand uvm_reg_field ADDRMAP7_addrmap_row_b17;
	rand uvm_reg_field addrmap_row_b17;
	rand uvm_reg_field ADDRMAP8_addrmap_row_b10;
	rand uvm_reg_field addrmap_row_b10;
	rand uvm_reg_field ADDRMAP8_addrmap_row_b11;
	rand uvm_reg_field addrmap_row_b11;
	rand uvm_reg_field ADDRMAP8_addrmap_row_b12;
	rand uvm_reg_field addrmap_row_b12;
	rand uvm_reg_field ADDRMAP8_addrmap_row_b13;
	rand uvm_reg_field addrmap_row_b13;
	rand uvm_reg_field ADDRMAP9_addrmap_row_b6;
	rand uvm_reg_field addrmap_row_b6;
	rand uvm_reg_field ADDRMAP9_addrmap_row_b7;
	rand uvm_reg_field addrmap_row_b7;
	rand uvm_reg_field ADDRMAP9_addrmap_row_b8;
	rand uvm_reg_field addrmap_row_b8;
	rand uvm_reg_field ADDRMAP9_addrmap_row_b9;
	rand uvm_reg_field addrmap_row_b9;
	rand uvm_reg_field ADDRMAP10_addrmap_row_b2;
	rand uvm_reg_field addrmap_row_b2;
	rand uvm_reg_field ADDRMAP10_addrmap_row_b3;
	rand uvm_reg_field addrmap_row_b3;
	rand uvm_reg_field ADDRMAP10_addrmap_row_b4;
	rand uvm_reg_field addrmap_row_b4;
	rand uvm_reg_field ADDRMAP10_addrmap_row_b5;
	rand uvm_reg_field addrmap_row_b5;
	rand uvm_reg_field ADDRMAP11_addrmap_row_b0;
	rand uvm_reg_field addrmap_row_b0;
	rand uvm_reg_field ADDRMAP11_addrmap_row_b1;
	rand uvm_reg_field addrmap_row_b1;
	rand uvm_reg_field ADDRMAP12_nonbinary_device_density;
	rand uvm_reg_field nonbinary_device_density;
	rand uvm_reg_field ADDRMAP12_bank_hash_en;
	rand uvm_reg_field bank_hash_en;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ADDRMAP1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	ADDRMAP3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC };
		option.weight = 1;
	}

	ADDRMAP4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	ADDRMAP5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h14 };
		option.weight = 1;
	}

	ADDRMAP6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h18 };
		option.weight = 1;
	}

	ADDRMAP7 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1C };
		option.weight = 1;
	}

	ADDRMAP8 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h20 };
		option.weight = 1;
	}

	ADDRMAP9 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h24 };
		option.weight = 1;
	}

	ADDRMAP10 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h28 };
		option.weight = 1;
	}

	ADDRMAP11 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2C };
		option.weight = 1;
	}

	ADDRMAP12 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_ddrctl_map_REGB_ADDR_MAP0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ADDRMAP1 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1::type_id::create("ADDRMAP1",,get_full_name());
      if(this.ADDRMAP1.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP1.cg_bits.option.name = {get_name(), ".", "ADDRMAP1_bits"};
      this.ADDRMAP1.configure(this, null, "");
      this.ADDRMAP1.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_cs_bit0", 0, 6}
         });
      this.default_map.add_reg(this.ADDRMAP1, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.ADDRMAP1_addrmap_cs_bit0 = this.ADDRMAP1.addrmap_cs_bit0;
		this.addrmap_cs_bit0 = this.ADDRMAP1.addrmap_cs_bit0;
      this.ADDRMAP3 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP3::type_id::create("ADDRMAP3",,get_full_name());
      if(this.ADDRMAP3.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP3.cg_bits.option.name = {get_name(), ".", "ADDRMAP3_bits"};
      this.ADDRMAP3.configure(this, null, "");
      this.ADDRMAP3.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP3.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_bank_b0", 0, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_bank_b1", 8, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_bank_b2", 16, 6}
         });
      this.default_map.add_reg(this.ADDRMAP3, `UVM_REG_ADDR_WIDTH'hC, "RW", 0);
		this.ADDRMAP3_addrmap_bank_b0 = this.ADDRMAP3.addrmap_bank_b0;
		this.addrmap_bank_b0 = this.ADDRMAP3.addrmap_bank_b0;
		this.ADDRMAP3_addrmap_bank_b1 = this.ADDRMAP3.addrmap_bank_b1;
		this.addrmap_bank_b1 = this.ADDRMAP3.addrmap_bank_b1;
		this.ADDRMAP3_addrmap_bank_b2 = this.ADDRMAP3.addrmap_bank_b2;
		this.addrmap_bank_b2 = this.ADDRMAP3.addrmap_bank_b2;
      this.ADDRMAP4 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP4::type_id::create("ADDRMAP4",,get_full_name());
      if(this.ADDRMAP4.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP4.cg_bits.option.name = {get_name(), ".", "ADDRMAP4_bits"};
      this.ADDRMAP4.configure(this, null, "");
      this.ADDRMAP4.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP4.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_bg_b0", 0, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_bg_b1", 8, 6}
         });
      this.default_map.add_reg(this.ADDRMAP4, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.ADDRMAP4_addrmap_bg_b0 = this.ADDRMAP4.addrmap_bg_b0;
		this.addrmap_bg_b0 = this.ADDRMAP4.addrmap_bg_b0;
		this.ADDRMAP4_addrmap_bg_b1 = this.ADDRMAP4.addrmap_bg_b1;
		this.addrmap_bg_b1 = this.ADDRMAP4.addrmap_bg_b1;
      this.ADDRMAP5 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP5::type_id::create("ADDRMAP5",,get_full_name());
      if(this.ADDRMAP5.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP5.cg_bits.option.name = {get_name(), ".", "ADDRMAP5_bits"};
      this.ADDRMAP5.configure(this, null, "");
      this.ADDRMAP5.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP5.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP5.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b7", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b8", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b9", 16, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b10", 24, 5}
         });
      this.default_map.add_reg(this.ADDRMAP5, `UVM_REG_ADDR_WIDTH'h14, "RW", 0);
		this.ADDRMAP5_addrmap_col_b7 = this.ADDRMAP5.addrmap_col_b7;
		this.addrmap_col_b7 = this.ADDRMAP5.addrmap_col_b7;
		this.ADDRMAP5_addrmap_col_b8 = this.ADDRMAP5.addrmap_col_b8;
		this.addrmap_col_b8 = this.ADDRMAP5.addrmap_col_b8;
		this.ADDRMAP5_addrmap_col_b9 = this.ADDRMAP5.addrmap_col_b9;
		this.addrmap_col_b9 = this.ADDRMAP5.addrmap_col_b9;
		this.ADDRMAP5_addrmap_col_b10 = this.ADDRMAP5.addrmap_col_b10;
		this.addrmap_col_b10 = this.ADDRMAP5.addrmap_col_b10;
      this.ADDRMAP6 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP6::type_id::create("ADDRMAP6",,get_full_name());
      if(this.ADDRMAP6.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP6.cg_bits.option.name = {get_name(), ".", "ADDRMAP6_bits"};
      this.ADDRMAP6.configure(this, null, "");
      this.ADDRMAP6.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP6.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP6.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b3", 0, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b4", 8, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b5", 16, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_col_b6", 24, 4}
         });
      this.default_map.add_reg(this.ADDRMAP6, `UVM_REG_ADDR_WIDTH'h18, "RW", 0);
		this.ADDRMAP6_addrmap_col_b3 = this.ADDRMAP6.addrmap_col_b3;
		this.addrmap_col_b3 = this.ADDRMAP6.addrmap_col_b3;
		this.ADDRMAP6_addrmap_col_b4 = this.ADDRMAP6.addrmap_col_b4;
		this.addrmap_col_b4 = this.ADDRMAP6.addrmap_col_b4;
		this.ADDRMAP6_addrmap_col_b5 = this.ADDRMAP6.addrmap_col_b5;
		this.addrmap_col_b5 = this.ADDRMAP6.addrmap_col_b5;
		this.ADDRMAP6_addrmap_col_b6 = this.ADDRMAP6.addrmap_col_b6;
		this.addrmap_col_b6 = this.ADDRMAP6.addrmap_col_b6;
      this.ADDRMAP7 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP7::type_id::create("ADDRMAP7",,get_full_name());
      if(this.ADDRMAP7.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP7.cg_bits.option.name = {get_name(), ".", "ADDRMAP7_bits"};
      this.ADDRMAP7.configure(this, null, "");
      this.ADDRMAP7.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP7.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP7.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b14", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b15", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b16", 16, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b17", 24, 5}
         });
      this.default_map.add_reg(this.ADDRMAP7, `UVM_REG_ADDR_WIDTH'h1C, "RW", 0);
		this.ADDRMAP7_addrmap_row_b14 = this.ADDRMAP7.addrmap_row_b14;
		this.addrmap_row_b14 = this.ADDRMAP7.addrmap_row_b14;
		this.ADDRMAP7_addrmap_row_b15 = this.ADDRMAP7.addrmap_row_b15;
		this.addrmap_row_b15 = this.ADDRMAP7.addrmap_row_b15;
		this.ADDRMAP7_addrmap_row_b16 = this.ADDRMAP7.addrmap_row_b16;
		this.addrmap_row_b16 = this.ADDRMAP7.addrmap_row_b16;
		this.ADDRMAP7_addrmap_row_b17 = this.ADDRMAP7.addrmap_row_b17;
		this.addrmap_row_b17 = this.ADDRMAP7.addrmap_row_b17;
      this.ADDRMAP8 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP8::type_id::create("ADDRMAP8",,get_full_name());
      if(this.ADDRMAP8.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP8.cg_bits.option.name = {get_name(), ".", "ADDRMAP8_bits"};
      this.ADDRMAP8.configure(this, null, "");
      this.ADDRMAP8.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP8.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP8.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b10", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b11", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b12", 16, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b13", 24, 5}
         });
      this.default_map.add_reg(this.ADDRMAP8, `UVM_REG_ADDR_WIDTH'h20, "RW", 0);
		this.ADDRMAP8_addrmap_row_b10 = this.ADDRMAP8.addrmap_row_b10;
		this.addrmap_row_b10 = this.ADDRMAP8.addrmap_row_b10;
		this.ADDRMAP8_addrmap_row_b11 = this.ADDRMAP8.addrmap_row_b11;
		this.addrmap_row_b11 = this.ADDRMAP8.addrmap_row_b11;
		this.ADDRMAP8_addrmap_row_b12 = this.ADDRMAP8.addrmap_row_b12;
		this.addrmap_row_b12 = this.ADDRMAP8.addrmap_row_b12;
		this.ADDRMAP8_addrmap_row_b13 = this.ADDRMAP8.addrmap_row_b13;
		this.addrmap_row_b13 = this.ADDRMAP8.addrmap_row_b13;
      this.ADDRMAP9 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP9::type_id::create("ADDRMAP9",,get_full_name());
      if(this.ADDRMAP9.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP9.cg_bits.option.name = {get_name(), ".", "ADDRMAP9_bits"};
      this.ADDRMAP9.configure(this, null, "");
      this.ADDRMAP9.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP9.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP9.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b6", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b7", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b8", 16, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b9", 24, 5}
         });
      this.default_map.add_reg(this.ADDRMAP9, `UVM_REG_ADDR_WIDTH'h24, "RW", 0);
		this.ADDRMAP9_addrmap_row_b6 = this.ADDRMAP9.addrmap_row_b6;
		this.addrmap_row_b6 = this.ADDRMAP9.addrmap_row_b6;
		this.ADDRMAP9_addrmap_row_b7 = this.ADDRMAP9.addrmap_row_b7;
		this.addrmap_row_b7 = this.ADDRMAP9.addrmap_row_b7;
		this.ADDRMAP9_addrmap_row_b8 = this.ADDRMAP9.addrmap_row_b8;
		this.addrmap_row_b8 = this.ADDRMAP9.addrmap_row_b8;
		this.ADDRMAP9_addrmap_row_b9 = this.ADDRMAP9.addrmap_row_b9;
		this.addrmap_row_b9 = this.ADDRMAP9.addrmap_row_b9;
      this.ADDRMAP10 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP10::type_id::create("ADDRMAP10",,get_full_name());
      if(this.ADDRMAP10.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP10.cg_bits.option.name = {get_name(), ".", "ADDRMAP10_bits"};
      this.ADDRMAP10.configure(this, null, "");
      this.ADDRMAP10.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP10.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP10.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b2", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b3", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b4", 16, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b5", 24, 5}
         });
      this.default_map.add_reg(this.ADDRMAP10, `UVM_REG_ADDR_WIDTH'h28, "RW", 0);
		this.ADDRMAP10_addrmap_row_b2 = this.ADDRMAP10.addrmap_row_b2;
		this.addrmap_row_b2 = this.ADDRMAP10.addrmap_row_b2;
		this.ADDRMAP10_addrmap_row_b3 = this.ADDRMAP10.addrmap_row_b3;
		this.addrmap_row_b3 = this.ADDRMAP10.addrmap_row_b3;
		this.ADDRMAP10_addrmap_row_b4 = this.ADDRMAP10.addrmap_row_b4;
		this.addrmap_row_b4 = this.ADDRMAP10.addrmap_row_b4;
		this.ADDRMAP10_addrmap_row_b5 = this.ADDRMAP10.addrmap_row_b5;
		this.addrmap_row_b5 = this.ADDRMAP10.addrmap_row_b5;
      this.ADDRMAP11 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP11::type_id::create("ADDRMAP11",,get_full_name());
      if(this.ADDRMAP11.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP11.cg_bits.option.name = {get_name(), ".", "ADDRMAP11_bits"};
      this.ADDRMAP11.configure(this, null, "");
      this.ADDRMAP11.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP11.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP11.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b0", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_addr_map0_addrmap_row_b1", 8, 5}
         });
      this.default_map.add_reg(this.ADDRMAP11, `UVM_REG_ADDR_WIDTH'h2C, "RW", 0);
		this.ADDRMAP11_addrmap_row_b0 = this.ADDRMAP11.addrmap_row_b0;
		this.addrmap_row_b0 = this.ADDRMAP11.addrmap_row_b0;
		this.ADDRMAP11_addrmap_row_b1 = this.ADDRMAP11.addrmap_row_b1;
		this.addrmap_row_b1 = this.ADDRMAP11.addrmap_row_b1;
      this.ADDRMAP12 = ral_reg_DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP12::type_id::create("ADDRMAP12",,get_full_name());
      if(this.ADDRMAP12.has_coverage(UVM_CVR_REG_BITS))
      	this.ADDRMAP12.cg_bits.option.name = {get_name(), ".", "ADDRMAP12_bits"};
      this.ADDRMAP12.configure(this, null, "");
      this.ADDRMAP12.build();
	  uvm_resource_db#(string)::set({"REG::", ADDRMAP12.get_full_name()}, "accessType", "NONSECURE", this);
         this.ADDRMAP12.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_addr_map0_nonbinary_device_density", 0, 3},
            '{"U_apb_slvtop.slvif.ff_regb_addr_map0_bank_hash_en", 4, 1}
         });
      this.default_map.add_reg(this.ADDRMAP12, `UVM_REG_ADDR_WIDTH'h30, "RW", 0);
		this.ADDRMAP12_nonbinary_device_density = this.ADDRMAP12.nonbinary_device_density;
		this.nonbinary_device_density = this.ADDRMAP12.nonbinary_device_density;
		this.ADDRMAP12_bank_hash_en = this.ADDRMAP12.bank_hash_en;
		this.bank_hash_en = this.ADDRMAP12.bank_hash_en;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_ddrctl_map_REGB_ADDR_MAP0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_ddrctl_map_REGB_ADDR_MAP0


endpackage
`endif
